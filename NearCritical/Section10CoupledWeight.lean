module

public import NearCritical.Section10CoupledPairMass
public import NearCritical.Section10WeightSecondMoment

/-! Source `prop.nw.main`, first conclusion `P[W >= 1/2] >= 1/8`, on the ACTUAL
coupled law, for the weight `W` built from actual chains.

`routeWeightSum` is the source `W = sum_Gamma mu(Gamma) omega_Gamma zeta_Gamma`
as a function of the configuration pair: the cube weight `w γ` is a function of
the reveal, and `zeta` is the chain weight `chainValue`.

`coupled_good_weight_probability` assembles
* `E[W] = 1` from `revealed_chain_mean` (`lem.nw.mean`),
* `E[W^2] <= sum mu mu' E[w w' rho^#shared]` from `revealed_pair_mass_le`
  (`eq.nw.pair.mass`),
* the EIT moment bound `exponential_count_moment_le_two`,
* Paley--Zygmund on the actual law (`coupled_paley_zygmund`).

Remaining hypotheses are concrete statements about the actual objects:
the step rule (locality, mean one, shared-step bound), freshness of the joint
schedules, `E[w_Gamma(G)] = 1`, the cube-pair bound
`E[w w' rho^#shared] <= Lambda^N` and the EIT tail of `mu x mu`.
-/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open MeasureTheory
open scoped Classical BigOperators

/-- Local on some finite bond set. -/
def IsLoc {d : ℕ} (G : Configuration d × Configuration d → ℝ) : Prop :=
  ∃ R : Finset (LBond d), IsLocal R G

lemma IsLoc.mul {d : ℕ} {G K : Configuration d × Configuration d → ℝ}
    (hG : IsLoc G) (hK : IsLoc K) : IsLoc (fun z => G z * K z) := by
  obtain ⟨R, hR⟩ := hG
  obtain ⟨T, hT⟩ := hK
  exact ⟨R ∪ T, hR.mul_union hT⟩

lemma isLoc_const {d : ℕ} (c : ℝ) : IsLoc (fun _ : Configuration d × Configuration d => c) :=
  ⟨∅, isLocal_const ∅ c⟩

lemma isLoc_sum {d : ℕ} {Y : Type*} [Fintype Y]
    {F : Y → Configuration d × Configuration d → ℝ} (hF : ∀ y, IsLoc (F y)) :
    IsLoc (fun z => ∑ y, F y z) := by
  choose R hR using hF
  exact ⟨Finset.univ.biUnion R, isLocal_sum (fun y =>
    (hR y).mono (Finset.subset_biUnion_of_mem R (Finset.mem_univ y)))⟩

lemma IsLoc.comp {d : ℕ} {G : Configuration d × Configuration d → ℝ} (hG : IsLoc G)
    (φ : ℝ → ℝ) : IsLoc (fun z => φ (G z)) := by
  obtain ⟨R, g, hg⟩ := hG
  exact ⟨R, fun b => φ (g b), fun z => congrArg φ (hg z)⟩

lemma IsLoc.integrable {d : ℕ} (p q : unitInterval)
    {G : Configuration d × Configuration d → ℝ} (hG : IsLoc G) :
    Integrable G ((percolation d p).prod (percolation d q)) := by
  obtain ⟨R, hR⟩ := hG
  exact hR.integrable p q

/-- A function that is local on each atom of a reveal with local atoms is local. -/
lemma isLoc_of_reveal {d : ℕ} {Φ : Type*} [Fintype Φ]
    (ρ : Configuration d × Configuration d → Φ) (S : Φ → Finset (LBond d))
    (hρ : ∀ F, IsLocal (S F) (fun z => if ρ z = F then (1:ℝ) else 0))
    (V : Φ → Configuration d × Configuration d → ℝ) (hV : ∀ F, IsLoc (V F)) :
    IsLoc (fun z => V (ρ z) z) := by
  have h : (fun z => V (ρ z) z) = fun z => ∑ F, (if ρ z = F then (1:ℝ) else 0) * V F z := by
    funext z
    rw [Finset.sum_eq_single (ρ z)]
    · rw [if_pos rfl, one_mul]
    · intro F _ hF
      rw [if_neg (Ne.symm hF), zero_mul]
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [h]
  exact isLoc_sum (fun F => IsLoc.mul ⟨S F, hρ F⟩ (hV F))

/-- Paley--Zygmund on the actual coupled law, in the form used by
`prop.nw.main`: mean one and second moment at most two give
`P[W >= 1/2] >= 1/8`. -/
theorem coupled_paley_zygmund {d : ℕ} (p q : unitInterval)
    {W : Configuration d × Configuration d → ℝ} (hW : IsLoc W)
    (hmean : (∫ z, W z ∂((percolation d p).prod (percolation d q))) = 1)
    (hsecond : (∫ z, W z ^ 2 ∂((percolation d p).prod (percolation d q))) ≤ 2) :
    (1/8 : ℝ) ≤ ∫ z, (if (1/2:ℝ) ≤ W z then (1:ℝ) else 0)
      ∂((percolation d p).prod (percolation d q)) := by
  have hI : IsLoc (fun z => (if (1/2:ℝ) ≤ W z then (1:ℝ) else 0)) :=
    hW.comp (fun v => if (1/2:ℝ) ≤ v then (1:ℝ) else 0)
  have hW2 : IsLoc (fun z => W z ^ 2) := hW.comp (fun v => v ^ 2)
  have hpt : ∀ z, W z ≤ 1/2 + ((1/8) * W z ^ 2 +
      (3/2) * (if (1/2:ℝ) ≤ W z then (1:ℝ) else 0)) := by
    intro z
    by_cases h : (1/2:ℝ) ≤ W z
    · rw [if_pos h]
      nlinarith [sq_nonneg (W z - 4)]
    · rw [if_neg h]
      nlinarith [sq_nonneg (W z)]
  have hi1 : Integrable (fun z => (1/8) * W z ^ 2)
      ((percolation d p).prod (percolation d q)) := (hW2.integrable p q).const_mul _
  have hi2 : Integrable (fun z => (3/2) * (if (1/2:ℝ) ≤ W z then (1:ℝ) else 0))
      ((percolation d p).prod (percolation d q)) := (hI.integrable p q).const_mul _
  have hi0 : Integrable (fun _ : Configuration d × Configuration d => (1/2:ℝ))
      ((percolation d p).prod (percolation d q)) := integrable_const _
  have hmono := integral_mono (hW.integrable p q) (hi0.add (hi1.add hi2)) hpt
  have e1 := integral_add hi0 (hi1.add hi2)
  have e2 := integral_add hi1 hi2
  simp only [Pi.add_apply] at hmono e1
  rw [e1, e2, integral_const_mul, integral_const_mul, integral_const, probReal_univ, one_smul,
    hmean] at hmono
  linarith

/-- The source weight `W = sum_Gamma mu(Gamma) omega_Gamma zeta_Gamma`. -/
def routeWeightSum {d : ℕ} {X Φ Γ : Type*} [Fintype X] [Fintype Γ]
    (μ : Γ → ℝ) (ρ : Configuration d × Configuration d → Φ) (w : Γ → Φ → ℝ)
    (k : Γ → Φ → ℕ → X → X → Configuration d × Configuration d → ℝ)
    (n : Γ → Φ → ℕ) (x₀ : Γ → Φ → X) (z : Configuration d × Configuration d) : ℝ :=
  ∑ γ, μ γ * (w γ (ρ z) * chainValue (k γ (ρ z)) (n γ (ρ z)) 0 (x₀ γ (ρ z)) z)

/-- **`prop.nw.main`, first conclusion, on the actual coupled law.** -/
theorem coupled_good_weight_probability {d : ℕ} {X Φ Γ : Type*}
    [Fintype X] [Fintype Φ] [Fintype Γ] (p q : unitInterval)
    (ρ : Configuration d × Configuration d → Φ) (S : Φ → Finset (LBond d))
    (hρ : ∀ F, IsLocal (S F) (fun z => if ρ z = F then (1:ℝ) else 0))
    (μ : Γ → ℝ) (hμ0 : ∀ γ, 0 ≤ μ γ) (hμ1 : ∑ γ, μ γ = 1)
    (B : Γ → Φ → ℕ → Finset (LBond d))
    (hB : ∀ γ F i j, i ≠ j → Disjoint (B γ F i) (B γ F j))
    (hSB : ∀ γ F j, Disjoint (S F) (B γ F j))
    (k : Γ → Φ → ℕ → X → X → Configuration d × Configuration d → ℝ)
    (hk : ∀ γ F t x y, IsLocal (B γ F t) (k γ F t x y))
    (hk0 : ∀ γ F t x y z, 0 ≤ k γ F t x y z)
    (hnorm : ∀ γ F t x,
      (∫ z, ∑ y, k γ F t x y z ∂((percolation d p).prod (percolation d q))) = 1)
    (sch : Γ → Γ → Φ → List PairMove) (n : Γ → Φ → ℕ)
    (hleft : ∀ γ γ' F, leftCount (sch γ γ' F) = n γ F)
    (hright : ∀ γ γ' F, rightCount (sch γ γ' F) = n γ' F)
    (hfresh : ∀ γ γ' F, PairFresh (B γ F) (B γ' F) (sch γ γ' F) 0 0 (S F))
    {ϱ : ℝ} (hϱ : 0 ≤ ϱ)
    (hBoth : ∀ γ γ' F t t' x x', (∫ z, ∑ yy : X × X, k γ F t x yy.1 z * k γ' F t' x' yy.2 z
      ∂((percolation d p).prod (percolation d q))) ≤ ϱ)
    (w : Γ → Φ → ℝ) (hw0 : ∀ γ F, 0 ≤ w γ F)
    (hwmean : ∀ γ, (∫ z, w γ (ρ z) ∂((percolation d p).prod (percolation d q))) = 1)
    (x₀ : Γ → Φ → X)
    (N : Γ × Γ → ℕ) (H : ℕ) (hN : ∀ y, N y ≤ H) {Λ C q₀ Mpow : ℝ}
    (hΛ : 0 ≤ Λ) (hC : 0 ≤ C) (hq₀ : 0 ≤ q₀) (hΛq : Λ * q₀ < 1) (hMpow : 0 < Mpow)
    (htail : ∀ j, (∑ y : Γ × Γ, if j + 1 ≤ N y then μ y.1 * μ y.2 else 0) ≤
      (C / Mpow) * q₀ ^ j)
    (hlarge : C * Λ / (1 - Λ * q₀) ≤ Mpow)
    (hcube : ∀ γ γ', (∫ z, (w γ (ρ z) * w γ' (ρ z)) * ϱ ^ sharedCount (sch γ γ' (ρ z))
      ∂((percolation d p).prod (percolation d q))) ≤ Λ ^ N (γ, γ')) :
    (1/8 : ℝ) ≤ ∫ z, (if (1/2:ℝ) ≤ routeWeightSum μ ρ w k n x₀ z then (1:ℝ) else 0)
      ∂((percolation d p).prod (percolation d q)) := by
  -- one route's term
  obtain ⟨T, hTdef⟩ : ∃ T : Γ → Configuration d × Configuration d → ℝ, T = fun γ z =>
      w γ (ρ z) * chainValue (k γ (ρ z)) (n γ (ρ z)) 0 (x₀ γ (ρ z)) z := ⟨_, rfl⟩
  have hT : ∀ γ, IsLoc (T γ) := by
    intro γ
    rw [hTdef]
    exact isLoc_of_reveal ρ S hρ
      (fun F z => w γ F * chainValue (k γ F) (n γ F) 0 (x₀ γ F) z)
      (fun F => (isLoc_const (w γ F)).mul
        ⟨_, chainValue_isLocal (B γ F) (k γ F) (hk γ F) (n γ F) 0 (x₀ γ F)⟩)
  have hWfun : routeWeightSum μ ρ w k n x₀ = fun z => ∑ γ, μ γ * T γ z := by
    rw [hTdef]
    rfl
  have hμT : ∀ γ, IsLoc (fun z => μ γ * T γ z) :=
    fun γ => (isLoc_const (μ γ)).mul (hT γ)
  have hW : IsLoc (routeWeightSum μ ρ w k n x₀) := by
    rw [hWfun]
    exact isLoc_sum hμT
  -- mean
  have hTmean : ∀ γ, (∫ z, T γ z ∂((percolation d p).prod (percolation d q))) = 1 := by
    intro γ
    rw [hTdef]
    exact (revealed_chain_mean p q ρ S hρ (B γ) (hB γ) (hSB γ) (k γ) (hk γ) (hnorm γ)
      (w γ) (n γ) (x₀ γ)).trans (hwmean γ)
  have hmean : (∫ z, routeWeightSum μ ρ w k n x₀ z
      ∂((percolation d p).prod (percolation d q))) = 1 := by
    rw [hWfun, integral_finsetSum _ (fun γ _ => (hμT γ).integrable p q)]
    have h : ∀ γ, (∫ z, μ γ * T γ z ∂((percolation d p).prod (percolation d q))) = μ γ := by
      intro γ
      rw [integral_const_mul, hTmean γ, mul_one]
    rw [Finset.sum_congr rfl (fun γ _ => h γ), hμ1]
  -- pair terms
  have hpair : ∀ γ γ', (∫ z, T γ z * T γ' z ∂((percolation d p).prod (percolation d q))) ≤
      Λ ^ N (γ, γ') := by
    intro γ γ'
    have h := revealed_pair_mass_le p q ρ S hρ (B γ) (B γ') (sch γ γ') (hfresh γ γ')
      (k γ) (k γ') (hk γ) (hk γ') (hk0 γ) (hk0 γ') hϱ
      (fun F t x => (hnorm γ F t x).le) (fun F t x => (hnorm γ' F t x).le) (hBoth γ γ')
      (fun F => w γ F * w γ' F) (fun F => mul_nonneg (hw0 γ F) (hw0 γ' F)) (x₀ γ) (x₀ γ')
    refine le_trans (le_of_eq ?_) (h.trans (hcube γ γ'))
    apply integral_congr_ae
    refine Filter.Eventually.of_forall fun z => ?_
    rw [hTdef]
    change (w γ (ρ z) * chainValue (k γ (ρ z)) (n γ (ρ z)) 0 (x₀ γ (ρ z)) z) *
        (w γ' (ρ z) * chainValue (k γ' (ρ z)) (n γ' (ρ z)) 0 (x₀ γ' (ρ z)) z) =
      (w γ (ρ z) * w γ' (ρ z)) *
        (chainValue (k γ (ρ z)) (leftCount (sch γ γ' (ρ z))) 0 (x₀ γ (ρ z)) z *
          chainValue (k γ' (ρ z)) (rightCount (sch γ γ' (ρ z))) 0 (x₀ γ' (ρ z)) z)
    rw [hleft γ γ' (ρ z), hright γ γ' (ρ z)]
    ring
  -- second moment
  have hsq : (fun z => routeWeightSum μ ρ w k n x₀ z ^ 2) =
      fun z => ∑ γ, ∑ γ', (μ γ * μ γ') * (T γ z * T γ' z) := by
    funext z
    rw [hWfun]
    change (∑ γ, μ γ * T γ z) ^ 2 = _
    rw [pow_two, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl (fun γ _ => Finset.sum_congr rfl (fun γ' _ => by ring))
  have hloc2 : ∀ γ γ', IsLoc (fun z => (μ γ * μ γ') * (T γ z * T γ' z)) :=
    fun γ γ' => (isLoc_const (μ γ * μ γ')).mul ((hT γ).mul (hT γ'))
  have hνprob : (∑ y : Γ × Γ, μ y.1 * μ y.2) = 1 := by
    rw [Fintype.sum_prod_type]
    change (∑ γ, ∑ γ', μ γ * μ γ') = 1
    rw [← Fintype.sum_mul_sum, hμ1, mul_one]
  have hEIT := exponential_count_moment_le_two (fun y : Γ × Γ => μ y.1 * μ y.2) N
    (fun y => mul_nonneg (hμ0 y.1) (hμ0 y.2)) hνprob H hN hΛ hC hq₀ hΛq hMpow htail hlarge
  have hsecond : (∫ z, routeWeightSum μ ρ w k n x₀ z ^ 2
      ∂((percolation d p).prod (percolation d q))) ≤ 2 := by
    rw [hsq, integral_finsetSum _ (fun γ _ => (isLoc_sum (hloc2 γ)).integrable p q)]
    have h1 : ∀ γ, (∫ z, ∑ γ', (μ γ * μ γ') * (T γ z * T γ' z)
        ∂((percolation d p).prod (percolation d q))) ≤
        ∑ γ', (μ γ * μ γ') * Λ ^ N (γ, γ') := by
      intro γ
      rw [integral_finsetSum _ (fun γ' _ => (hloc2 γ γ').integrable p q)]
      refine Finset.sum_le_sum (fun γ' _ => ?_)
      rw [integral_const_mul]
      exact mul_le_mul_of_nonneg_left (hpair γ γ') (mul_nonneg (hμ0 γ) (hμ0 γ'))
    refine (Finset.sum_le_sum (fun γ _ => h1 γ)).trans ?_
    rw [Fintype.sum_prod_type] at hEIT
    exact hEIT
  exact coupled_paley_zygmund p q hW hmean hsecond

end NearCritical.Section10
