module

public import NearCritical.Section10StepRuleWeight
public import NearCritical.Section10SiteWeights
public import NearCritical.Section10RouteLaw

/-! `prop.nw.main`, first conclusion, with the ACTUAL route law.

Routes are `SourceRoute D M` with the survival-conditioned law `routeLaw`; the
exponential intersection tail is the proved `routeLaw_tail`. The cube weight of
a route is the product of normalised site indicators over its sites, and the
chains use the source step kernel.

What remains hypothetical is local and deterministic data:
* the reveal and its explored bonds;
* labels (tubes), their blocks, and a rank increasing along each route;
* the step rule with `1/rho <= s_t`;
* site indicators `u a` (local on disjoint cube bonds, mean one,
  second moment at most `kappa`) and the identification of `w γ (reveal)` with
  their product;
* the counting inequality
  `rho ^ #common labels * kappa ^ #common sites <= Lambda ^ #common levels`;
* `Lambda q0 < 1` and `M` large.
-/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open MeasureTheory
open scoped Classical BigOperators

theorem sourceRoute_good_weight_probability {D : ℕ} (hD : 3 ≤ D) :
    ∃ (q0 C : ℝ) (M₀ : ℕ), 0 < q0 ∧ q0 < 1 ∧ 0 ≤ C ∧ ∀ M ≥ M₀,
    ∀ {d : ℕ} {X Φ E A : Type*} [Fintype X] [Fintype Φ] (p q : unitInterval)
      (ρ : Configuration d × Configuration d → Φ) (S : Φ → Finset (LBond d))
      (_hρ : ∀ F, IsLocal (S F) (fun z => if ρ z = F then (1:ℝ) else 0))
      (rank : E → ℕ) (Bl : Φ → E → Finset (LBond d))
      (_hBl : ∀ F a b, a ≠ b → Disjoint (Bl F a) (Bl F b))
      (_hS : ∀ F a, Disjoint (S F) (Bl F a))
      (lab : SourceRoute D M → ℕ → E)
      (_hlab : ∀ γ, StrictMono (fun t => rank (lab γ t))) (n : SourceRoute D M → ℕ)
      (a : ∀ (γ : SourceRoute D M) (F : Φ) (t : ℕ), X → Set (Bl F (lab γ t) → Bool))
      (o : ∀ (γ : SourceRoute D M) (F : Φ) (t : ℕ), X →
        (Bl F (lab γ t) → Bool) → Finset X)
      (_ho : ∀ γ F t x, ∀ b ∈ a γ F t x, (o γ F t x b).Nonempty)
      {ϱ : ℝ} (_hϱ : 1 ≤ ϱ)
      (_hs : ∀ γ F t x, ϱ⁻¹ ≤ localSuccessProbability p q (Bl F (lab γ t)) (a γ F t x))
      (Es : A → Finset (LBond d)) (_hEs : ∀ a b, a ≠ b → Disjoint (Es a) (Es b))
      (u : A → Configuration d × Configuration d → ℝ) (_hu : ∀ a, IsLocal (Es a) (u a))
      (_hu0 : ∀ a z, 0 ≤ u a z)
      (_humean : ∀ a, (∫ z, u a z ∂((percolation d p).prod (percolation d q))) = 1)
      {κ : ℝ} (_hκ : 1 ≤ κ)
      (_husq : ∀ a, (∫ z, u a z * u a z ∂((percolation d p).prod (percolation d q))) ≤ κ)
      (sites : SourceRoute D M → Finset A)
      (w : SourceRoute D M → Φ → ℝ) (_hw0 : ∀ γ F, 0 ≤ w γ F)
      (_hwu : ∀ γ z, w γ (ρ z) = ∏ a ∈ sites γ, u a z)
      (x₀ : SourceRoute D M → Φ → X)
      {Λ : ℝ} (_hΛ : 0 ≤ Λ) (_hΛq : Λ * q0 < 1)
      (_hlarge : C * Λ / (1 - Λ * q0) ≤ (M:ℝ) ^ (D-1))
      (_hcount : ∀ γ γ', ϱ ^ commonLabelCount (lab γ) (lab γ') (n γ) (n γ') *
        κ ^ (sites γ ∩ sites γ').card ≤ Λ ^ routeCommonLevels D M (γ, γ')),
      (1/8 : ℝ) ≤ ∫ z, (if (1/2:ℝ) ≤
          routeWeightSum (routeLaw D M) ρ w (sourceKernel p q Bl lab a o) (fun γ _ => n γ) x₀ z
        then (1:ℝ) else 0) ∂((percolation d p).prod (percolation d q)) := by
  obtain ⟨q0, C, M₀, hq0, hq1, hC, hlaw⟩ := routeLaw_tail hD
  refine ⟨q0, C, max M₀ 1, hq0, hq1, hC, ?_⟩
  intro M hM d X Φ E A _ _ p q ρ S hρ rank Bl hBl hS lab hlab n a o ho ϱ hϱ hs Es hEs u hu
    hu0 humean κ hκ husq sites w hw0 hwu x₀ Λ hΛ hΛq hlarge hcount
  obtain ⟨hμ0, hμ1, htail⟩ := hlaw M ((le_max_left _ _).trans hM)
  have hM1 : 1 ≤ M := (le_max_right _ _).trans hM
  have hMpow : (0:ℝ) < (M:ℝ) ^ (D-1) := pow_pos (by exact_mod_cast hM1) _
  refine sourceRule_good_weight_probability p q ρ S hρ (routeLaw D M) hμ0 hμ1 rank Bl hBl hS
    lab hlab n a o ho hϱ hs w hw0 ?_ x₀ (routeCommonLevels D M) M (routeCommonLevels_le D M)
    hΛ hC hq0.le hΛq hMpow htail hlarge ?_
  · intro γ
    simp only [hwu]
    exact siteWeight_mean p q Es hEs u hu humean (sites γ)
  · intro γ γ'
    simp only [hwu]
    refine le_trans ?_ (hcount γ γ')
    exact mul_le_mul_of_nonneg_left
      (siteWeight_pair_le p q Es hEs u hu hu0 humean hκ husq (sites γ) (sites γ'))
      (pow_nonneg (zero_le_one.trans hϱ) _)

end NearCritical.Section10
