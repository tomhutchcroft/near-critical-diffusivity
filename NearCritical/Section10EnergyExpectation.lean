module

public import NearCritical.Section10EnergyAssembly

/-! Expected energy of the flow of `prop.nw.main`.

`energy_expectation_le`: let `En >= 0` be any function of the configuration pair
(in the application, the energy of the normalised flow on `{W >= 1/2}`, zero
elsewhere) that is pointwise bounded as in `flow_energy_le_marked`, with marks
`2 * tau + (1 - tau) * sigma` (`tau`: the two bridges intersect; `sigma`: site
entanglement). If for every pair of routes and every reveal atom the one-step
estimates of `pair_entanglement_le` hold for the pair kernel, then

  `E[En] <= 4 Pb sum_{γ,γ'} mu mu' E[omega_γ omega_γ' * entanglementBound]`.

This is the second display of the energy part of the proof of `prop.nw.main`
(5787), before the sum over routes. Hypotheses still to be supplied for the
lattice rule: the flows and `lem.nw.overlap` (through `hEn`) and the one-step
estimates of `lem.nw.H`.
-/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open MeasureTheory
open scoped Classical BigOperators

lemma markedValue_linear {d : ℕ} {X : Type*} [Fintype X]
    (k a c : ℕ → X → X → Configuration d × Configuration d → ℝ) (α : ℝ) :
    ∀ (m t : ℕ) (x : X) (z : Configuration d × Configuration d),
      markedValue k (fun t x y z => α * a t x y z + c t x y z) m t x z =
        α * markedValue k a m t x z + markedValue k c m t x z := by
  intro m
  induction m with
  | zero =>
    intro t x z
    simp [markedValue]
  | succ m ih =>
    intro t x z
    simp only [markedValue, ih]
    simp only [Finset.mul_sum, mul_add, add_mul, Finset.sum_add_distrib]
    have h1 : ∀ y, α * a t x y z * chainValue k m (t+1) y z =
        α * (a t x y z * chainValue k m (t+1) y z) := fun y => by ring
    have h2 : ∀ y, k t x y z * (α * markedValue k a m (t+1) y z) =
        α * (k t x y z * markedValue k a m (t+1) y z) := fun y => by ring
    simp only [h1, h2]
    ring

theorem energy_expectation_le {d : ℕ} {X Φ Γ : Type*} [Fintype X] [Fintype Φ] [Fintype Γ]
    (p q : unitInterval) (ρr : Configuration d × Configuration d → Φ)
    (Sx : Φ → Finset (LBond d))
    (hρr : ∀ F, IsLocal (Sx F) (fun z => if ρr z = F then (1:ℝ) else 0))
    (μ : Γ → ℝ) (hμ : ∀ γ, 0 ≤ μ γ) (w : Γ → Φ → ℝ) (hw : ∀ γ F, 0 ≤ w γ F)
    (B : Γ → Γ → Φ → ℕ → Finset (LBond d))
    (hB : ∀ γ γ' F i j, i ≠ j → Disjoint (B γ γ' F i) (B γ γ' F j))
    (hSB : ∀ γ γ' F j, Disjoint (Sx F) (B γ γ' F j))
    (k : Γ → Φ → ℕ → X → X → Configuration d × Configuration d → ℝ)
    (hk0 : ∀ γ F t x y z, 0 ≤ k γ F t x y z)
    (hK : ∀ γ γ' F t x y, IsLocal (B γ γ' F t) (pairKernel (k γ F) (k γ' F) t x y))
    (τ σ : Γ → Γ → Φ → ℕ → X × X → X × X → Configuration d × Configuration d → ℝ)
    (hτ : ∀ γ γ' F t x y, IsLocal (B γ γ' F t) (τ γ γ' F t x y))
    (hσ : ∀ γ γ' F t x y, IsLocal (B γ γ' F t) (σ γ γ' F t x y))
    (hτ01 : ∀ γ γ' F t x y z, 0 ≤ τ γ γ' F t x y z ∧ τ γ γ' F t x y z ≤ 1)
    (hσ0 : ∀ γ γ' F t x y z, 0 ≤ σ γ γ' F t x y z)
    (ρ δ : Γ → Γ → Φ → ℕ → ℝ) (hρ : ∀ γ γ' F t, 1 ≤ ρ γ γ' F t)
    (hδ : ∀ γ γ' F t, 0 ≤ δ γ γ' F t) {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (hrow : ∀ γ γ' F t x, ∑ y, (∫ z, pairKernel (k γ F) (k γ' F) t x y z
      ∂((percolation d p).prod (percolation d q))) ≤ ρ γ γ' F t)
    (φ : Γ → Γ → Φ → ℕ → X × X → ℝ) (hφ0 : ∀ γ γ' F t x, 0 ≤ φ γ γ' F t x)
    (hpersist : ∀ γ γ' F t x, ∑ y, (∫ z, pairKernel (k γ F) (k γ' F) t x y z *
      τ γ γ' F t x y z ∂((percolation d p).prod (percolation d q))) * φ γ γ' F (t+1) y ≤
      θ * ∑ y, ∫ z, pairKernel (k γ F) (k γ' F) t x y z * τ γ γ' F t x y z ∂((percolation d p).prod (percolation d q)))
    (henter : ∀ γ γ' F t x, ∑ y, (∫ z, pairKernel (k γ F) (k γ' F) t x y z *
        (1 - τ γ γ' F t x y z) ∂((percolation d p).prod (percolation d q))) * φ γ γ' F (t+1) y ≤
      φ γ γ' F t x - (∑ y, ∫ z, pairKernel (k γ F) (k γ' F) t x y z *
        τ γ γ' F t x y z ∂((percolation d p).prod (percolation d q))) + δ γ γ' F t)
    (hsite : ∀ γ γ' F t x, ∑ y, (∫ z, pairKernel (k γ F) (k γ' F) t x y z *
      (1 - τ γ γ' F t x y z) * σ γ γ' F t x y z
      ∂((percolation d p).prod (percolation d q))) ≤ δ γ γ' F t)
    (m : ℕ) (x₀ : Γ → Φ → X) {Pb : ℝ} (hPb : 0 ≤ Pb)
    (En : Configuration d × Configuration d → ℝ) (hEn0 : ∀ z, 0 ≤ En z)
    (hEn : ∀ z, En z ≤ 4 * (Pb * ∑ γ, ∑ γ', (μ γ * μ γ') * ((w γ (ρr z) * w γ' (ρr z)) *
      markedValue (pairKernel (k γ (ρr z)) (k γ' (ρr z)))
        (fun t x y z' => pairKernel (k γ (ρr z)) (k γ' (ρr z)) t x y z' *
          (2 * τ γ γ' (ρr z) t x y z' +
            (1 - τ γ γ' (ρr z) t x y z') * σ γ γ' (ρr z) t x y z')) m 0
        (x₀ γ (ρr z), x₀ γ' (ρr z)) z))) :
    (∫ z, En z ∂((percolation d p).prod (percolation d q))) ≤
      4 * (Pb * ∑ γ, ∑ γ', (μ γ * μ γ') *
        ∫ z, (w γ (ρr z) * w γ' (ρr z)) *
          entanglementBound (ρ γ γ' (ρr z)) (δ γ γ' (ρr z)) θ
            (φ γ γ' (ρr z) 0 (x₀ γ (ρr z), x₀ γ' (ρr z))) m
          ∂((percolation d p).prod (percolation d q))) := by
  -- the three mark kernels of a pair on an atom
  obtain ⟨a, ha⟩ : ∃ a : Γ → Γ → Φ → ℕ → X × X → X × X →
      Configuration d × Configuration d → ℝ, a = fun γ γ' F t x y z =>
      pairKernel (k γ F) (k γ' F) t x y z * τ γ γ' F t x y z := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : Γ → Γ → Φ → ℕ → X × X → X × X →
      Configuration d × Configuration d → ℝ, b = fun γ γ' F t x y z =>
      pairKernel (k γ F) (k γ' F) t x y z * (1 - τ γ γ' F t x y z) := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : Γ → Γ → Φ → ℕ → X × X → X × X →
      Configuration d × Configuration d → ℝ, c = fun γ γ' F t x y z =>
      pairKernel (k γ F) (k γ' F) t x y z * (1 - τ γ γ' F t x y z) * σ γ γ' F t x y z :=
    ⟨_, rfl⟩
  have hKnn : ∀ γ γ' F t x y z, 0 ≤ pairKernel (k γ F) (k γ' F) t x y z :=
    fun γ γ' F t x y z => mul_nonneg (hk0 γ F t _ _ z) (hk0 γ' F t _ _ z)
  have haloc : ∀ γ γ' F t x y, IsLocal (B γ γ' F t) (a γ γ' F t x y) := fun γ γ' F t x y => by
    rw [ha]
    exact (hK γ γ' F t x y).mul (hτ γ γ' F t x y)
  have hbloc : ∀ γ γ' F t x y, IsLocal (B γ γ' F t) (b γ γ' F t x y) := fun γ γ' F t x y => by
    rw [hb]
    have h1 : IsLocal (B γ γ' F t) (fun z => 1 - τ γ γ' F t x y z) := by
      obtain ⟨g, hg⟩ := hτ γ γ' F t x y
      exact ⟨fun v => 1 - g v, fun z => by
        show 1 - τ γ γ' F t x y z = 1 - g _
        rw [hg z]⟩
    exact (hK γ γ' F t x y).mul h1
  have hcloc : ∀ γ γ' F t x y, IsLocal (B γ γ' F t) (c γ γ' F t x y) := fun γ γ' F t x y => by
    have h := (hbloc γ γ' F t x y).mul (hσ γ γ' F t x y)
    rw [hb] at h
    rw [hc]
    exact h
  -- per pair: the revealed estimate
  have hpair : ∀ γ γ', (∫ z, (w γ (ρr z) * w γ' (ρr z)) *
      markedValue (pairKernel (k γ (ρr z)) (k γ' (ρr z)))
        (fun t x y z' => pairKernel (k γ (ρr z)) (k γ' (ρr z)) t x y z' *
          (2 * τ γ γ' (ρr z) t x y z' +
            (1 - τ γ γ' (ρr z) t x y z') * σ γ γ' (ρr z) t x y z')) m 0
        (x₀ γ (ρr z), x₀ γ' (ρr z)) z ∂((percolation d p).prod (percolation d q))) ≤
      ∫ z, (w γ (ρr z) * w γ' (ρr z)) *
        entanglementBound (ρ γ γ' (ρr z)) (δ γ γ' (ρr z)) θ
          (φ γ γ' (ρr z) 0 (x₀ γ (ρr z), x₀ γ' (ρr z))) m
        ∂((percolation d p).prod (percolation d q)) := by
    intro γ γ'
    have h := revealed_pair_entanglement_le p q ρr Sx hρr (B γ γ') (hB γ γ') (hSB γ γ')
      (fun F => pairKernel (k γ F) (k γ' F)) (a γ γ') (b γ γ') (c γ γ') (hK γ γ')
      (haloc γ γ') (hbloc γ γ') (hcloc γ γ')
      (fun F t x y z => by
        rw [ha]
        exact mul_nonneg (hKnn γ γ' F t x y z) (hτ01 γ γ' F t x y z).1)
      (fun F t x y z => by
        rw [hb]
        exact mul_nonneg (hKnn γ γ' F t x y z) (sub_nonneg.mpr (hτ01 γ γ' F t x y z).2))
      (fun F t x y z => by
        rw [hc]
        exact mul_nonneg (mul_nonneg (hKnn γ γ' F t x y z)
          (sub_nonneg.mpr (hτ01 γ γ' F t x y z).2)) (hσ0 γ γ' F t x y z))
      (fun F t x y z => by
        rw [ha, hb]
        ring)
      (ρ γ γ') (δ γ γ') (hρ γ γ') (hδ γ γ') hθ0 hθ1 (hrow γ γ')
      (φ γ γ') (hφ0 γ γ')
      (fun F t x => by rw [ha]; exact hpersist γ γ' F t x)
      (fun F t x => by rw [ha, hb]; exact henter γ γ' F t x)
      (fun F t x => by rw [hc]; exact hsite γ γ' F t x)
      (fun F => w γ F * w γ' F) (fun F => mul_nonneg (hw γ F) (hw γ' F)) m
      (fun F => (x₀ γ F, x₀ γ' F))
    rw [ha] at h
    refine le_trans (le_of_eq ?_) h
    apply integral_congr_ae
    refine Filter.Eventually.of_forall fun z => ?_
    show (w γ (ρr z) * w γ' (ρr z)) * _ = (w γ (ρr z) * w γ' (ρr z)) * _
    congr 1
    have hlin := markedValue_linear (pairKernel (k γ (ρr z)) (k γ' (ρr z)))
      (a γ γ' (ρr z)) (c γ γ' (ρr z)) 2 m 0 (x₀ γ (ρr z), x₀ γ' (ρr z)) z
    rw [ha, hc] at hlin
    rw [hc, ← hlin]
    congr 1
    funext t x y z'
    ring
  -- integrability of the pointwise bound
  have hloc : ∀ γ γ', IsLoc (fun z => (w γ (ρr z) * w γ' (ρr z)) *
      markedValue (pairKernel (k γ (ρr z)) (k γ' (ρr z)))
        (fun t x y z' => pairKernel (k γ (ρr z)) (k γ' (ρr z)) t x y z' *
          (2 * τ γ γ' (ρr z) t x y z' +
            (1 - τ γ γ' (ρr z) t x y z') * σ γ γ' (ρr z) t x y z')) m 0
        (x₀ γ (ρr z), x₀ γ' (ρr z)) z) := by
    intro γ γ'
    refine isLoc_of_reveal ρr Sx hρr
      (fun F z => (w γ F * w γ' F) *
        markedValue (pairKernel (k γ F) (k γ' F))
          (fun t x y z' => pairKernel (k γ F) (k γ' F) t x y z' *
            (2 * τ γ γ' F t x y z' + (1 - τ γ γ' F t x y z') * σ γ γ' F t x y z')) m 0
          (x₀ γ F, x₀ γ' F) z) (fun F => ?_)
    refine (isLoc_const _).mul (markedValue_isLoc (B γ γ' F) _ _ (hK γ γ' F) (fun t x y => ?_)
      m 0 _)
    have h2 : IsLocal (B γ γ' F t) (fun z' => 2 * τ γ γ' F t x y z' +
        (1 - τ γ γ' F t x y z') * σ γ γ' F t x y z') := by
      obtain ⟨g, hg⟩ := hτ γ γ' F t x y
      obtain ⟨g', hg'⟩ := hσ γ γ' F t x y
      exact ⟨fun v => 2 * g v + (1 - g v) * g' v, fun z' => by
        show 2 * τ γ γ' F t x y z' + (1 - τ γ γ' F t x y z') * σ γ γ' F t x y z' = _
        rw [hg z', hg' z']⟩
    exact (hK γ γ' F t x y).mul h2
  obtain ⟨Tm, hTm⟩ : ∃ Tm : Γ → Γ → Configuration d × Configuration d → ℝ,
      Tm = fun γ γ' z => (w γ (ρr z) * w γ' (ρr z)) *
      markedValue (pairKernel (k γ (ρr z)) (k γ' (ρr z)))
        (fun t x y z' => pairKernel (k γ (ρr z)) (k γ' (ρr z)) t x y z' *
          (2 * τ γ γ' (ρr z) t x y z' +
            (1 - τ γ γ' (ρr z) t x y z') * σ γ γ' (ρr z) t x y z')) m 0
        (x₀ γ (ρr z), x₀ γ' (ρr z)) z := ⟨_, rfl⟩
  have hTmloc : ∀ γ γ', IsLoc (Tm γ γ') := fun γ γ' => by rw [hTm]; exact hloc γ γ'
  have hEn' : ∀ z, En z ≤ 4 * (Pb * ∑ γ, ∑ γ', (μ γ * μ γ') * Tm γ γ' z) := by
    intro z
    rw [hTm]
    exact hEn z
  have hbigloc : IsLoc (fun z => 4 * (Pb * ∑ γ, ∑ γ', (μ γ * μ γ') * Tm γ γ' z)) :=
    (isLoc_const 4).mul ((isLoc_const Pb).mul (isLoc_sum (fun γ => isLoc_sum (fun γ' =>
      (isLoc_const (μ γ * μ γ')).mul (hTmloc γ γ')))))
  have hstep1 : (∫ z, En z ∂((percolation d p).prod (percolation d q))) ≤
      ∫ z, 4 * (Pb * ∑ γ, ∑ γ', (μ γ * μ γ') * Tm γ γ' z)
        ∂((percolation d p).prod (percolation d q)) :=
    integral_mono_of_nonneg (Filter.Eventually.of_forall hEn0) (hbigloc.integrable p q)
      (Filter.Eventually.of_forall hEn')
  refine hstep1.trans ?_
  rw [integral_const_mul, integral_const_mul]
  refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hPb) (by norm_num)
  rw [integral_finsetSum _ (fun γ _ => (isLoc_sum (fun γ' =>
    (isLoc_const (μ γ * μ γ')).mul (hTmloc γ γ'))).integrable p q)]
  refine Finset.sum_le_sum (fun γ _ => ?_)
  rw [integral_finsetSum _ (fun γ' _ =>
    ((isLoc_const (μ γ * μ γ')).mul (hTmloc γ γ')).integrable p q)]
  refine Finset.sum_le_sum (fun γ' _ => ?_)
  rw [integral_const_mul]
  refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (hμ γ) (hμ γ'))
  rw [hTm]
  exact hpair γ γ'

end NearCritical.Section10
