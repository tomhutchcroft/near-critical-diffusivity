module

public import NearCritical.SlabUpperAssembly
public import NearCritical.SlabCriticalLower

/-! Source Theorem 1.3 (thm.slab, eq.main_slab), assembled from its three
inequalities (source 6101–6104):

* first:  `SlabCriticalLower.slabCriticalPoint_lower_of_weighted`
  (cited weighted critical pioneer decay as the explicit STANDARD input);
* second: `Slab.slabCriticalPoint_comparison` (subgraph monotonicity, unconditional);
* third:  `SlabUpperAssembly.slab_upper_inverse_square`
  (explicit renormalized-exploration data, see `RenormalizedExploration`).

This is a CONDITIONAL statement: neither the pioneer decay nor the renormalized
exploration data are constructed here. It does not establish thm.slab
unconditionally. -/

@[expose] public section

namespace NearCritical

open scoped ENNReal

theorem slab_theorem_of_inputs {d : ℕ} (hd : 3 ≤ d)
    {C c : ℝ} (hC : 0 < C) (hc : 0 < c) (hpc : 0 < (criticalPoint d : ℝ))
    (hpc1 : (criticalPoint d : ℝ) < 1)
    (decay : WeightedPositiveHeightPioneerDecay (criticalPoint d)
      (⟨d-1, by omega⟩ : Fin d) C c)
    {lam : ℝ} (hlam : 0 < lam) (n₀ : ℕ)
    (hmodel : ∀ n : ℕ, n₀ ≤ n → 1 ≤ n → ∀ p : unitInterval,
      (p : ℝ) = (criticalPoint d : ℝ) + lam / (n : ℝ) ^ 2 →
        ∃ (F : Finset (Vertex d)) (θ : ℝ≥0∞), θ ≠ 0 ∧
          ∀ N, Nonempty (RenormalizedExploration d p (slabVertices d 2 n) F N θ)) :
    ∃ a A : ℝ, 0 < a ∧ ∀ n : ℕ, 1 ≤ n →
      a / (n : ℝ) ^ 2 ≤
          (restrictedCriticalPoint d (slabVertices d (d-1) n) : ℝ) - criticalPoint d ∧
        (restrictedCriticalPoint d (slabVertices d (d-1) n) : ℝ) - criticalPoint d ≤
          (restrictedCriticalPoint d (slabVertices d 2 n) : ℝ) - criticalPoint d ∧
        (restrictedCriticalPoint d (slabVertices d 2 n) : ℝ) - criticalPoint d ≤
          A / (n : ℝ) ^ 2 := by
  obtain ⟨a, ha, hlow⟩ :=
    slabCriticalPoint_lower_of_weighted (by omega) hC hc hpc hpc1 decay
  obtain ⟨A, hup⟩ := slab_upper_inverse_square hlam n₀ hmodel
  refine ⟨a, A, ha, fun n hn ↦ ⟨hlow n hn, ?_, hup n hn⟩⟩
  have hmid := slabCriticalPoint_comparison d n hd
  have : (restrictedCriticalPoint d (slabVertices d (d-1) n) : ℝ) ≤
      restrictedCriticalPoint d (slabVertices d 2 n) := hmid
  linarith

end NearCritical
