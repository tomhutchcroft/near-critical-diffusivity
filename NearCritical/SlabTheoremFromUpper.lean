module

public import NearCritical.SlabCriticalLower
public import NearCritical.CriticalPointInterior

/-! Combine the lower estimate and subgraph comparison with the upper
estimate for the two-dimensional slab. -/
@[expose] public section
noncomputable section

namespace NearCritical

/-- The two-sided slab estimate once the two-dimensional slab upper
estimate is supplied. The lower branch uses the weighted pioneer input. -/
theorem slab_theorem_from_upper {d : ℕ} (hd : 3 ≤ d) (hA : TwoPointAsymptotics d)
    {C c : ℝ} (hC : 0 < C) (hc : 0 < c)
    (decay : WeightedPositiveHeightPioneerDecay (criticalPoint d)
      (⟨d-1, by omega⟩ : Fin d) C c)
    (hupper : ∃ A : ℝ, ∀ n : ℕ, 1 ≤ n →
      (restrictedCriticalPoint d (slabVertices d 2 n) : ℝ) - criticalPoint d ≤
        A / (n : ℝ) ^ 2) :
    ∃ a A : ℝ, 0 < a ∧ 0 < A ∧ ∀ n : ℕ, 1 ≤ n →
      a / (n : ℝ) ^ 2 ≤
        (restrictedCriticalPoint d (slabVertices d (d-1) n) : ℝ) - criticalPoint d ∧
      (restrictedCriticalPoint d (slabVertices d (d-1) n) : ℝ) - criticalPoint d ≤
        (restrictedCriticalPoint d (slabVertices d 2 n) : ℝ) - criticalPoint d ∧
      (restrictedCriticalPoint d (slabVertices d 2 n) : ℝ) - criticalPoint d ≤
        A / (n : ℝ) ^ 2 := by
  obtain ⟨hpc, hpc1⟩ :=
    criticalPoint_interior_of_twoPointAsymptotics (by omega) (⟨0, by omega⟩ : Fin d) hA
  obtain ⟨a, ha, hlow⟩ := slabCriticalPoint_lower_of_weighted (by omega) hC hc hpc hpc1 decay
  obtain ⟨A, hA'⟩ := hupper
  refine ⟨a, max 1 A, ha, zero_lt_one.trans_le (le_max_left _ _), fun n hn => ⟨hlow n hn, ?_, ?_⟩⟩
  · have hmid : (restrictedCriticalPoint d (slabVertices d (d-1) n) : ℝ) ≤
        restrictedCriticalPoint d (slabVertices d 2 n) :=
      slabCriticalPoint_comparison d n hd
    exact sub_le_sub_right hmid _
  · exact (hA' n hn).trans (div_le_div_of_nonneg_right (le_max_right _ _) (sq_nonneg _))

end NearCritical
