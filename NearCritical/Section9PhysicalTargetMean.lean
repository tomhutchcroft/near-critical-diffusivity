module
public import NearCritical.Section9PhysicalTargetVariance

/-! Actual fresh target-success mean from nonempty physical pools. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory
open scoped Classical BigOperators

/-- Each nonempty physical pool has success probability at least q.
No disjointness of pools or target-success independence is required. -/
theorem section9_physical_target_success_mean_lower {d : ℕ} {ι : Type*}
    (q : unitInterval) (I : Finset ι) (pools : ι → Finset (Bond d)) :
    (q : ℝ)*((I.filter (fun j => (pools j).Nonempty)).card : ℝ) ≤
      ∫ ζ : Configuration d, (∑ j ∈ I,
        if ∃ b ∈ pools j, ζ b = true then (1 : ℝ) else 0) ∂percolation d q := by
  let μ := percolation d q
  let E := fun j => {ζ : Configuration d | ∃ b ∈ pools j, ζ b = true}
  have hE (j : ι) : MeasurableSet (E j) := by
    have he : E j = (pools j).restrict ⁻¹'
        {ξ : (pools j) → Bool | ∃ b, ξ b = true} := by
      ext ζ
      simp [E,Finset.restrict]
    rw [he]
    exact (Set.toFinite _).measurableSet.preimage (Finset.measurable_restrict (pools j))
  have hmean : (∫ ζ : Configuration d, (∑ j ∈ I,
        if ∃ b ∈ pools j, ζ b = true then (1 : ℝ) else 0) ∂μ) = ∑ j ∈ I, μ.real (E j) := by
    have hfun : (fun ζ : Configuration d => ∑ j ∈ I,
        if ∃ b ∈ pools j, ζ b = true then (1 : ℝ) else 0) =
        (fun ζ => ∑ j ∈ I, (E j).indicator (fun _ => (1 : ℝ)) ζ) := by
      funext ζ
      simp only [E,Set.indicator_apply,Set.mem_setOf_eq]
    rw [hfun,integral_finsetSum I (fun j _ => (integrable_const (1 : ℝ)).indicator (hE j))]
    exact Finset.sum_congr rfl (fun j _ => integral_indicator_one (hE j))
  rw [hmean]
  calc
    _ = ∑ j ∈ I, if (pools j).Nonempty then (q : ℝ) else 0 := by
      rw [← Finset.sum_filter,Finset.sum_const,nsmul_eq_mul,mul_comm]
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro j _
      by_cases hj : (pools j).Nonempty
      · rw [if_pos hj]
        obtain ⟨b,hb⟩ := hj
        have hsingle : μ.real {ζ : Configuration d | ζ b = true} = (q : ℝ) := by
          simpa using section9_physical_bonds_open_probability q ({b} : Finset (Bond d))
        rw [← hsingle]
        apply measureReal_mono _ (measure_ne_top _ _)
        intro ζ hζ
        exact ⟨b,hb,hζ⟩
      · rw [if_neg hj]
        exact measureReal_nonneg

end NearCritical
