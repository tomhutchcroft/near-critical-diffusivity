module

public import NearCritical.BKAllParameters
public import NearCritical.CylinderDisjointOccurrence

/-! All-parameter BK for finite-coordinate events in the actual infinite lattice
percolation law, with the standard full-configuration disjoint-occurrence operator. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Set MeasureTheory ProbabilityTheory
open scoped Classical

lemma eventProbability_cylinder (d : ℕ) (p : unitInterval) (s : Finset (Bond d))
    (A : Set ((e : s) → Bool)) :
    BK.eventProbability (p : ℝ) A = (percolation d p).real ((s.restrict) ⁻¹' A) := by
  classical
  calc
    _ = ∫ ω, (if s.restrict ω ∈ A then (1 : ℝ) else 0) ∂percolation d p :=
      (percolation_cylinder_expectation d p s (fun η ↦ if η ∈ A then (1 : ℝ) else 0)).symm
    _ = _ := by
      have hA : MeasurableSet A := (Set.toFinite A).measurableSet
      have hRestr : Measurable (s.restrict : Configuration d → ((e : s) → Bool)) :=
        Finset.measurable_restrict s
      have hs : MeasurableSet {ω : Configuration d | s.restrict ω ∈ A} := by
        convert! hA.preimage hRestr using 1
      have h := integral_indicator_one (μ := percolation d p) hs
      simpa only [Set.indicator, Pi.one_apply, Set.mem_preimage] using! h

/-- BK for cylinder events under the concrete infinite product law. The circle
operator is the standard one on ALL lattice bonds, not a weakened finite proxy. -/
theorem percolation_cylinder_bk (d : ℕ) (p : unitInterval) (s : Finset (Bond d))
    (A B : Set ((e : s) → Bool)) (hA : BK.Increasing A) (hB : BK.Increasing B) :
    (percolation d p).real
        {ω | DisjointOccurrence ((s.restrict) ⁻¹' A) ((s.restrict) ⁻¹' B) ω} ≤
      (percolation d p).real ((s.restrict) ⁻¹' A) *
      (percolation d p).real ((s.restrict) ⁻¹' B) := by
  have heq : {ω | DisjointOccurrence ((s.restrict) ⁻¹' A) ((s.restrict) ⁻¹' B) ω} =
      (s.restrict) ⁻¹' BK.occurrenceEvent A B := by
    ext ω
    exact (disjointOccurrence_restrict_iff s A B ω).symm
  rw [heq]
  have h := BK.bk_eventProbability p A B hA hB
  rw [eventProbability_cylinder d p s, eventProbability_cylinder d p s,
    eventProbability_cylinder d p s] at h
  exact h

end NearCritical
