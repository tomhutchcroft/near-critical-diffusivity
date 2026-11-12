module

public import NearCritical.LatticeBK
public import NearCritical.SourceProbabilityReduction

/-! Exact BK reduction of the paper's finite-volume energies. No one-arm or
half-space decay estimate is assumed or claimed. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory

/-- The two orientations from the source two-arm event, after BK. -/
def boundaryConnectionProducts {d : ℕ} (U : Finset (Vertex d)) (i : Fin d)
    (p : unitInterval) (e : IssuedBond U) : ℝ :=
  (percolation d p).real (latticeBoundaryConnectionEvent U ((issuedNetwork U).tail e) (negativeFace U i)) *
    (percolation d p).real (latticeBoundaryConnectionEvent U ((issuedNetwork U).head e) (positiveFace U i)) +
  (percolation d p).real (latticeBoundaryConnectionEvent U ((issuedNetwork U).tail e) (positiveFace U i)) *
    (percolation d p).real (latticeBoundaryConnectionEvent U ((issuedNetwork U).head e) (negativeFace U i))

lemma sourceTwoArm_sum_le_connectionProducts {d : ℕ} (U : Finset (Vertex d)) (i : Fin d)
    (p : unitInterval) :
    (∑ e : IssuedBond U, (percolation d p).real {ω | sourceTwoArm U i ω e}) ≤
      ∑ e : IssuedBond U, boundaryConnectionProducts U i p e := by
  exact Finset.sum_le_sum fun e _ ↦ sourceTwoArm_probability_le U i p e

/-- Source eq.aa_bound_step1 through the BK step, retaining both orientations
explicitly rather than presuming a reflection/edge-counting identification. -/
theorem annealedRelaxed_le_connectionProducts {d : ℕ} (U : Finset (Vertex d)) (i : Fin d)
    {l h : DomainVertex U} (hl : l ∈ negativeFace U i) (hh : h ∈ positiveFace U i)
    (p : unitInterval) :
    annealedRelaxed U i (p : ℝ) ≤ ((coordinateData i h - coordinateData i l) ^ 2 / (U.card : ℝ)) *
      ∑ e : IssuedBond U, boundaryConnectionProducts U i p e := by
  exact (annealedRelaxed_le_sourceTwoArm_probabilities U i hl hh p).trans
    (mul_le_mul_of_nonneg_left (sourceTwoArm_sum_le_connectionProducts U i p)
      (div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)))

/-- The analogous exact reduction for the auxiliary term in the differential inequality. -/
theorem annealedB_le_connectionProducts {d : ℕ} (U : Finset (Vertex d)) (i : Fin d)
    {l h : DomainVertex U} (hl : l ∈ negativeFace U i) (hh : h ∈ positiveFace U i)
    (p : unitInterval) :
    annealedB U i (p : ℝ) ≤ ((coordinateData i h - coordinateData i l) ^ 2 / (U.card : ℝ)) *
      ∑ e : IssuedBond U, boundaryConnectionProducts U i p e := by
  exact (annealedB_le_sourceTwoArm_probabilities U i hl hh p).trans
    (mul_le_mul_of_nonneg_left (sourceTwoArm_sum_le_connectionProducts U i p)
      (div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)))

end NearCritical
