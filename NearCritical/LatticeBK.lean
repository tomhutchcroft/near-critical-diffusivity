module

public import NearCritical.CylinderBK
public import NearCritical.LatticePivotal

/-! All-parameter BK estimates for the source finite-domain connection and
two-arm events under the actual infinite lattice percolation law. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Set MeasureTheory ProbabilityTheory

/-- Opposite-face finite-domain connections satisfy BK at every Bernoulli p. -/
theorem lattice_boundary_connections_bk {d : ℕ} (U : Finset (Vertex d))
    (p : unitInterval) (x y : DomainVertex U) (A B : Set (DomainVertex U)) :
    (percolation d p).real {ω | DisjointOccurrence
      (latticeBoundaryConnectionEvent U x A) (latticeBoundaryConnectionEvent U y B) ω} ≤
      (percolation d p).real (latticeBoundaryConnectionEvent U x A) *
      (percolation d p).real (latticeBoundaryConnectionEvent U y B) :=
  percolation_cylinder_bk d p (issuedBondSet U)
    ((issuedNetwork U).boundaryConnectionEvent x A) ((issuedNetwork U).boundaryConnectionEvent y B)
    ((issuedNetwork U).boundaryConnectionEvent_increasing x A)
    ((issuedNetwork U).boundaryConnectionEvent_increasing y B)

/-- The source two-arm probability is bounded by the two products of ordinary
connection probabilities. The tested edge is not required to be open. -/
theorem sourceTwoArm_probability_le {d : ℕ} (U : Finset (Vertex d)) (i : Fin d)
    (p : unitInterval) (e : IssuedBond U) :
    (percolation d p).real {ω | sourceTwoArm U i ω e} ≤
      (percolation d p).real (latticeBoundaryConnectionEvent U ((issuedNetwork U).tail e) (negativeFace U i)) *
        (percolation d p).real (latticeBoundaryConnectionEvent U ((issuedNetwork U).head e) (positiveFace U i)) +
      (percolation d p).real (latticeBoundaryConnectionEvent U ((issuedNetwork U).tail e) (positiveFace U i)) *
        (percolation d p).real (latticeBoundaryConnectionEvent U ((issuedNetwork U).head e) (negativeFace U i)) := by
  let A : Set (Configuration d) := {ω | DisjointOccurrence
    (latticeBoundaryConnectionEvent U ((issuedNetwork U).tail e) (negativeFace U i))
    (latticeBoundaryConnectionEvent U ((issuedNetwork U).head e) (positiveFace U i)) ω}
  let B : Set (Configuration d) := {ω | DisjointOccurrence
    (latticeBoundaryConnectionEvent U ((issuedNetwork U).tail e) (positiveFace U i))
    (latticeBoundaryConnectionEvent U ((issuedNetwork U).head e) (negativeFace U i)) ω}
  have heq : {ω | sourceTwoArm U i ω e} = A ∪ B := rfl
  rw [heq]
  exact (measureReal_union_le A B).trans (add_le_add
    (lattice_boundary_connections_bk U p _ _ _ _) (lattice_boundary_connections_bk U p _ _ _ _))

end NearCritical
