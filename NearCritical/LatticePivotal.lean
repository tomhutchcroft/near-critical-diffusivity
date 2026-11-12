module

public import NearCritical.LatticeDifferential
public import NearCritical.LatticeTwoArm
public import NearCritical.DisjointOccurrence
public import NearCritical.CylinderDisjointOccurrence

/-! Source-level pivotal support: conductivity-changing openings in the
infinite-lattice configuration have the closed-edge and old-configuration
two-arm event from `lem.pivot_trick`. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Set BernoulliCalculus

lemma localTwoArm_restrict_iff {d : ℕ} (U : Finset (Vertex d)) (i : Fin d)
    (ω : Configuration d) (e : IssuedBond U) :
    localTwoArm U i ((issuedBondSet U).restrict ω) e ↔
      latticeTwoArm U i ω ((issuedNetwork U).tail e) ((issuedNetwork U).head e) := by
  have hw : Network.binaryWeights ((issuedBondSet U).restrict ω) = domainWeights (U := U) ω := rfl
  unfold localTwoArm Network.binaryTwoArm latticeTwoArm
  rw [hw]

/-- A finite-domain connection event on the full lattice configuration space.
Connections use E⁺(U) on U⁺, rather than unrestricted lattice paths. -/
def latticeBoundaryConnectionEvent {d : ℕ} (U : Finset (Vertex d))
    (x : DomainVertex U) (A : Set (DomainVertex U)) : Set (Configuration d) :=
  (issuedBondSet U).restrict ⁻¹' (issuedNetwork U).boundaryConnectionEvent x A

/-- Exact source circle-event semantics in the full percolation sample space. -/
lemma localTwoArm_iff_global_disjointOccurrence {d : ℕ} (U : Finset (Vertex d)) (i : Fin d)
    (ω : Configuration d) (e : IssuedBond U) :
    localTwoArm U i ((issuedBondSet U).restrict ω) e ↔
      DisjointOccurrence
        (latticeBoundaryConnectionEvent U ((issuedNetwork U).tail e) (negativeFace U i))
        (latticeBoundaryConnectionEvent U ((issuedNetwork U).head e) (positiveFace U i)) ω ∨
      DisjointOccurrence
        (latticeBoundaryConnectionEvent U ((issuedNetwork U).tail e) (positiveFace U i))
        (latticeBoundaryConnectionEvent U ((issuedNetwork U).head e) (negativeFace U i)) ω := by
  unfold localTwoArm Network.binaryTwoArm
  rw [(issuedNetwork U).disjointBoundaryConnections_iff_disjointOccurrence,
    (issuedNetwork U).disjointBoundaryConnections_iff_disjointOccurrence]
  exact or_congr
    (disjointOccurrence_restrict_iff (issuedBondSet U) _ _ ω)
    (disjointOccurrence_restrict_iff (issuedBondSet U) _ _ ω)

/-- The source two-arm event, expressed directly by circle events on all bonds. -/
def sourceTwoArm {d : ℕ} (U : Finset (Vertex d)) (i : Fin d)
    (ω : Configuration d) (e : IssuedBond U) : Prop :=
  DisjointOccurrence
    (latticeBoundaryConnectionEvent U ((issuedNetwork U).tail e) (negativeFace U i))
    (latticeBoundaryConnectionEvent U ((issuedNetwork U).head e) (positiveFace U i)) ω ∨
  DisjointOccurrence
    (latticeBoundaryConnectionEvent U ((issuedNetwork U).tail e) (positiveFace U i))
    (latticeBoundaryConnectionEvent U ((issuedNetwork U).head e) (negativeFace U i)) ω

lemma localTwoArm_iff_sourceTwoArm {d : ℕ} (U : Finset (Vertex d)) (i : Fin d)
    (ω : Configuration d) (e : IssuedBond U) :
    localTwoArm U i ((issuedBondSet U).restrict ω) e ↔ sourceTwoArm U i ω e :=
  localTwoArm_iff_global_disjointOccurrence U i ω e

/-- `lem.pivot_trick`, with all events in the ORIGINAL percolation configuration. -/
theorem lattice_pivotal_support {d : ℕ} {U : Finset (Vertex d)} (hU : U.Nonempty) (i : Fin d)
    (ω : Configuration d) (e : IssuedBond U)
    (hchange : relaxedConductivity U i (Function.update ω e.val true) ≠ relaxedConductivity U i ω) :
    ω e.val = false ∧ latticeTwoArm U i ω ((issuedNetwork U).tail e) ((issuedNetwork U).head e) := by
  classical
  let η : IssuedBond U → Bool := (issuedBondSet U).restrict ω
  have hη : (issuedNetwork U).binaryConductance (twoFaceBoundary U i) (coordinateData i) (forceOpen e η) ≠
      (issuedNetwork U).binaryConductance (twoFaceBoundary U i) (coordinateData i) η := by
    intro heq
    apply hchange
    have hs := congrArg (fun r : ℝ ↦ r / (U.card : ℝ)) heq
    simp_rw [relaxedConductivity_restrict, restrict_update_bond, localRelaxedConductivity_eq_binary]
    exact hs
  have hclosed := BernoulliCalculus.opening_change_implies_closed e
    ((issuedNetwork U).binaryConductance (twoFaceBoundary U i) (coordinateData i)) η hη
  have htwo := localConductance_pivotal_support hU i η e hη
  refine ⟨?_, (localTwoArm_restrict_iff U i ω e).mp htwo⟩
  exact hclosed

/-- The pivotal-support theorem with the source's disjoint-occurrence operator
on the infinite bond configuration space, not only finite-network certificates. -/
theorem lattice_pivotal_support_disjointOccurrence {d : ℕ} {U : Finset (Vertex d)}
    (hU : U.Nonempty) (i : Fin d) (ω : Configuration d) (e : IssuedBond U)
    (hchange : relaxedConductivity U i (Function.update ω e.val true) ≠ relaxedConductivity U i ω) :
    ω e.val = false ∧
      (DisjointOccurrence
        (latticeBoundaryConnectionEvent U ((issuedNetwork U).tail e) (negativeFace U i))
        (latticeBoundaryConnectionEvent U ((issuedNetwork U).head e) (positiveFace U i)) ω ∨
      DisjointOccurrence
        (latticeBoundaryConnectionEvent U ((issuedNetwork U).tail e) (positiveFace U i))
        (latticeBoundaryConnectionEvent U ((issuedNetwork U).head e) (negativeFace U i)) ω) := by
  obtain ⟨hclosed, htwo⟩ := lattice_pivotal_support hU i ω e hchange
  exact ⟨hclosed, (localTwoArm_iff_global_disjointOccurrence U i ω e).mp
    ((localTwoArm_restrict_iff U i ω e).mpr htwo)⟩

end NearCritical
