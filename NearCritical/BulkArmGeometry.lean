module

public import NearCritical.BulkDomain
public import NearCritical.ConnectionToSet

/-! The paper's bulk separation turns both source arms into ordinary extrinsic
arms. Distance is the actual sup metric on Fin d → integers, as in BulkDomain.
The original finite disjoint open certificates force the new arms under every
outside assignment; no BK estimate or tested-edge openness is assumed. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Set
open scoped Classical

/-- Ordinary extrinsic arm beyond radius r in the FULL open lattice graph.
The metric on Vertex d is the finite-product sup metric, not the Euclidean norm. -/
def extrinsicRadiusArmEvent {d : ℕ} (x : Vertex d) (r : ℝ) : Set (Configuration d) :=
  {ω | ∃ y : Vertex d, r < dist x y ∧ (openGraph ω).Reachable x y}

lemma measurableSet_extrinsicRadiusArmEvent {d : ℕ} (x : Vertex d) (r : ℝ) :
    MeasurableSet (extrinsicRadiusArmEvent x r) := by
  have heq : extrinsicRadiusArmEvent x r =
      ⋃ y : Vertex d, {ω : Configuration d | r < dist x y} ∩ connectionEvent x y := by
    ext ω
    simp [extrinsicRadiusArmEvent, connectionEvent]
  rw [heq]
  exact MeasurableSet.iUnion (fun y ↦ (MeasurableSet.const _).inter
    (measurableSet_connectionEvent x y))

lemma extrinsicRadiusArmEvent_increasing {d : ℕ} (x : Vertex d) (r : ℝ) :
    BK.Increasing (extrinsicRadiusArmEvent x r) := by
  rintro ω η h ⟨y, hry, hp⟩
  exact ⟨y, hry, SimpleGraph.Reachable.mono (openGraph_mono h) hp⟩

/-- Every point of EITHER source face is farther than delta*h/2 from any bulk
vertex. This is the actual infimum-distance definition, not a coordinate proxy. -/
lemma bulkVertex_dist_twoFace_gt {d : ℕ} (U : Finset (Vertex d)) (i : Fin d)
    (height δ : ℝ) {x : Vertex d} (hx : x ∈ bulkVertices U i height δ)
    {y : DomainVertex U} (hy : y ∈ twoFaceBoundary U i) :
    δ * height / 2 < dist x y.val := by
  have hr := ((mem_bulkVertices U i height δ x).mp hx).2
  exact hr.trans_le (Metric.infDist_le_dist_of_mem (s := Subtype.val '' twoFaceBoundary U i)
    ⟨y, hy, rfl⟩)

/-- A finite issued-domain path to a source face is an ordinary full-lattice
arm from a bulk vertex. The graph embedding is used in the inclusion direction. -/
theorem latticeBoundaryConnectionEvent_subset_extrinsicRadiusArm {d : ℕ}
    (U : Finset (Vertex d)) (i : Fin d) (height δ : ℝ)
    (x : DomainVertex U) (hx : x.val ∈ bulkVertices U i height δ)
    (A : Set (DomainVertex U)) (hA : A ⊆ twoFaceBoundary U i) :
    latticeBoundaryConnectionEvent U x A ⊆ extrinsicRadiusArmEvent x.val (δ * height / 2) := by
  intro ω hω
  obtain ⟨_, y, hy, _, hp⟩ := latticeBoundaryConnectionEvent_subset U x A hω
  obtain ⟨z, hz, rfl⟩ := hy
  refine ⟨z.val, bulkVertex_dist_twoFace_gt U i height δ hx (hA hz), ?_⟩
  have hle : restrictedGraph ω (sitesPlus U : Set (Vertex d)) ≤ openGraph ω :=
    fun _ _ h ↦ h.1
  exact SimpleGraph.Reachable.mono hle hp

/-- Both source orientations yield the SAME ordered pair of ordinary arms,
from tail and head respectively. The tested bond need not be open. -/
theorem sourceTwoArm_bulk_subset_disjoint_extrinsicArms {d : ℕ}
    (U : Finset (Vertex d)) (i : Fin d) (height δ : ℝ)
    (e : IssuedBond U) (he : e ∈ bulkBondMask U i height δ) :
    {ω | sourceTwoArm U i ω e} ⊆
      {ω | DisjointOccurrence
        (extrinsicRadiusArmEvent ((issuedNetwork U).tail e).val (δ * height / 2))
        (extrinsicRadiusArmEvent ((issuedNetwork U).head e).val (δ * height / 2)) ω} := by
  have hx : ((issuedNetwork U).tail e).val ∈ bulkVertices U i height δ :=
    ((mem_bulkBondMask U i height δ e).mp he).1
  have hy : ((issuedNetwork U).head e).val ∈ bulkVertices U i height δ :=
    ((mem_bulkBondMask U i height δ e).mp he).2
  have hneg : negativeFace U i ⊆ twoFaceBoundary U i := by
    rw [twoFaceBoundary_eq_union]
    exact Set.subset_union_left
  have hpos : positiveFace U i ⊆ twoFaceBoundary U i := by
    rw [twoFaceBoundary_eq_union]
    exact Set.subset_union_right
  rintro ω (hω | hω)
  · exact BK.disjointOccurrence_mono
      (latticeBoundaryConnectionEvent_subset_extrinsicRadiusArm U i height δ _ hx _ hneg)
      (latticeBoundaryConnectionEvent_subset_extrinsicRadiusArm U i height δ _ hy _ hpos) hω
  · exact BK.disjointOccurrence_mono
      (latticeBoundaryConnectionEvent_subset_extrinsicRadiusArm U i height δ _ hx _ hpos)
      (latticeBoundaryConnectionEvent_subset_extrinsicRadiusArm U i height δ _ hy _ hneg) hω

/-- Explicit positive finite certificates for the two ordinary arms. For ANY
configuration theta opening F (respectively H), the corresponding arm survives,
with no constraint on any other bit. F,H are disjoint and open in the OLD omega. -/
theorem sourceTwoArm_bulk_open_forcing {d : ℕ}
    (U : Finset (Vertex d)) (i : Fin d) (height δ : ℝ)
    (e : IssuedBond U) (he : e ∈ bulkBondMask U i height δ)
    {ω : Configuration d} (hω : sourceTwoArm U i ω e) :
    ∃ F H : Set (Bond d), F.Finite ∧ H.Finite ∧ Disjoint F H ∧
      (∀ f ∈ F, ω f = true) ∧ (∀ f ∈ H, ω f = true) ∧
      (∀ θ : Configuration d, (∀ f ∈ F, θ f = true) →
        θ ∈ extrinsicRadiusArmEvent ((issuedNetwork U).tail e).val (δ * height / 2)) ∧
      (∀ θ : Configuration d, (∀ f ∈ H, θ f = true) →
        θ ∈ extrinsicRadiusArmEvent ((issuedNetwork U).head e).val (δ * height / 2)) := by
  have h := sourceTwoArm_bulk_subset_disjoint_extrinsicArms U i height δ e he hω
  obtain ⟨F, H, hFfin, hHfin, hdis, hF, hH, hAF, hBH⟩ :=
    BK.openDisjointOccurrence_of_disjointOccurrence h
  refine ⟨F, H, hFfin, hHfin, hdis, hF, hH, ?_, ?_⟩
  · intro θ hθ
    apply extrinsicRadiusArmEvent_increasing _ _ ?_ hAF
    intro f hf
    exact hθ f ((BK.openMask_eq_true F f).mp hf)
  · intro θ hθ
    apply extrinsicRadiusArmEvent_increasing _ _ ?_ hBH
    intro f hf
    exact hθ f ((BK.openMask_eq_true H f).mp hf)

end NearCritical
