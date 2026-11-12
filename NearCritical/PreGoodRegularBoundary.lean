module

public import NearCritical.NestRegularBoundary
public import NearCritical.PreGoodRegularityLoss

/-! Literal regularity marks and source pre-good Step2, with internal support
and measurability derived. The NEW regularity first moment remains open. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Finset Set MeasureTheory
open scoped Classical

/-- Actual irregular points on a chosen counting boundary. The ERE2 test still
uses the FULL cubeBoundary; markBoundary may be a truncated face or their union. -/
def irregularBoundaryVertices {d : ℕ} (ω : Configuration d)
    (Q heart excluded cubeBoundary markBoundary : Finset (Vertex d)) (r : ℕ) (δ : ℝ) : Finset (Vertex d) :=
  (heartClusterUnion ω Q heart ∩ markBoundary).filter
    (fun x => ¬sourceRegularPoint (heartClusterUnion ω Q heart) excluded cubeBoundary r δ x)

lemma irregularBoundaryVertices_subset {d : ℕ} (ω : Configuration d)
    (Q heart excluded cubeBoundary markBoundary : Finset (Vertex d)) (r : ℕ) (δ : ℝ) :
    irregularBoundaryVertices ω Q heart excluded cubeBoundary markBoundary r δ ⊆ Q := by
  intro x hx
  exact heartClusterUnion_subset ω Q heart (Finset.mem_inter.mp (Finset.mem_filter.mp hx).1).1

/-- Full-union regularity marks have actual finite internal support. -/
lemma irregularBoundaryVertices_reconstruct {d : ℕ} (ω : Configuration d)
    (Q heart excluded cubeBoundary markBoundary : Finset (Vertex d)) (r : ℕ) (δ : ℝ) :
    irregularBoundaryVertices ω Q heart excluded cubeBoundary markBoundary r δ =
      irregularBoundaryVertices (reconstructInterior Q ((internalBondSet Q).restrict ω))
        Q heart excluded cubeBoundary markBoundary r δ := by
  have h := heartClusterUnion_eq_of_internal_agree Q Q heart (fun _ hx => hx)
    ω _ (reconstructInterior_restrict_agree Q ω)
  simp only [irregularBoundaryVertices,h]

/-- No regularity measurability premise: the literal ERE tests are finite
functions of a finite internal restriction. -/
theorem measurableSet_irregularBoundary_member {d : ℕ}
    (Q heart excluded cubeBoundary markBoundary : Finset (Vertex d)) (r : ℕ) (δ : ℝ) (x : Vertex d) :
    MeasurableSet {ω | x ∈ irregularBoundaryVertices ω Q heart excluded cubeBoundary markBoundary r δ} := by
  have he : {ω : Configuration d | x ∈ irregularBoundaryVertices ω Q heart excluded cubeBoundary markBoundary r δ} =
      (internalBondSet Q).restrict ⁻¹'
        {η | x ∈ irregularBoundaryVertices (reconstructInterior Q η) Q heart excluded cubeBoundary markBoundary r δ} := by
    ext ω
    exact congrArg (fun B : Finset (Vertex d) => x ∈ B)
      (irregularBoundaryVertices_reconstruct ω Q heart excluded cubeBoundary markBoundary r δ) |>.to_iff
  rw [he]
  exact (Finset.measurable_restrict _) (Set.toFinite _).measurableSet

/-- Every irregular point of a candidate component on a source patch belongs
to the literal marked set, if the component lies in the heart-cluster union. -/
lemma irregularBoundary_patch_cover {d : ℕ} (ω : Configuration d)
    (Q heart excluded cubeBoundary markBoundary patch C : Finset (Vertex d)) (r : ℕ) (δ : ℝ)
    (hC : C ⊆ heartClusterUnion ω Q heart) (hpatch : patch ⊆ markBoundary) :
    (C ∩ patch).filter (fun x => ¬sourceRegularPoint
      (heartClusterUnion ω Q heart) excluded cubeBoundary r δ x) ⊆
      irregularBoundaryVertices ω Q heart excluded cubeBoundary markBoundary r δ := by
  intro x hx
  obtain ⟨hxCP,hbad⟩ := Finset.mem_filter.mp hx
  obtain ⟨hxC,hxp⟩ := Finset.mem_inter.mp hxCP
  exact Finset.mem_filter.mpr ⟨Finset.mem_inter.mpr ⟨hC hxC,hpatch hxp⟩,hbad⟩

/-- Heart-touching of an ACTUAL candidate component supplies union membership;
no component-to-mark coverage conclusion is assumed. -/
lemma component_subset_heartUnion_of_meets {d : ℕ} (ω : Configuration d)
    (Q heart C : Finset (Vertex d)) (hC : C ∈ finiteClusterFamily ω Q)
    (hmeet : (C ∩ heart).Nonempty) : C ⊆ heartClusterUnion ω Q heart := by
  obtain ⟨root,hroot⟩ := hmeet
  obtain ⟨hrC,hrH⟩ := Finset.mem_inter.mp hroot
  have he := finiteClusterFamily_recover ω Q hC hrC
  rw [← he]
  exact cluster_subset_heartClusterUnion ω Q heart hrH

/-- Actual ERE regularity-loss rate. Abstract marked-set support, membership
measurability and coverage have all been discharged. hmoment is precisely the
remaining NEW point first-moment obligation, not a loss-probability premise. -/
theorem literal_regularity_loss_source_bound {d : ℕ} {φ : Type*} (p : unitInterval)
    (Q heart excluded cubeBoundary markBoundary : Finset (Vertex d)) (r : ℕ) (δ : ℝ)
    (P : Configuration d → Finset (Vertex d) → Prop) (patch : φ → Finset (Vertex d))
    (hpatch_mark : ∀ i, patch i ⊆ markBoundary)
    (hmeet : ∀ ω C, C ∈ filteredClusterFamily ω Q (P ω) → (C ∩ heart).Nonempty)
    (n : ℕ) (hn : 1 ≤ n) (hd : 6 ≤ d) {c c1 ε' : ℝ} (hc : 0 < c) (hc1 : 0 < c1)
    (hpatch : ∀ ω C, C ∈ filteredClusterFamily ω Q (P ω) → ∀ i,
      c*(n:ℝ)^2 ≤ ((C ∩ patch i).card:ℝ))
    (hmoment : (∑ x ∈ Q, (percolation d p).real
      {ω | x ∈ irregularBoundaryVertices ω Q heart excluded cubeBoundary markBoundary r δ}) ≤
      2*(d:ℝ)*ε'*(n:ℝ)^(d-4)) :
    (percolation d p).real {ω | (c1/2)*(n:ℝ)^(d-6) ≤
      ((filteredClusterFamily ω Q (regularityBadCluster (P ω) patch
        (sourceRegularPoint (heartClusterUnion ω Q heart) excluded cubeBoundary r δ)
        ((c/2)*(n:ℝ)^2))).card:ℝ)} ≤ 8*(d:ℝ)*ε'/(c*c1) := by
  apply regularity_loss_source_bound p Q
    (fun ω => irregularBoundaryVertices ω Q heart excluded cubeBoundary markBoundary r δ)
    (fun ω => irregularBoundaryVertices_subset ω Q heart excluded cubeBoundary markBoundary r δ)
    (fun x _hx => measurableSet_irregularBoundary_member Q heart excluded cubeBoundary markBoundary r δ x)
    P patch (fun ω => sourceRegularPoint (heartClusterUnion ω Q heart) excluded cubeBoundary r δ)
    n hn hd hc hc1 hpatch
  · intro ω C hC i
    exact irregularBoundary_patch_cover ω Q heart excluded cubeBoundary markBoundary (patch i) C r δ
      (component_subset_heartUnion_of_meets ω Q heart C (Finset.mem_filter.mp hC).1
        (hmeet ω C hC)) (hpatch_mark i)
  · exact hmoment

end NearCritical
