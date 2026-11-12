module

public import NearCritical.Section9CoalescenceSharedLeft
public import NearCritical.Section9RestrictedTripodProbability

@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory
open scoped Classical BigOperators

/-- A marked pivotal event has disjoint certificates for its two left
connections together and its right arm. -/
theorem section9_marked_pivotal_occurrence {d : ℕ} (ω : Configuration d)
    (L R Q₁ F₁ Q₃ F₃ A B : Finset (Vertex d)) (e : Vertex d × Vertex d) (w : Vertex d)
    (he : sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ A B e)
    (hw : w ∈ sprinklingUnexploredCluster ω L Q₁ F₁ e.1) :
    DisjointOccurrence
      (connectionToSetEvent (L : Set (Vertex d)) e.1 {w} ∩
        connectionToSetEvent (L : Set (Vertex d)) e.1 (A : Set (Vertex d)))
      (connectionToSetEvent (R : Set (Vertex d)) e.2 (B : Set (Vertex d))) ω := by
  obtain ⟨x, hx⟩ := he.2.2.2.1
  obtain ⟨hxC, hxA⟩ := Finset.mem_inter.mp hx
  obtain ⟨z, hz⟩ := he.2.2.2.2.1
  obtain ⟨hzC, hzB⟩ := Finset.mem_inter.mp hz
  obtain ⟨S, hSo, hSb, hSf⟩ := sprinklingComponent_connection_certificate ω L Q₁ F₁ he.2.1
    ((mem_sprinklingUnexploredCluster ω L Q₁ F₁ e.1 w).mp hw).2
  obtain ⟨U, hUo, hUb, hUf⟩ := sprinklingComponent_connection_certificate ω L Q₁ F₁ he.2.1
    ((mem_sprinklingUnexploredCluster ω L Q₁ F₁ e.1 x).mp hxC).2
  obtain ⟨V, hVo, hVb, hVf⟩ := sprinklingComponent_connection_certificate ω R Q₃ F₃ he.2.2.1
    ((mem_sprinklingUnexploredCluster ω R Q₃ F₃ e.2 z).mp hzC).2
  have hLeft : ∀ b ∈ S ∪ U, b.1 ∈ sprinklingUnexploredCluster ω L Q₁ F₁ e.1 := by
    intro b hb
    exact (Finset.mem_union.mp hb).elim (hSb b) (hUb b)
  have hdis := disjoint_bond_certificates_of_disjoint_bases he.2.2.2.2.2 hLeft hVb
  refine ⟨(↑(S ∪ U) : Set (Bond d)), V, (S ∪ U).finite_toSet, V.finite_toSet,
    Set.disjoint_left.mpr (Finset.disjoint_left.mp hdis), ?_, ?_⟩
  · intro θ hθ
    refine ⟨hSf θ (fun b hb => (hθ b (Finset.mem_union_left U hb)).trans (hSo b hb)), ?_⟩
    apply connectionToSetEvent_mono (Set.Subset.refl _)
      (Set.singleton_subset_iff.mpr hxA) e.1
    exact hUf θ (fun b hb => (hθ b (Finset.mem_union_right S hb)).trans (hUo b hb))
  · intro θ hθ
    apply connectionToSetEvent_mono (Set.Subset.refl _)
      (Set.singleton_subset_iff.mpr hzB) e.2
    exact hVf θ (fun b hb => (hθ b hb).trans (hVo b hb))

/-- Finite-domain tree bound for a pivotal event marked by a left-cluster vertex. -/
theorem section9_marked_pivotal_tree_bound {d : ℕ} (p : unitInterval)
    (L R Q₁ F₁ Q₃ F₃ A B : Finset (Vertex d)) (e : Vertex d × Vertex d) (w : Vertex d) :
    let P := fun a b => (percolation d p).real
      (connectionToSetEvent (L : Set (Vertex d)) a {b})
    (percolation d p).real {ω | sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ A B e ∧
      w ∈ sprinklingUnexploredCluster ω L Q₁ F₁ e.1} ≤
      (∑ x ∈ A, ∑ u ∈ L, P e.1 u * (P u w * P x u)) *
        (percolation d p).real
          (connectionToSetEvent (R : Set (Vertex d)) e.2 (B : Set (Vertex d))) := by
  intro P
  let J := connectionToSetEvent (L : Set (Vertex d)) e.1 {w} ∩
    connectionToSetEvent (L : Set (Vertex d)) e.1 (A : Set (Vertex d))
  let K := connectionToSetEvent (R : Set (Vertex d)) e.2 (B : Set (Vertex d))
  have hJ : BK.Increasing J := by
    intro ω η hωη h
    exact ⟨connectionToSetEvent_increasing _ _ _ hωη h.1,
      connectionToSetEvent_increasing _ _ _ hωη h.2⟩
  have hK : BK.Increasing K := connectionToSetEvent_increasing _ _ _
  refine (measureReal_mono (fun ω h =>
    section9_marked_pivotal_occurrence ω L R Q₁ F₁ Q₃ F₃ A B e w h.1 h.2)
    (measure_ne_top _ _)).trans ?_
  exact (percolation_bk d p J K hJ hK).trans
    (mul_le_mul_of_nonneg_right (restricted_joint_connection_probability_le p L A e.1 w)
      measureReal_nonneg)

end NearCritical
