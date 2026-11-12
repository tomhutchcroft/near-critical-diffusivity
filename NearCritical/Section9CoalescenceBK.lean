module

public import NearCritical.Section9CoalescenceConnection
public import NearCritical.Section8DiagramBK

@[expose] public section
namespace NearCritical
open scoped Classical

/-- In the shared-right case, the two left connections and the joint
right connection have three disjoint finite forcing witnesses. -/
theorem section9_shared_right_disjointOccurrence {d : ℕ} (ω : Configuration d)
    (L R Q₁ F₁ Q₃ F₃ B : Finset (Vertex d)) (x y : Vertex d)
    (e f : Vertex d × Vertex d)
    (he : sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ {x} B e)
    (hf : sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ {y} B f)
    (hLL : Disjoint (sprinklingUnexploredCluster ω L Q₁ F₁ e.1)
      (sprinklingUnexploredCluster ω L Q₁ F₁ f.1))
    (hshared : sprinklingUnexploredCluster ω R Q₃ F₃ e.2 =
      sprinklingUnexploredCluster ω R Q₃ F₃ f.2) :
    DisjointOccurrence (connectionToSetEvent (L : Set (Vertex d)) e.1 {x})
      {θ | DisjointOccurrence (connectionToSetEvent (L : Set (Vertex d)) f.1 {y})
        (connectionToSetEvent (R : Set (Vertex d)) e.2 {f.2} ∩
          connectionToSetEvent (R : Set (Vertex d)) e.2 (B : Set (Vertex d))) θ} ω := by
  obtain ⟨z, hz, hef, hez⟩ :=
    section9_shared_right_three_terminals ω L R Q₁ F₁ Q₃ F₃ {x} B e f he hf.2.2.1 hshared
  have leftReach (v : Vertex d) (a : Vertex d × Vertex d)
      (h : sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ {v} B a) :
      (sprinklingUnexploredGraph ω L Q₁ F₁).Reachable a.1 v := by
    obtain ⟨w, hw⟩ := h.2.2.2.1
    obtain ⟨hwC, hwv⟩ := Finset.mem_inter.mp hw
    have hwEq := Finset.mem_singleton.mp hwv
    subst w
    exact ((mem_sprinklingUnexploredCluster ω L Q₁ F₁ a.1 v).mp hwC).2
  obtain ⟨S, hSo, hSb, hSf⟩ :=
    sprinklingComponent_connection_certificate ω L Q₁ F₁ he.2.1 (leftReach x e he)
  obtain ⟨U, hUo, hUb, hUf⟩ :=
    sprinklingComponent_connection_certificate ω L Q₁ F₁ hf.2.1 (leftReach y f hf)
  obtain ⟨V, hVo, hVb, hVf⟩ :=
    sprinklingComponent_connection_certificate ω R Q₃ F₃ he.2.2.1 hef
  obtain ⟨W, hWo, hWb, hWf⟩ :=
    sprinklingComponent_connection_certificate ω R Q₃ F₃ he.2.2.1 hez
  have hRight : ∀ b ∈ V ∪ W, b.1 ∈ sprinklingUnexploredCluster ω R Q₃ F₃ e.2 := by
    intro b hb
    exact (Finset.mem_union.mp hb).elim (hVb b) (hWb b)
  have hUR : Disjoint (sprinklingUnexploredCluster ω L Q₁ F₁ f.1)
      (sprinklingUnexploredCluster ω R Q₃ F₃ e.2) := by
    rw [hshared]
    exact hf.2.2.2.2.2
  have hSU := disjoint_bond_certificates_of_disjoint_bases hLL hSb hUb
  have hSR := disjoint_bond_certificates_of_disjoint_bases he.2.2.2.2.2 hSb hRight
  have hUR' := disjoint_bond_certificates_of_disjoint_bases hUR hUb hRight
  refine ⟨S, (U : Set (Bond d)) ∪ (↑(V ∪ W) : Set (Bond d)), S.finite_toSet,
    U.finite_toSet.union (V ∪ W).finite_toSet, ?_, ?_, ?_⟩
  · apply Set.disjoint_left.mpr
    intro b hbS hb
    exact hb.elim (Finset.disjoint_left.mp hSU hbS) (Finset.disjoint_left.mp hSR hbS)
  · intro θ hθ
    exact hSf θ (fun b hb => (hθ b hb).trans (hSo b hb))
  · apply Section8.forcesOn_disjointOccurrence_union U.finite_toSet (V ∪ W).finite_toSet
    · exact Set.disjoint_left.mpr (Finset.disjoint_left.mp hUR')
    · intro θ hθ
      exact hUf θ (fun b hb => (hθ b hb).trans (hUo b hb))
    · intro θ hθ
      refine ⟨hVf θ (fun b hb => (hθ b (Finset.mem_union_left W hb)).trans (hVo b hb)), ?_⟩
      apply connectionToSetEvent_mono (Set.Subset.refl _)
        (Set.singleton_subset_iff.mpr hz) e.2
      exact hWf θ (fun b hb => (hθ b (Finset.mem_union_right V hb)).trans (hWo b hb))

end NearCritical
