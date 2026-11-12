module

public import NearCritical.Section9CoalescenceConnection
public import NearCritical.Section9RestrictedTripodProbability

@[expose] public section
namespace NearCritical
open MeasureTheory
open scoped Classical

/-- Case 1 supplies three terminals in the deleted left graph. The pivot
and the two roots are joined before the independent opening is sampled. -/
theorem section9_shared_left_three_terminals {d : ℕ} (ω : Configuration d)
    (L R Q₁ F₁ Q₃ F₃ B : Finset (Vertex d)) (x y : Vertex d)
    (e : Vertex d × Vertex d)
    (he : sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ {x} B e)
    (hxy : (sprinklingUnexploredCluster ω L Q₁ F₁ x ∩
      sprinklingUnexploredCluster ω L Q₁ F₁ y).Nonempty) :
    (sprinklingUnexploredGraph ω L Q₁ F₁).Reachable x y ∧
      (sprinklingUnexploredGraph ω L Q₁ F₁).Reachable x e.1 := by
  obtain ⟨v, hv⟩ := hxy
  obtain ⟨hvx, hvy⟩ := Finset.mem_inter.mp hv
  have hxv := ((mem_sprinklingUnexploredCluster ω L Q₁ F₁ x v).mp hvx).2
  have hyv := ((mem_sprinklingUnexploredCluster ω L Q₁ F₁ y v).mp hvy).2
  obtain ⟨w, hw⟩ := he.2.2.2.1
  obtain ⟨hwe, hwx⟩ := Finset.mem_inter.mp hw
  have hwEq := Finset.mem_singleton.mp hwx
  subst w
  exact ⟨hxv.trans hyv.symm,
    ((mem_sprinklingUnexploredCluster ω L Q₁ F₁ e.1 x).mp hwe).2.symm⟩

/-- The common left component and the target-side arm have disjoint
certificates for an ordinary joint connection and an ordinary arm. -/
theorem section9_shared_left_disjointOccurrence {d : ℕ} (ω : Configuration d)
    (L R Q₁ F₁ Q₃ F₃ B : Finset (Vertex d)) (x y : Vertex d)
    (e : Vertex d × Vertex d)
    (he : sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ {x} B e)
    (hxy : (sprinklingUnexploredCluster ω L Q₁ F₁ x ∩
      sprinklingUnexploredCluster ω L Q₁ F₁ y).Nonempty) :
    DisjointOccurrence
      (connectionToSetEvent (L : Set (Vertex d)) e.1 {x} ∩
        connectionToSetEvent (L : Set (Vertex d)) e.1 {y})
      (connectionToSetEvent (R : Set (Vertex d)) e.2 (B : Set (Vertex d))) ω := by
  obtain ⟨hxy', hxe⟩ := section9_shared_left_three_terminals ω L R Q₁ F₁ Q₃ F₃ B x y e he hxy
  obtain ⟨z, hz⟩ := he.2.2.2.2.1
  obtain ⟨hzC, hzB⟩ := Finset.mem_inter.mp hz
  have hez := ((mem_sprinklingUnexploredCluster ω R Q₃ F₃ e.2 z).mp hzC).2
  obtain ⟨S, hSo, hSb, hSf⟩ :=
    sprinklingComponent_connection_certificate ω L Q₁ F₁ he.2.1 hxe.symm
  obtain ⟨U, hUo, hUb, hUf⟩ :=
    sprinklingComponent_connection_certificate ω L Q₁ F₁ he.2.1 (hxe.symm.trans hxy')
  obtain ⟨V, hVo, hVb, hVf⟩ :=
    sprinklingComponent_connection_certificate ω R Q₃ F₃ he.2.2.1 hez
  have hLeft : ∀ b ∈ S ∪ U, b.1 ∈ sprinklingUnexploredCluster ω L Q₁ F₁ e.1 := by
    intro b hb
    exact (Finset.mem_union.mp hb).elim (hSb b) (hUb b)
  have hdis := disjoint_bond_certificates_of_disjoint_bases he.2.2.2.2.2 hLeft hVb
  refine ⟨(↑(S ∪ U) : Set (Bond d)), V, (S ∪ U).finite_toSet, V.finite_toSet,
    Set.disjoint_left.mpr (Finset.disjoint_left.mp hdis), ?_, ?_⟩
  · intro θ hθ
    exact ⟨hSf θ (fun b hb => (hθ b (Finset.mem_union_left U hb)).trans (hSo b hb)),
      hUf θ (fun b hb => (hθ b (Finset.mem_union_right S hb)).trans (hUo b hb))⟩
  · intro θ hθ
    apply connectionToSetEvent_mono (Set.Subset.refl _)
      (Set.singleton_subset_iff.mpr hzB) e.2
    exact hVf θ (fun b hb => (hθ b hb).trans (hVo b hb))

/-- The Case 1 probability is bounded by the finite left tripod diagram
times the right-arm probability, using BK under the same law. -/
theorem section9_shared_left_probability_le {d : ℕ} (p : unitInterval)
    (L R Q₁ F₁ Q₃ F₃ B : Finset (Vertex d)) (x y : Vertex d)
    (e : Vertex d × Vertex d) :
    let P := fun a b => (percolation d p).real (connectionToSetEvent (L : Set (Vertex d)) a {b})
    (percolation d p).real {ω |
      sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ {x} B e ∧
      (sprinklingUnexploredCluster ω L Q₁ F₁ x ∩
        sprinklingUnexploredCluster ω L Q₁ F₁ y).Nonempty} ≤
      (∑ u ∈ L, P e.1 u * (P u x * P y u)) *
        (percolation d p).real (connectionToSetEvent (R : Set (Vertex d)) e.2 (B : Set (Vertex d))) := by
  dsimp only
  let A := connectionToSetEvent (L : Set (Vertex d)) e.1 {x}
  let C := connectionToSetEvent (L : Set (Vertex d)) e.1 {y}
  let D := connectionToSetEvent (R : Set (Vertex d)) e.2 (B : Set (Vertex d))
  have hAC : BK.Increasing (A ∩ C) := by
    intro ω θ h hω
    exact ⟨connectionToSetEvent_increasing _ _ _ h hω.1,
      connectionToSetEvent_increasing _ _ _ h hω.2⟩
  have hD : BK.Increasing D := connectionToSetEvent_increasing _ _ _
  calc
    _ ≤ (percolation d p).real {ω | DisjointOccurrence (A ∩ C) D ω} :=
      measureReal_mono (fun ω h =>
        section9_shared_left_disjointOccurrence ω L R Q₁ F₁ Q₃ F₃ B x y e h.1 h.2)
    _ ≤ (percolation d p).real (A ∩ C) * (percolation d p).real D :=
      percolation_bk d p (A ∩ C) D hAC hD
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ measureReal_nonneg
      simpa only [A, C, Finset.coe_singleton, Finset.sum_singleton] using
        restricted_joint_connection_probability_le p L {y} e.1 x

end NearCritical
