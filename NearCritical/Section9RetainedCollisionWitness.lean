module
public import NearCritical.Section9ResamplingMask
public import NearCritical.Section9CoalescenceConnection
public import NearCritical.Section9PivotalSupport
public import NearCritical.Section9MarkedArmOccurrence

/-! First-hit collision witnesses retain disjoint arms without requiring the
replacement configuration to satisfy the nonmonotone pivotal event. -/
@[expose] public section
noncomputable section
namespace NearCritical
open scoped Classical

private theorem walk_transfer_component {V : Type*} (G H : SimpleGraph V) (root : V)
    (hedge : ∀ a b, G.Reachable root a → G.Adj a b → H.Adj a b)
    {a b : V} (p : G.Walk a b) (ha : G.Reachable root a) :
    ∃ q : H.Walk a b, q.support = p.support := by
  induction p with
  | nil => exact ⟨.nil,rfl⟩
  | @cons a b c hab p ih =>
    obtain ⟨q,hq⟩ := ih (ha.trans hab.reachable)
    exact ⟨q.cons (hedge a b ha hab),by simp only [SimpleGraph.Walk.support_cons,hq]⟩

private theorem walk_first_component_collision {V : Type*} (G H : SimpleGraph V)
    (root : V) (C : Set V)
    (hedge : ∀ a b, a ∉ C → b ∉ C → H.Adj a b → G.Adj a b)
    {a z : V} (p : H.Walk a z) (ha : G.Reachable root a) (haC : a ∉ C) (hz : z ∈ C) :
    ∃ w ∈ C, ∃ q : H.Walk a w,
      ∀ v ∈ q.support, G.Reachable root v ∨ v ∈ C := by
  induction p with
  | nil => exact (haC hz).elim
  | @cons a b z hab p ih =>
    by_cases hb : b ∈ C
    · refine ⟨b,hb,.cons hab .nil,?_⟩
      intro v hv
      simp only [SimpleGraph.Walk.support_cons,SimpleGraph.Walk.support_nil,
        List.mem_cons,List.not_mem_nil,or_false] at hv
      rcases hv with rfl | rfl
      · exact Or.inl ha
      · exact Or.inr hb
    · obtain ⟨w,hw,q,hq⟩ := ih (ha.trans (hedge a b haC hb hab).reachable) hb hz
      refine ⟨w,hw,q.cons hab,?_⟩
      intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact Or.inl ha
      · exact hq v hv

private theorem deleted_walk_supported_certificate {d : ℕ} (ω : Configuration d)
    (T Q F : Finset (Vertex d)) {a b : Vertex d}
    (p : (sprinklingUnexploredGraph ω T Q F).Walk a b) (ha : a ∈ T)
    (V : Finset (Vertex d)) (hsupport : ∀ v ∈ p.support, v ∈ V) :
    ∃ P : Finset (Bond d), (∀ e ∈ P, ω e = true) ∧
      (∀ e ∈ P, e.1 ∈ V) ∧
      ∀ θ : Configuration d, (∀ e ∈ P, θ e = true) →
        connectionToSetEvent (T : Set (Vertex d)) a {b} θ := by
  let q := p.mapLe (microscopicPieceGraph_le ω _ _)
  have hq : q.support = p.support := SimpleGraph.Walk.support_mapLe_eq_support _ _
  obtain ⟨P,hopen,hedge,hforce⟩ := openWalk_certificate q (T : Set (Vertex d))
    (fun v hv => microscopicWalk_support p ha v (hq ▸ hv))
  exact ⟨P,hopen,(fun e he => hsupport e.1 (hq ▸ q.fst_mem_support_of_mem_edges (hedge e he))),hforce⟩

/-- An old pivotal pair whose components avoid C, followed by a replacement
left-component hit of C, supplies a first-hit marked left arm jointly disjoint
from the retained right arm. The conclusion imposes no new pivotal event. -/
theorem section9_retained_left_collision_witness {d : ℕ}
    (S : Finset (Bond d)) (C L R Q₁ F₁ Q₃ F₃ A B : Finset (Vertex d))
    (htouch : ∀ b ∈ S, b.1 ∈ C ∨ bondTip b ∈ C)
    (ω ζ : Configuration d) (f : Vertex d × Vertex d)
    (hpivot : sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ A B f)
    (hleft : Disjoint (sprinklingUnexploredCluster ω L Q₁ F₁ f.1) C)
    (hright : Disjoint (sprinklingUnexploredCluster ω R Q₃ F₃ f.2) C)
    (hhit : (sprinklingUnexploredCluster (resampleBonds S ω ζ) L Q₁ F₁ f.1 ∩ C).Nonempty) :
    let U := sprinklingAvailableBonds L Q₁ F₁ ∪ sprinklingAvailableBonds R Q₃ F₃
    let η := extendConfiguration U (fun _ => false) (U.restrict (resampleBonds S ω ζ))
    ∃ w ∈ C, DisjointOccurrence
      (connectionToSetEvent (L : Set (Vertex d)) f.1 {w} ∩
        connectionToSetEvent (L : Set (Vertex d)) f.1 (A : Set (Vertex d)))
      (connectionToSetEvent (R : Set (Vertex d)) f.2 (B : Set (Vertex d))) η := by
  intro U η
  let CL := sprinklingUnexploredCluster ω L Q₁ F₁ f.1
  let CR := sprinklingUnexploredCluster ω R Q₃ F₃ f.2
  have hmask (T Q F : Finset (Vertex d))
      (hsub : sprinklingAvailableBonds T Q F ⊆ U) :
      sprinklingUnexploredGraph η T Q F =
        sprinklingUnexploredGraph (resampleBonds S ω ζ) T Q F := by
    apply sprinklingUnexploredGraph_eq_of_available_agree
    intro b hb
    dsimp [η]
    simp [extendConfiguration,hsub hb,Finset.restrict]
  have hmaskL := hmask L Q₁ F₁ (Finset.subset_union_left)
  have hmaskR := hmask R Q₃ F₃ (Finset.subset_union_right)
  have haway (T Q F : Finset (Vertex d))
      (heq : sprinklingUnexploredGraph η T Q F =
        sprinklingUnexploredGraph (resampleBonds S ω ζ) T Q F)
      (a b : Vertex d) (ha : a ∉ C) (hb : b ∉ C) :
      (sprinklingUnexploredGraph η T Q F).Adj a b ↔
        (sprinklingUnexploredGraph ω T Q F).Adj a b := by
    rw [heq]
    change ((openGraph (resampleBonds S ω ζ)).Adj a b ∧ a ∈ T ∧ b ∈ T ∧
      s(a,b) ∈ (exploredEdgeSet (Q : Set (Vertex d)) (F : Set (Vertex d)))ᶜ) ↔
      ((openGraph ω).Adj a b ∧ a ∈ T ∧ b ∈ T ∧
      s(a,b) ∈ (exploredEdgeSet (Q : Set (Vertex d)) (F : Set (Vertex d)))ᶜ)
    rw [resampleBonds_open_adj_away S C htouch ω ζ a b ha hb]
  have htransfer (T Q F : Finset (Vertex d)) (root : Vertex d)
      (heq : sprinklingUnexploredGraph η T Q F =
        sprinklingUnexploredGraph (resampleBonds S ω ζ) T Q F)
      (hdis : Disjoint (sprinklingUnexploredCluster ω T Q F root) C) :
      ∀ a b, (sprinklingUnexploredGraph ω T Q F).Reachable root a →
        (sprinklingUnexploredGraph ω T Q F).Adj a b →
        (sprinklingUnexploredGraph η T Q F).Adj a b := by
    intro a b ha hab
    have haC := Finset.disjoint_left.mp hdis
      ((mem_sprinklingUnexploredCluster ω T Q F root a).mpr ⟨hab.2.1,ha⟩)
    have hbC := Finset.disjoint_left.mp hdis
      ((mem_sprinklingUnexploredCluster ω T Q F root b).mpr ⟨hab.2.2.1,ha.trans hab.reachable⟩)
    exact (haway T Q F heq a b haC hbC).mpr hab
  have hrootL : f.1 ∉ C := Finset.disjoint_left.mp hleft
    (root_mem_sprinklingUnexploredCluster ω L Q₁ F₁ hpivot.2.1)
  obtain ⟨z,hz⟩ := hhit
  obtain ⟨hzcluster,hzC⟩ := Finset.mem_inter.mp hz
  obtain ⟨hzL,hreach⟩ := (mem_sprinklingUnexploredCluster _ L Q₁ F₁ f.1 z).mp hzcluster
  rw [← hmaskL] at hreach
  obtain ⟨p⟩ := hreach
  obtain ⟨w,hw,q,hq⟩ := walk_first_component_collision
    (sprinklingUnexploredGraph ω L Q₁ F₁) (sprinklingUnexploredGraph η L Q₁ F₁)
    f.1 (C : Set (Vertex d))
    (fun a b ha hb hab => (haway L Q₁ F₁ hmaskL a b ha hb).mp hab)
    p (.refl _) hrootL hzC
  have hqV : ∀ v ∈ q.support, v ∈ CL ∪ C := by
    intro v hv
    rcases hq v hv with hvold | hvC
    · exact Finset.mem_union_left _ ((mem_sprinklingUnexploredCluster ω L Q₁ F₁ f.1 v).mpr
        ⟨microscopicWalk_support q hpivot.2.1 v hv,hvold⟩)
    · exact Finset.mem_union_right _ hvC
  obtain ⟨x,hx⟩ := hpivot.2.2.2.1
  obtain ⟨hxCL,hxA⟩ := Finset.mem_inter.mp hx
  obtain ⟨pL⟩ := ((mem_sprinklingUnexploredCluster ω L Q₁ F₁ f.1 x).mp hxCL).2
  obtain ⟨qL,hqL⟩ := walk_transfer_component _ _ f.1
    (htransfer L Q₁ F₁ f.1 hmaskL hleft) pL (.refl _)
  have hqLV : ∀ v ∈ qL.support, v ∈ CL ∪ C := by
    intro v hv
    have hpv : v ∈ pL.support := hqL ▸ hv
    exact Finset.mem_union_left _ ((mem_sprinklingUnexploredCluster ω L Q₁ F₁ f.1 v).mpr
      ⟨microscopicWalk_support pL hpivot.2.1 v hpv,(pL.takeUntil v hpv).reachable⟩)
  obtain ⟨y,hy⟩ := hpivot.2.2.2.2.1
  obtain ⟨hyCR,hyB⟩ := Finset.mem_inter.mp hy
  obtain ⟨pR⟩ := ((mem_sprinklingUnexploredCluster ω R Q₃ F₃ f.2 y).mp hyCR).2
  obtain ⟨qR,hqR⟩ := walk_transfer_component _ _ f.2
    (htransfer R Q₃ F₃ f.2 hmaskR hright) pR (.refl _)
  have hqRV : ∀ v ∈ qR.support, v ∈ CR := by
    intro v hv
    have hpv : v ∈ pR.support := hqR ▸ hv
    exact (mem_sprinklingUnexploredCluster ω R Q₃ F₃ f.2 v).mpr
      ⟨microscopicWalk_support pR hpivot.2.2.1 v hpv,(pR.takeUntil v hpv).reachable⟩
  obtain ⟨P,hPo,hPb,hPf⟩ := deleted_walk_supported_certificate η L Q₁ F₁ q hpivot.2.1 (CL ∪ C) hqV
  obtain ⟨V,hVo,hVb,hVf⟩ := deleted_walk_supported_certificate η L Q₁ F₁ qL hpivot.2.1 (CL ∪ C) hqLV
  obtain ⟨Z,hZo,hZb,hZf⟩ := deleted_walk_supported_certificate η R Q₃ F₃ qR hpivot.2.2.1 CR hqRV
  have hdisV : Disjoint (CL ∪ C) CR := Finset.disjoint_union_left.mpr
    ⟨hpivot.2.2.2.2.2,hright.symm⟩
  have hdis := disjoint_bond_certificates_of_disjoint_bases hdisV
    (fun b hb => (Finset.mem_union.mp hb).elim (hPb b) (hVb b)) hZb
  refine ⟨w,hw,(↑(P ∪ V) : Set (Bond d)),(↑Z : Set (Bond d)),
    (P ∪ V).finite_toSet,Z.finite_toSet,
    Set.disjoint_left.mpr (Finset.disjoint_left.mp hdis),?_,?_⟩
  · intro θ hagree
    refine ⟨hPf θ (fun b hb => (hagree b (Finset.mem_union_left _ hb)).trans (hPo b hb)),?_⟩
    apply connectionToSetEvent_mono (Set.Subset.refl _)
      (Set.singleton_subset_iff.mpr hxA) f.1
    exact hVf θ (fun b hb => (hagree b (Finset.mem_union_right _ hb)).trans (hVo b hb))
  · intro θ hagree
    apply connectionToSetEvent_mono (Set.Subset.refl _)
      (Set.singleton_subset_iff.mpr hyB) f.2
    exact hZf θ (fun b hb => (hagree b hb).trans (hZo b hb))

/-- Named-event version of the retained first-hit witness. -/
theorem section9_retained_left_collision_occurrence {d : ℕ}
    (S : Finset (Bond d)) (C L R Q₁ F₁ Q₃ F₃ A B : Finset (Vertex d))
    (htouch : ∀ b ∈ S, b.1 ∈ C ∨ bondTip b ∈ C)
    (ω ζ : Configuration d) (f : Vertex d × Vertex d)
    (hpivot : sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ A B f)
    (hleft : Disjoint (sprinklingUnexploredCluster ω L Q₁ F₁ f.1) C)
    (hright : Disjoint (sprinklingUnexploredCluster ω R Q₃ F₃ f.2) C)
    (hhit : (sprinklingUnexploredCluster (resampleBonds S ω ζ) L Q₁ F₁ f.1 ∩ C).Nonempty) :
    ∃ w ∈ C, resampleBonds S ω ζ ∈
      section9LeftMarkedArmOccurrence L R Q₁ F₁ Q₃ F₃ A B f w := by
  exact section9_retained_left_collision_witness S C L R Q₁ F₁ Q₃ F₃ A B
    htouch ω ζ f hpivot hleft hright hhit

end NearCritical
