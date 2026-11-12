module
public import NearCritical.Section9AvoidanceCertificate

/-! Last-exit certificates for the nonmonotone avoidance event. -/
@[expose] public section
noncomputable section
namespace NearCritical
open scoped Classical

private theorem avoidance_walk_last_exit {X : Type*} {G : SimpleGraph X} {a b : X}
    (w : G.Walk a b) (C : Set X) (hhit : ∃ x ∈ w.support, x ∈ C)
    (hb : b ∉ C) :
    ∃ (u v : X) (p : G.Walk a u) (q : G.Walk v b) (h : G.Adj u v),
      p.append (q.cons h) = w ∧ u ∈ C ∧ ∀ x ∈ q.support, x ∉ C := by
  induction w with
  | @nil a =>
    obtain ⟨x,hx,hxC⟩ := hhit
    have hxa : x = a := by simpa only [SimpleGraph.Walk.support_nil,List.mem_singleton] using hx
    exact (hb (hxa ▸ hxC)).elim
  | @cons a c b hac w ih =>
    by_cases htail : ∃ x ∈ w.support, x ∈ C
    · obtain ⟨u,v,p,q,h,hsplit,hu,hq⟩ := ih htail hb
      refine ⟨u,v,p.cons hac,q,h,?_,hu,hq⟩
      simp only [SimpleGraph.Walk.cons_append,hsplit]
    · have ha : a ∈ C := by
        obtain ⟨x,hx,hxC⟩ := hhit
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hxC
        · exact (htail ⟨x,hx,hxC⟩).elim
      exact ⟨a,c,.nil,w,hac,by simp,ha,fun x hx hxC => htail ⟨x,hx,hxC⟩⟩

private theorem avoidance_walk_restrict {d : ℕ} {ω : Configuration d}
    (D C Q F : Finset (Vertex d)) {a b : Vertex d}
    (w : (sprinklingUnexploredGraph ω D Q F).Walk a b)
    (hsupport : ∀ x ∈ w.support, x ∈ D \ C) :
    ∃ q : (sprinklingUnexploredGraph ω (D \ C) Q F).Walk a b, q.edges = w.edges := by
  induction w with
  | nil => exact ⟨.nil,rfl⟩
  | @cons a c b hac w ih =>
    have ht : ∀ x ∈ w.support, x ∈ D \ C :=
      fun x hx => hsupport x (List.mem_cons_of_mem _ hx)
    obtain ⟨q,hq⟩ := ih ht
    have ha : a ∈ D \ C := hsupport a (w.cons hac).start_mem_support
    have hc : c ∈ D \ C := ht c w.start_mem_support
    have hac' : (sprinklingUnexploredGraph ω (D \ C) Q F).Adj a c :=
      ⟨hac.1,ha,hc,hac.2.2.2⟩
    refine ⟨q.cons hac',?_⟩
    simp only [SimpleGraph.Walk.edges_cons,hq]

/-- An actual avoidance connection starting inside C has a last crossing
of C with three disjoint finite forcing witnesses. The suffix connects in
D\C, while its nonhit condition still concerns the SAME larger tube T.
The final certificate includes all currently closed available bonds in T. -/
theorem section9_avoidance_last_exit_certificates {d : ℕ} (ω : Configuration d)
    (D T C Q F B V : Finset (Vertex d)) {z : Vertex d}
    (hzD : z ∈ D) (hzC : z ∈ C) (hDT : D ⊆ T) (hBC : Disjoint B C)
    (havoid : ω ∈ section9AvoidanceEvent D T Q F B V z) :
    ∃ (u v : Vertex d) (b : Bond d),
      u ∈ D ∧ u ∈ C ∧ v ∈ D \ C ∧
      b ∈ sprinklingAvailableBonds D Q F ∧ ω b = true ∧
      ((u = b.1 ∧ v = bondTip b) ∨ (v = b.1 ∧ u = bondTip b)) ∧
      ∃ P N : Finset (Bond d),
        (∀ c ∈ P, ω c = true) ∧ (∀ c ∈ N, ω c = true) ∧
        Disjoint P {b} ∧
        Disjoint P (N ∪ section9ClosedAvailableBonds ω T Q F) ∧
        Disjoint ({b} : Finset (Bond d)) (N ∪ section9ClosedAvailableBonds ω T Q F) ∧
        Disjoint N (section9ClosedAvailableBonds ω T Q F) ∧
        ForcesOn {θ | u ∈ sprinklingUnexploredCluster θ D Q F z} ω (P : Set (Bond d)) ∧
        ForcesOn {θ | θ b = true} ω (({b} : Finset (Bond d)) : Set (Bond d)) ∧
        ForcesOn (section9AvoidanceEvent (D \ C) T Q F B V v) ω
          ((N ∪ section9ClosedAvailableBonds ω T Q F : Finset (Bond d)) : Set (Bond d)) := by
  obtain ⟨hhit,hnon⟩ := havoid
  obtain ⟨y,hy⟩ := hhit
  obtain ⟨hyCluster,hyB⟩ := Finset.mem_inter.mp hy
  obtain ⟨hyD,hyReach⟩ := (mem_sprinklingUnexploredCluster ω D Q F z y).mp hyCluster
  obtain ⟨w⟩ := hyReach
  let W := w.bypass
  have hW : W.IsTrail := w.bypass_isPath.isTrail
  have hyC : y ∉ C := fun hyC => Finset.disjoint_left.mp hBC hyB hyC
  obtain ⟨u,v,p,q,huv,hsplit,huC,hqC⟩ := avoidance_walk_last_exit W (C : Set (Vertex d))
    ⟨z,W.start_mem_support,hzC⟩ hyC
  have htrail : (p.append (q.cons huv)).IsTrail := by rw [hsplit]; exact hW
  obtain ⟨hpTrail,hqTrail,hpq⟩ := (SimpleGraph.Walk.isTrail_append p (q.cons huv)).mp htrail
  have hbridge : s(u,v) ∉ q.edges := ((SimpleGraph.Walk.isTrail_cons huv q).mp hqTrail).2
  have huD : u ∈ D := huv.2.1
  have hvD : v ∈ D := huv.2.2.1
  have hvDC : v ∈ D \ C := Finset.mem_sdiff.mpr ⟨hvD,hqC v q.start_mem_support⟩
  have hqDC : ∀ x ∈ q.support, x ∈ D \ C := by
    intro x hx
    exact Finset.mem_sdiff.mpr ⟨microscopicWalk_support q hvD x hx,hqC x hx⟩
  obtain ⟨q',hq'⟩ := avoidance_walk_restrict D C Q F q hqDC
  have hle : sprinklingUnexploredGraph ω D Q F ≤ sprinklingUnexploredGraph ω T Q F :=
    fun _ _ h => ⟨h.1,hDT h.2.1,hDT h.2.2.1,h.2.2.2⟩
  have hzv : (sprinklingUnexploredGraph ω T Q F).Reachable z v :=
    (p.reachable.trans huv.reachable).mono hle
  have hnonv : ¬ (sprinklingUnexploredCluster ω T Q F v ∩ V).Nonempty := by
    rintro ⟨x,hx⟩
    obtain ⟨hxCluster,hxV⟩ := Finset.mem_inter.mp hx
    obtain ⟨hxT,hvx⟩ := (mem_sprinklingUnexploredCluster ω T Q F v x).mp hxCluster
    apply hnon
    exact ⟨x,Finset.mem_inter.mpr
      ⟨(mem_sprinklingUnexploredCluster ω T Q F z x).mpr ⟨hxT,hzv.trans hvx⟩,hxV⟩⟩
  obtain ⟨b,hbAvailable,hbOpen,hbEnds⟩ := sprinklingUnexplored_adj_available_bond D Q F huv
  have hbEdge : s(b.1,bondTip b) = s(u,v) := by
    rcases hbEnds with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · rfl
    · exact Sym2.eq_swap
  obtain ⟨P,hP,hPEdges,hPForce⟩ := sprinklingUnexploredWalk_certificate D Q F p
  obtain ⟨N,hN,hNEdges,hNClosed,hNForce⟩ :=
    section9AvoidanceEvent_certificate ω (D \ C) T Q F B V hvDC hyB q' hnonv
  have hPBridge : Disjoint P ({b} : Finset (Bond d)) := by
    apply Finset.disjoint_left.mpr
    intro c hc hcb
    have hcb' : c = b := Finset.mem_singleton.mp hcb
    subst c
    exact List.disjoint_left.mp hpq (hPEdges b hc)
      (by simp only [SimpleGraph.Walk.edges_cons,List.mem_cons]; exact Or.inl hbEdge)
  have hPN : Disjoint P N := by
    apply Finset.disjoint_left.mpr
    intro c hcP hcN
    have hqedge : s(c.1,bondTip c) ∈ q.edges := hq' ▸ hNEdges c hcN
    exact List.disjoint_left.mp hpq (hPEdges c hcP)
      (List.mem_cons_of_mem _ hqedge)
  have hBridgeN : Disjoint ({b} : Finset (Bond d)) N := by
    apply Finset.disjoint_left.mpr
    intro c hcb hcN
    have hcb' : c = b := Finset.mem_singleton.mp hcb
    subst c
    have hqedge : s(b.1,bondTip b) ∈ q.edges := hq' ▸ hNEdges b hcN
    exact hbridge (hbEdge ▸ hqedge)
  have hPClosed : Disjoint P (section9ClosedAvailableBonds ω T Q F) :=
    (section9ClosedAvailable_disjoint_open ω T Q F P hP).symm
  have hBridgeClosed : Disjoint ({b} : Finset (Bond d))
      (section9ClosedAvailableBonds ω T Q F) :=
    (section9ClosedAvailable_disjoint_open ω T Q F {b}
      (by
        intro c hc
        rcases Finset.mem_singleton.mp hc with rfl
        exact hbOpen)).symm
  refine ⟨u,v,b,huD,huC,hvDC,hbAvailable,hbOpen,hbEnds,P,N,hP,hN,hPBridge,
    Finset.disjoint_union_right.mpr ⟨hPN,hPClosed⟩,
    Finset.disjoint_union_right.mpr ⟨hBridgeN,hBridgeClosed⟩,hNClosed,?_,?_,hNForce⟩
  · intro θ hagree
    apply (mem_sprinklingUnexploredCluster θ D Q F z u).mpr
    exact ⟨huD,hPForce θ (fun c hc => (hagree c hc).trans (hP c hc))⟩
  · intro θ hagree
    exact (hagree b (Finset.mem_singleton_self b)).trans hbOpen

end NearCritical
