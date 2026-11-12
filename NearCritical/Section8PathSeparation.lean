module
public import NearCritical.Section8HeartAnnulus

/-! First deterministic step of the five-diagram argument: certificates for
two heart paths may overlap each other, but cannot both avoid the third path
in a branch configuration. -/
@[expose] public section
noncomputable section
namespace NearCritical.Section8
open Set
open scoped Classical

/-- A walk hitting a vertex set has a prefix whose only possible vertex in
that set is its endpoint. This constructs the first hit used in the diagrams. -/
theorem walk_first_hit {V : Type*} {G : SimpleGraph V} {x y : V}
    (w : G.Walk x y) (T : Set V) (hex : ∃ v ∈ w.support, v ∈ T) :
    ∃ (u : V) (p : G.Walk x u) (q : G.Walk u y),
      p.append q = w ∧ u ∈ T ∧ ∀ v ∈ p.support, v ∈ T → v = u := by
  induction w with
  | @nil a =>
    have ha : a ∈ T := by simpa using hex
    exact ⟨a,.nil,.nil,rfl,ha,by simp⟩
  | @cons a b c hab w ih =>
    by_cases ha : a ∈ T
    · exact ⟨a,.nil,w.cons hab,by simp,ha,by simp⟩
    · have ht : ∃ v ∈ w.support, v ∈ T := by
        obtain ⟨v,hv,hvT⟩ := hex
        rcases List.mem_cons.mp hv with rfl | hv
        · exact (ha hvT).elim
        · exact ⟨v,hv,hvT⟩
      obtain ⟨u,p,q,hpq,hu,hfirst⟩ := ih ht
      refine ⟨u,p.cons hab,q,?_,hu,?_⟩
      · simp only [SimpleGraph.Walk.cons_append,hpq]
      · intro v hv hvT
        rcases List.mem_cons.mp hv with rfl | hv
        · exact (ha hvT).elim
        · exact hfirst v hv hvT

/-- Sharing at most one vertex precludes sharing an edge, including walks
of length zero. No simplicity assumption on either walk is needed. -/
theorem walk_edges_disjoint_of_one_common_vertex {V : Type*} {G : SimpleGraph V}
    {a b c d u : V} (p : G.Walk a b) (q : G.Walk c d)
    (h : ∀ v ∈ p.support, v ∈ q.support → v = u) :
    p.edges.Disjoint q.edges := by
  apply List.disjoint_left.mpr
  intro e hep heq
  obtain ⟨v,w⟩ := e
  have hv := h v (p.fst_mem_support_of_mem_edges hep) (q.fst_mem_support_of_mem_edges heq)
  have hw := h w (p.snd_mem_support_of_mem_edges hep) (q.snd_mem_support_of_mem_edges heq)
  exact (p.adj_of_mem_edges hep).ne (hv.trans hw.symm)

/-- First hitting a simple path produces three edge-disjoint legs. The two
decompositions also retain their original support and domain information. -/
theorem first_hit_tripod {V : Type*} {G : SimpleGraph V} {x a z b : V}
    (wx : G.Walk x a) (hx : wx.IsPath) (wz : G.Walk z b)
    (hex : ∃ v ∈ wz.support, v ∈ wx.support) :
    ∃ (u : V) (p : G.Walk x u) (q : G.Walk u a)
      (r : G.Walk z u) (s : G.Walk u b),
      p.append q = wx ∧ r.append s = wz ∧
      p.edges.Disjoint q.edges ∧ r.edges.Disjoint p.edges ∧
      r.edges.Disjoint q.edges ∧
      (∀ v ∈ r.support, v ∈ wx.support → v = u) := by
  obtain ⟨u,r,s,hrs,hu,hfirst⟩ := walk_first_hit wz {v | v ∈ wx.support} hex
  refine ⟨u,wx.takeUntil u hu,wx.dropUntil u hu,r,s,
    wx.take_spec hu,hrs,hx.isTrail.disjoint_edges_takeUntil_dropUntil hu,?_,?_,hfirst⟩
  · apply walk_edges_disjoint_of_one_common_vertex
    intro v hvr hvp
    exact hfirst v hvr (wx.support_takeUntil_subset_support hu hvp)
  · apply walk_edges_disjoint_of_one_common_vertex
    intro v hvr hvq
    exact hfirst v hvr (wx.support_dropUntil_subset_support hu hvq)

/-- The first two walks need not be disjoint. Their certificate UNION forces
the pair event and is disjoint from the third certificate. -/
theorem threeWalks_pair_disjointOccurrence {d : ℕ} {ω : Configuration d}
    (Q H : Finset (Vertex d)) {x y z a b c : Vertex d}
    (wx : (openGraph ω).Walk x a) (wy : (openGraph ω).Walk y b)
    (wz : (openGraph ω).Walk z c)
    (hxQ : ∀ v ∈ wx.support, v ∈ Q) (hyQ : ∀ v ∈ wy.support, v ∈ Q)
    (hzQ : ∀ v ∈ wz.support, v ∈ Q) (ha : a ∈ H) (hb : b ∈ H) (hc : c ∈ H)
    (hxz : wx.edges.Disjoint wz.edges) (hyz : wy.edges.Disjoint wz.edges) :
    DisjointOccurrence (heartPairEvent Q H x y) (heartEvent Q H z) ω := by
  obtain ⟨F,hoF,heF,hF⟩ := openWalk_certificate wx (Q : Set (Vertex d)) hxQ
  obtain ⟨G,hoG,heG,hG⟩ := openWalk_certificate wy (Q : Set (Vertex d)) hyQ
  obtain ⟨K,hoK,heK,hK⟩ := openWalk_certificate wz (Q : Set (Vertex d)) hzQ
  refine ⟨((F ∪ G : Finset (Bond d)) : Set (Bond d)),(K : Set (Bond d)),
    (F ∪ G).finite_toSet,K.finite_toSet,?_,?_,?_⟩
  · apply Set.disjoint_left.mpr
    intro e he heK'
    rcases Finset.mem_union.mp he with heF' | heG'
    · exact List.disjoint_left.mp hxz (heF e heF') (heK e heK')
    · exact List.disjoint_left.mp hyz (heG e heG') (heK e heK')
  · intro θ hθ
    have hx := hF θ (fun e he => (hθ e (Finset.mem_union_left G he)).trans (hoF e he))
    have hy := hG θ (fun e he => (hθ e (Finset.mem_union_right F he)).trans (hoG e he))
    obtain ⟨hxQ',a',haa,haQ',hxa⟩ := hx
    obtain ⟨hyQ',b',hbb,hbQ',hyb⟩ := hy
    have haa' : a' = a := haa
    have hbb' : b' = b := hbb
    subst a'; subst b'
    exact ⟨⟨hxQ',a,ha,haQ',hxa⟩,⟨hyQ',b,hb,hbQ',hyb⟩⟩
  · intro θ hθ
    obtain ⟨hzQ',c',hcc,hcQ',hzc⟩ :=
      hK θ (fun e he => (hθ e he).trans (hoK e he))
    have hcc' : c' = c := hcc
    subst c'
    exact ⟨hzQ',c,hc,hcQ',hzc⟩

/-- In the literal branch event A(y,z), every choice of three actual heart
walks has an edge intersection of the third with at least one of the first
two. This is a conclusion, not a path-intersection hypothesis. -/
theorem heartBranch_walks_not_separated {d : ℕ} {ω : Configuration d}
    (Q H : Finset (Vertex d)) {x y z a b c : Vertex d}
    (hω : ω ∈ heartBranchEvent Q H x y z)
    (wx : (openGraph ω).Walk x a) (wy : (openGraph ω).Walk y b)
    (wz : (openGraph ω).Walk z c)
    (hxQ : ∀ v ∈ wx.support, v ∈ Q) (hyQ : ∀ v ∈ wy.support, v ∈ Q)
    (hzQ : ∀ v ∈ wz.support, v ∈ Q) (ha : a ∈ H) (hb : b ∈ H) (hc : c ∈ H) :
    ¬ (wx.edges.Disjoint wz.edges ∧ wy.edges.Disjoint wz.edges) := by
  rintro ⟨hxz,hyz⟩
  exact hω.2 (threeWalks_pair_disjointOccurrence Q H wx wy wz hxQ hyQ hzQ ha hb hc hxz hyz)

end NearCritical.Section8
