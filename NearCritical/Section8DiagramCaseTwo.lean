module
public import NearCritical.Section8PathSeparation

/-! Deterministic Case 2 of the source five-diagram argument. First hit the
UNION of the x and z paths; hitting x first would provide a rerouting that
contradicts the literal branch event. -/
@[expose] public section
noncomputable section
namespace NearCritical.Section8
open Set
open scoped Classical

theorem branch_caseTwo_first_hit {d : ℕ} {ω : Configuration d}
    (Q H : Finset (Vertex d)) {x y z a b c : Vertex d}
    (hω : ω ∈ heartBranchEvent Q H x y z)
    (wx : (openGraph ω).Walk x a) (wy : (openGraph ω).Walk y b)
    (wz : (openGraph ω).Walk z c)
    (hxQ : ∀ v ∈ wx.support, v ∈ Q) (hyQ : ∀ v ∈ wy.support, v ∈ Q)
    (hzQ : ∀ v ∈ wz.support, v ∈ Q) (ha : a ∈ H) (hc : c ∈ H)
    (hxz : wx.support.Disjoint wz.support)
    (hex : ∃ v ∈ wy.support, v ∈ wz.support) :
    ∃ (u : Vertex d) (p : (openGraph ω).Walk y u) (q : (openGraph ω).Walk u b),
      p.append q = wy ∧ u ∈ wz.support ∧ p.support.Disjoint wx.support ∧
      p.edges.Disjoint wz.edges ∧ (∀ v ∈ p.support, v ∈ Q) := by
  obtain ⟨u,p,q,hpq,hu,hfirst⟩ := walk_first_hit wy
    {v | v ∈ wx.support ∨ v ∈ wz.support}
    (by obtain ⟨v,hvy,hvz⟩ := hex; exact ⟨v,hvy,Or.inr hvz⟩)
  have hpQ : ∀ v ∈ p.support, v ∈ Q := by
    intro v hv
    apply hyQ v
    rw [← hpq]
    exact p.support_subset_support_append_left q hv
  have hxzedges : wx.edges.Disjoint wz.edges := by
    apply walk_edges_disjoint_of_one_common_vertex (u := u)
    intro v hvx hvz
    exact (List.disjoint_left.mp hxz hvx hvz).elim
  have hunx : u ∉ wx.support := by
    intro hux
    have hunz : u ∉ wz.support := fun huz => List.disjoint_left.mp hxz hux huz
    have hpz : p.support.Disjoint wz.support := by
      apply List.disjoint_left.mpr
      intro v hvp hvz
      have hvu := hfirst v hvp (Or.inr hvz)
      exact hunz (hvu ▸ hvz)
    let t := wx.dropUntil u hux
    have htQ : ∀ v ∈ t.support, v ∈ Q :=
      fun v hv => hxQ v (wx.support_dropUntil_subset_support hux hv)
    have htz : t.support.Disjoint wz.support := by
      apply List.disjoint_left.mpr
      intro v hvt hvz
      exact List.disjoint_left.mp hxz (wx.support_dropUntil_subset_support hux hvt) hvz
    have hpyQ : ∀ v ∈ (p.append t).support, v ∈ Q := by
      intro v hv
      simp only [SimpleGraph.Walk.support_append,List.mem_append] at hv
      rcases hv with hv | hv
      · exact hpQ v hv
      · exact htQ v (List.mem_of_mem_tail hv)
    have hpyz : (p.append t).edges.Disjoint wz.edges := by
      apply walk_edges_disjoint_of_one_common_vertex (u := u)
      intro v hv hvz
      simp only [SimpleGraph.Walk.support_append,List.mem_append] at hv
      rcases hv with hv | hv
      · exact (List.disjoint_left.mp hpz hv hvz).elim
      · exact (List.disjoint_left.mp htz (List.mem_of_mem_tail hv) hvz).elim
    exact hω.2 (threeWalks_pair_disjointOccurrence Q H wx (p.append t) wz
      hxQ hpyQ hzQ ha ha hc hxzedges hpyz)
  have huz : u ∈ wz.support := hu.resolve_left hunx
  refine ⟨u,p,q,hpq,huz,?_,?_,hpQ⟩
  · apply List.disjoint_left.mpr
    intro v hvp hvx
    have hvu := hfirst v hvp (Or.inl hvx)
    exact hunx (hvu ▸ hvx)
  · apply walk_edges_disjoint_of_one_common_vertex
    intro v hvp hvz
    exact hfirst v hvp (Or.inr hvz)

 /-- Actual four pairwise edge-disjoint walks forming source diagram 5.
 The z walk is chosen simple; the y prefix need not be simple. -/
theorem branch_caseTwo_diagram_five {d : ℕ} {ω : Configuration d}
    (Q H : Finset (Vertex d)) {x y z a b c : Vertex d}
    (hω : ω ∈ heartBranchEvent Q H x y z)
    (wx : (openGraph ω).Walk x a) (wy : (openGraph ω).Walk y b)
    (wz : (openGraph ω).Walk z c) (hwz : wz.IsPath)
    (hxQ : ∀ v ∈ wx.support, v ∈ Q) (hyQ : ∀ v ∈ wy.support, v ∈ Q)
    (hzQ : ∀ v ∈ wz.support, v ∈ Q) (ha : a ∈ H) (hc : c ∈ H)
    (hxz : wx.support.Disjoint wz.support)
    (hex : ∃ v ∈ wy.support, v ∈ wz.support) :
    ∃ (u : Vertex d) (p : (openGraph ω).Walk y u)
      (r : (openGraph ω).Walk z u) (s : (openGraph ω).Walk u c),
      u ∈ Q ∧ r.append s = wz ∧
      wx.edges.Disjoint p.edges ∧ wx.edges.Disjoint r.edges ∧
      wx.edges.Disjoint s.edges ∧ p.edges.Disjoint r.edges ∧
      p.edges.Disjoint s.edges ∧ r.edges.Disjoint s.edges ∧
      (∀ v ∈ p.support, v ∈ Q) ∧ (∀ v ∈ r.support, v ∈ Q) ∧
      (∀ v ∈ s.support, v ∈ Q) := by
  obtain ⟨u,p,_q,_hpq,hu,hpx,hpz,hpQ⟩ :=
    branch_caseTwo_first_hit Q H hω wx wy wz hxQ hyQ hzQ ha hc hxz hex
  refine ⟨u,p,wz.takeUntil u hu,wz.dropUntil u hu,hzQ u hu,wz.take_spec hu,
    ?_,?_,?_,?_,?_,hwz.isTrail.disjoint_edges_takeUntil_dropUntil hu,hpQ,
    (fun v hv => hzQ v (wz.support_takeUntil_subset_support hu hv)),
    (fun v hv => hzQ v (wz.support_dropUntil_subset_support hu hv))⟩
  · apply walk_edges_disjoint_of_one_common_vertex (u := u)
    intro v hvx hvp
    exact (List.disjoint_left.mp hpx hvp hvx).elim
  · apply walk_edges_disjoint_of_one_common_vertex (u := u)
    intro v hvx hvr
    exact (List.disjoint_left.mp hxz hvx (wz.support_takeUntil_subset_support hu hvr)).elim
  · apply walk_edges_disjoint_of_one_common_vertex (u := u)
    intro v hvx hvs
    exact (List.disjoint_left.mp hxz hvx (wz.support_dropUntil_subset_support hu hvs)).elim
  · apply List.disjoint_left.mpr
    intro e hep her
    exact List.disjoint_left.mp hpz hep (wz.edges_takeUntil_subset_edges hu her)
  · apply List.disjoint_left.mpr
    intro e hep hes
    exact List.disjoint_left.mp hpz hep (wz.edges_dropUntil_subset_edges hu hes)

/-- Transport the literal branch event, including its disjoint-occurrence
exclusion, to the annulus. All three starting points must lie in Ann. -/
theorem heartBranchEvent_eq_annulus {d : ℕ} (Q H : Finset (Vertex d)) (x y z : Vertex d)
    (hx : x ∈ heartAnnulus Q H) (hy : y ∈ heartAnnulus Q H) (hz : z ∈ heartAnnulus Q H) :
    heartBranchEvent Q H x y z =
      heartBranchEvent (heartAnnulus Q H) (boundarySites H) x y z := by
  have he (v : Vertex d) (hv : v ∈ heartAnnulus Q H) :
      heartEvent Q H v = heartEvent (heartAnnulus Q H) (boundarySites H) v :=
    heartEvent_eq_annulus Q H v hv
  simp only [heartBranchEvent,heartTripleEvent,heartPairEvent,he x hx,he y hy,he z hz]

/-- Source Case 2 with actual A(y,z), all legs confined to Ann, and both
heart endpoints on its retained inner boundary. -/
theorem heartBranch_annulus_diagram_five {d : ℕ} {ω : Configuration d}
    (Q H : Finset (Vertex d)) {x y z a b c : Vertex d}
    (hω : ω ∈ heartBranchEvent Q H x y z)
    (wx : (openGraph ω).Walk x a) (wy : (openGraph ω).Walk y b)
    (wz : (openGraph ω).Walk z c) (hwz : wz.IsPath)
    (hxAnn : ∀ v ∈ wx.support, v ∈ heartAnnulus Q H)
    (hyAnn : ∀ v ∈ wy.support, v ∈ heartAnnulus Q H)
    (hzAnn : ∀ v ∈ wz.support, v ∈ heartAnnulus Q H)
    (ha : a ∈ boundarySites H) (hc : c ∈ boundarySites H)
    (hxz : wx.support.Disjoint wz.support)
    (hex : ∃ v ∈ wy.support, v ∈ wz.support) :
    ∃ (u : Vertex d) (p : (openGraph ω).Walk y u)
      (r : (openGraph ω).Walk z u) (s : (openGraph ω).Walk u c),
      u ∈ heartAnnulus Q H ∧ r.append s = wz ∧
      wx.edges.Disjoint p.edges ∧ wx.edges.Disjoint r.edges ∧
      wx.edges.Disjoint s.edges ∧ p.edges.Disjoint r.edges ∧
      p.edges.Disjoint s.edges ∧ r.edges.Disjoint s.edges ∧
      (∀ v ∈ p.support, v ∈ heartAnnulus Q H) ∧
      (∀ v ∈ r.support, v ∈ heartAnnulus Q H) ∧
      (∀ v ∈ s.support, v ∈ heartAnnulus Q H) := by
  rw [heartBranchEvent_eq_annulus Q H x y z
    (hxAnn x wx.start_mem_support) (hyAnn y wy.start_mem_support)
    (hzAnn z wz.start_mem_support)] at hω
  exact branch_caseTwo_diagram_five (heartAnnulus Q H) (boundarySites H) hω
    wx wy wz hwz hxAnn hyAnn hzAnn ha hc hxz hex

end NearCritical.Section8
