module
public import NearCritical.Section9RestrictedTripod

/-! Four-terminal finite tree witnesses, with all five legs in the original
restricted domain and genuinely pairwise edge-disjoint. -/
@[expose] public section
noncomputable section
namespace NearCritical
open scoped Classical

/-- A four-terminal pairing has two branch vertices and five pairwise
edge-disjoint open walks, all supported in the original domain. -/
def restrictedQuartetLegs {d : ℕ} (ω : Configuration d) (D : Set (Vertex d))
    (a b c z : Vertex d) : Prop :=
  ∃ u ∈ D, ∃ v ∈ D,
    ∃ (p : (openGraph ω).Walk a u) (q : (openGraph ω).Walk b u)
      (r : (openGraph ω).Walk u v) (s : (openGraph ω).Walk c v)
      (t : (openGraph ω).Walk z v),
    p.edges.Disjoint q.edges ∧ p.edges.Disjoint r.edges ∧
    p.edges.Disjoint s.edges ∧ p.edges.Disjoint t.edges ∧
    q.edges.Disjoint r.edges ∧ q.edges.Disjoint s.edges ∧
    q.edges.Disjoint t.edges ∧ r.edges.Disjoint s.edges ∧
    r.edges.Disjoint t.edges ∧ s.edges.Disjoint t.edges ∧
    (∀ x ∈ p.support, x ∈ D) ∧ (∀ x ∈ q.support, x ∈ D) ∧
    (∀ x ∈ r.support, x ∈ D) ∧ (∀ x ∈ s.support, x ∈ D) ∧
    (∀ x ∈ t.support, x ∈ D)

private theorem quartet_disjoint_mono {α : Type*} {p q p' q' : List α}
    (h : p.Disjoint q) (hp : p' ⊆ p) (hq : q' ⊆ q) : p'.Disjoint q' := by
  apply List.disjoint_left.mpr
  intro e he hf
  exact List.disjoint_left.mp h (hp he) (hq hf)

private theorem quartet_reverse_left {d : ℕ} {ω : Configuration d}
    {a b c e : Vertex d} (p : (openGraph ω).Walk a b) (q : (openGraph ω).Walk c e)
    (h : p.edges.Disjoint q.edges) : p.reverse.edges.Disjoint q.edges := by
  simpa only [SimpleGraph.Walk.edges_reverse,List.disjoint_reverse_left] using h

private theorem quartet_reverse_right {d : ℕ} {ω : Configuration d}
    {a b c e : Vertex d} (p : (openGraph ω).Walk a b) (q : (openGraph ω).Walk c e)
    (h : p.edges.Disjoint q.edges) : p.edges.Disjoint q.reverse.edges := by
  simpa only [SimpleGraph.Walk.edges_reverse,List.disjoint_reverse_right] using h

private theorem quartet_swap_pairs {d : ℕ} {ω : Configuration d} {D : Set (Vertex d)}
    {a b c z : Vertex d} (h : restrictedQuartetLegs ω D a b c z) :
    restrictedQuartetLegs ω D c z a b := by
  obtain ⟨u,hu,v,hv,p,q,r,s,t,hpq,hpr,hps,hpt,hqr,hqs,hqt,hrs,hrt,hst,hp,hq,hr,hs,ht⟩ := h
  refine ⟨v,hv,u,hu,s,t,r.reverse,p,q,hst,?_,hps.symm,hqs.symm,?_,hpt.symm,hqt.symm,?_,?_,hpq,
    hs,ht,?_,hp,hq⟩
  · exact quartet_reverse_right s r hrs.symm
  · exact quartet_reverse_right t r hrt.symm
  · exact quartet_reverse_left r p hpr.symm
  · exact quartet_reverse_left r q hqr.symm
  · intro x hx
    exact hr x (by simpa only [SimpleGraph.Walk.support_reverse,List.mem_reverse] using hx)

/-- Splitting the first leg at the first-hit vertex gives one pairing. -/
private theorem quartet_of_first_leg_hit {d : ℕ} {ω : Configuration d}
    (D : Set (Vertex d)) {a b c z u v : Vertex d}
    (p : (openGraph ω).Walk a u) (q : (openGraph ω).Walk b u)
    (r : (openGraph ω).Walk c u) (t : (openGraph ω).Walk z v)
    (hptrail : p.IsTrail) (hv : v ∈ p.support)
    (hpq : p.edges.Disjoint q.edges) (hpr : p.edges.Disjoint r.edges)
    (hqr : q.edges.Disjoint r.edges)
    (htp : t.edges.Disjoint p.edges) (htq : t.edges.Disjoint q.edges)
    (htr : t.edges.Disjoint r.edges)
    (hp : ∀ x ∈ p.support, x ∈ D) (hq : ∀ x ∈ q.support, x ∈ D)
    (hr : ∀ x ∈ r.support, x ∈ D) (ht : ∀ x ∈ t.support, x ∈ D) :
    restrictedQuartetLegs ω D a z b c := by
  have htake := p.edges_takeUntil_subset_edges hv
  have hdrop := p.edges_dropUntil_subset_edges hv
  refine ⟨v,hp v hv,u,hp u p.end_mem_support,p.takeUntil v hv,t,p.dropUntil v hv,q,r,
    ?_,hptrail.disjoint_edges_takeUntil_dropUntil hv,?_,?_,?_,htq,htr,?_,?_,hqr,?_,ht,?_,hq,hr⟩
  · exact quartet_disjoint_mono htp.symm htake (fun _ h => h)
  · exact quartet_disjoint_mono hpq htake (fun _ h => h)
  · exact quartet_disjoint_mono hpr htake (fun _ h => h)
  · exact quartet_disjoint_mono htp (fun _ h => h) hdrop
  · exact quartet_disjoint_mono hpq hdrop (fun _ h => h)
  · exact quartet_disjoint_mono hpr hdrop (fun _ h => h)
  · intro x hx
    exact hp x (p.support_takeUntil_subset_support hv hx)
  · intro x hx
    exact hp x (p.support_dropUntil_subset_support hv hx)

/-- Four vertices connected in one restricted graph have one of the three
finite four-terminal tree pairings. No tree-graph estimate is a premise. -/
theorem restricted_connection_quartet_paths {d : ℕ} {ω : Configuration d}
    (D : Set (Vertex d)) {a b c z : Vertex d}
    (ha : a ∈ D) (hab : (restrictedGraph ω D).Reachable a b)
    (hac : (restrictedGraph ω D).Reachable a c)
    (haz : (restrictedGraph ω D).Reachable a z) :
    restrictedQuartetLegs ω D a b c z ∨
      restrictedQuartetLegs ω D a c b z ∨
      restrictedQuartetLegs ω D a z b c := by
  obtain ⟨u,hu,p,q,r,hpq,hrp,hrq,hp,hq,hr⟩ := restricted_connection_tripod D ha hab hac
  let P := p.bypass
  let Q := q.reverse.bypass
  let R := r.bypass
  have hP : ∀ x ∈ P.support, x ∈ D := fun x hx => hp x (p.support_bypass_subset_support hx)
  have hQ : ∀ x ∈ Q.support, x ∈ D := by
    intro x hx
    have hh := q.reverse.support_bypass_subset_support hx
    exact hq x (by simpa only [SimpleGraph.Walk.support_reverse,List.mem_reverse] using hh)
  have hR : ∀ x ∈ R.support, x ∈ D := fun x hx => hr x (r.support_bypass_subset_support hx)
  have hPQ : P.edges.Disjoint Q.edges := quartet_disjoint_mono
    (quartet_reverse_right p q hpq) p.edges_bypass_subset_edges q.reverse.edges_bypass_subset_edges
  have hPR : P.edges.Disjoint R.edges := quartet_disjoint_mono hrp.symm
    p.edges_bypass_subset_edges r.edges_bypass_subset_edges
  have hQR : Q.edges.Disjoint R.edges := quartet_disjoint_mono
    (quartet_reverse_left q r hrq.symm) q.reverse.edges_bypass_subset_edges r.edges_bypass_subset_edges
  obtain ⟨w⟩ := haz
  have hle : restrictedGraph ω D ≤ openGraph ω := fun _ _ h => h.1
  let W := w.reverse.mapLe hle
  have hz : z ∈ D := restrictedWalk_support w ha z w.end_mem_support
  have hW : ∀ x ∈ W.support, x ∈ D := by
    intro x hx
    exact restrictedWalk_support w.reverse hz x
      (by simpa only [W,SimpleGraph.Walk.support_mapLe_eq_support] using hx)
  let T : Set (Vertex d) := {x | x ∈ P.support ∨ x ∈ Q.support ∨ x ∈ R.support}
  have hhit : ∃ x ∈ W.support, x ∈ T := ⟨a,W.end_mem_support,Or.inl P.start_mem_support⟩
  obtain ⟨v,t,s,hts,hv,hfirst⟩ := Section8.walk_first_hit W T hhit
  have ht : ∀ x ∈ t.support, x ∈ D := by
    intro x hx
    apply hW x
    rw [← hts]
    exact t.support_subset_support_append_left s hx
  have htP : t.edges.Disjoint P.edges := by
    apply Section8.walk_edges_disjoint_of_one_common_vertex
    intro x hx hxP
    exact hfirst x hx (Or.inl hxP)
  have htQ : t.edges.Disjoint Q.edges := by
    apply Section8.walk_edges_disjoint_of_one_common_vertex
    intro x hx hxQ
    exact hfirst x hx (Or.inr (Or.inl hxQ))
  have htR : t.edges.Disjoint R.edges := by
    apply Section8.walk_edges_disjoint_of_one_common_vertex
    intro x hx hxR
    exact hfirst x hx (Or.inr (Or.inr hxR))
  rcases hv with hvP | hvQ | hvR
  · exact Or.inr (Or.inr (quartet_of_first_leg_hit D P Q R t p.bypass_isPath.isTrail hvP
      hPQ hPR hQR htP htQ htR hP hQ hR ht))
  · apply Or.inr ∘ Or.inl
    exact quartet_swap_pairs (quartet_of_first_leg_hit D Q P R t q.reverse.bypass_isPath.isTrail hvQ
      hPQ.symm hQR hPR htQ htP htR hQ hP hR ht)
  · apply Or.inl
    exact quartet_swap_pairs (quartet_of_first_leg_hit D R P Q t r.bypass_isPath.isTrail hvR
      hPR.symm hQR.symm hPQ htR htP htQ hR hP hQ ht)

end NearCritical
