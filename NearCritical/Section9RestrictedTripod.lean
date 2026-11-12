module

public import NearCritical.Section8PathSeparation
public import NearCritical.Section8DiagramBK

@[expose] public section
namespace NearCritical
open scoped Classical

/-- A pair of connections in one domain yields a branch point in that
domain, with three edge-disjoint legs whose supports stay in the domain. -/
theorem restricted_connection_tripod {d : ℕ} {ω : Configuration d}
    (D : Set (Vertex d)) {a b z : Vertex d}
    (ha : a ∈ D) (hab : (restrictedGraph ω D).Reachable a b)
    (haz : (restrictedGraph ω D).Reachable a z) :
    ∃ u ∈ D, ∃ (p : (openGraph ω).Walk a u) (q : (openGraph ω).Walk u b)
      (r : (openGraph ω).Walk z u),
      p.edges.Disjoint q.edges ∧ r.edges.Disjoint p.edges ∧ r.edges.Disjoint q.edges ∧
      (∀ v ∈ p.support, v ∈ D) ∧ (∀ v ∈ q.support, v ∈ D) ∧
      (∀ v ∈ r.support, v ∈ D) := by
  obtain ⟨w⟩ := hab
  obtain ⟨t⟩ := haz
  have hle : restrictedGraph ω D ≤ openGraph ω := fun _ _ h => h.1
  let w' := w.mapLe hle
  let t' := t.reverse.mapLe hle
  have hw : ∀ v ∈ w'.bypass.support, v ∈ D := by
    intro v hv
    exact restrictedWalk_support w ha v (by
      simpa only [w', SimpleGraph.Walk.support_mapLe_eq_support] using
        w'.support_bypass_subset_support hv)
  have hz : z ∈ D := restrictedWalk_support t ha z t.end_mem_support
  have ht : ∀ v ∈ t'.support, v ∈ D := by
    intro v hv
    exact restrictedWalk_support t.reverse hz v (by
      simpa only [t', SimpleGraph.Walk.support_mapLe_eq_support] using hv)
  have hhit : ∃ v ∈ t'.support, v ∈ w'.bypass.support :=
    ⟨a, t'.end_mem_support, w'.bypass.start_mem_support⟩
  obtain ⟨u, p, q, r, s, hpq, hrs, hpqd, hrpd, hrqd, _⟩ :=
    Section8.first_hit_tripod w'.bypass w'.bypass_isPath t' hhit
  have hp : ∀ v ∈ p.support, v ∈ D := by
    intro v hv
    apply hw v
    rw [← hpq]
    exact p.support_subset_support_append_left q hv
  refine ⟨u, hp u p.end_mem_support, p, q, r, hpqd, hrpd, hrqd, hp, ?_, ?_⟩
  · intro v hv
    apply hw v
    rw [← hpq]
    exact p.support_subset_support_append_right q hv
  · intro v hv
    apply ht v
    rw [← hrs]
    exact r.support_subset_support_append_left s hv

/-- The restricted tripod yields nested disjoint occurrence with its
branch vertex in the original domain. -/
theorem restricted_connection_tripod_occurrence {d : ℕ} {ω : Configuration d}
    (D : Set (Vertex d)) {a b z : Vertex d}
    (ha : a ∈ D) (hab : (restrictedGraph ω D).Reachable a b)
    (haz : (restrictedGraph ω D).Reachable a z) :
    ∃ u ∈ D, DisjointOccurrence (connectionToSetEvent D a {u})
      {θ | DisjointOccurrence (connectionToSetEvent D u {b})
        (connectionToSetEvent D z {u}) θ} ω := by
  obtain ⟨u, hu, p, q, r, hpq, hrp, hrq, hp, hq, hr⟩ :=
    restricted_connection_tripod D ha hab haz
  obtain ⟨F, hFo, hFe, hF⟩ := openWalk_certificate p D hp
  obtain ⟨G, hGo, hGe, hG⟩ := openWalk_certificate q D hq
  obtain ⟨K, hKo, hKe, hK⟩ := openWalk_certificate r D hr
  refine ⟨u, hu, F, (G : Set (Bond d)) ∪ (K : Set (Bond d)),
    F.finite_toSet, G.finite_toSet.union K.finite_toSet, ?_, ?_, ?_⟩
  · apply Set.disjoint_left.mpr
    intro e heF he
    rcases he with heG | heK
    · exact List.disjoint_left.mp hpq (hFe e heF) (hGe e heG)
    · exact List.disjoint_left.mp hrp (hKe e heK) (hFe e heF)
  · intro θ hθ
    exact hF θ (fun e he => (hθ e he).trans (hFo e he))
  · apply Section8.forcesOn_disjointOccurrence_union G.finite_toSet K.finite_toSet
    · exact Set.disjoint_left.mpr (fun e heG heK =>
        List.disjoint_left.mp hrq (hKe e heK) (hGe e heG))
    · intro θ hθ
      exact hG θ (fun e he => (hθ e he).trans (hGo e he))
    · intro θ hθ
      exact hK θ (fun e he => (hθ e he).trans (hKo e he))

end NearCritical
