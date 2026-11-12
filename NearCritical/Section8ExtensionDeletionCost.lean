module
public import NearCritical.Section9RestrictedTripod
public import NearCritical.Section9PivotalCount

/-! Actual explored-edge deletion cost for unique extension. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory
open scoped Classical BigOperators

private theorem extension_walk_avoiding_F {d : ℕ} {ω : Configuration d}
    (T Q F : Finset (Vertex d)) {a b : Vertex d}
    (w : (restrictedGraph ω (T : Set (Vertex d))).Walk a b) :
    (∀ u ∈ w.support, u ∉ F) → Nonempty ((sprinklingUnexploredGraph ω T Q F).Walk a b) := by
  induction w with
  | nil => intro _; exact ⟨.nil⟩
  | @cons a c b hac w ih =>
    intro hsupport
    have htail : ∀ u ∈ w.support, u ∉ F :=
      fun u hu => hsupport u (List.mem_cons_of_mem _ hu)
    obtain ⟨q⟩ := ih htail
    have ha : a ∉ F := hsupport a (w.cons hac).start_mem_support
    have hc : c ∉ F := htail c w.start_mem_support
    have hadj : (sprinklingUnexploredGraph ω T Q F).Adj a c := by
      refine ⟨hac.1,hac.2.1,hac.2.2,?_⟩
      intro he
      obtain ⟨_,_,heF⟩ := (pair_mem_exploredEdgeSet (Q : Set (Vertex d))
        (F : Set (Vertex d)) a c).mp he
      exact heF.elim ha hc
    exact ⟨q.cons hadj⟩

/-- Every full-tube connection either survives explored-edge deletion or
has two edge-disjoint connection certificates meeting at a vertex of F∩T. -/
theorem section8_extension_deletion_cover {d : ℕ}
    (T Q F : Finset (Vertex d)) (x z : Vertex d) :
    connectionToSetEvent (T : Set (Vertex d)) x {z} ⊆
      {ω | z ∈ sprinklingUnexploredCluster ω T Q F x} ∪
      ⋃ y ∈ F ∩ T, {ω | DisjointOccurrence
        (connectionToSetEvent (T : Set (Vertex d)) x {y})
        (connectionToSetEvent (T : Set (Vertex d)) y {z}) ω} := by
  rintro ω ⟨hx,t,ht,hz,hreach⟩
  have htz : t = z := ht
  subst t
  obtain ⟨w⟩ := hreach
  let W := w.bypass
  by_cases hhit : ∃ y ∈ W.support, y ∈ F
  · obtain ⟨y,p,q,hpq,hyF,_⟩ := Section8.walk_first_hit W (F : Set (Vertex d)) hhit
    have htrail : (p.append q).IsTrail := by rw [hpq]; exact w.bypass_isPath.isTrail
    have hdis := ((SimpleGraph.Walk.isTrail_append p q).mp htrail).2.2
    have hyT : y ∈ T := restrictedWalk_support p hx y p.end_mem_support
    have hle : restrictedGraph ω (T : Set (Vertex d)) ≤ openGraph ω := fun _ _ h => h.1
    let p' := p.mapLe hle
    let q' := q.mapLe hle
    have hpD : ∀ u ∈ p'.support, u ∈ (T : Set (Vertex d)) := by
      intro u hu
      exact restrictedWalk_support p hx u (by
        simpa only [p',SimpleGraph.Walk.support_mapLe_eq_support] using hu)
    have hqD : ∀ u ∈ q'.support, u ∈ (T : Set (Vertex d)) := by
      intro u hu
      exact restrictedWalk_support q hyT u (by
        simpa only [q',SimpleGraph.Walk.support_mapLe_eq_support] using hu)
    obtain ⟨P,hPo,hPe,hP⟩ := openWalk_certificate p' (T : Set (Vertex d)) hpD
    obtain ⟨N,hNo,hNe,hN⟩ := openWalk_certificate q' (T : Set (Vertex d)) hqD
    have hdis' : p'.edges.Disjoint q'.edges := by
      simpa only [p',q',SimpleGraph.Walk.edges_mapLe_eq_edges] using hdis
    apply Or.inr
    refine Set.mem_iUnion.mpr ⟨y,Set.mem_iUnion.mpr ⟨Finset.mem_inter.mpr ⟨hyF,hyT⟩,?_⟩⟩
    refine ⟨(P : Set (Bond d)),(N : Set (Bond d)),P.finite_toSet,N.finite_toSet,?_,?_,?_⟩
    · exact Set.disjoint_left.mpr (fun b hbP hbN => List.disjoint_left.mp hdis' (hPe b hbP) (hNe b hbN))
    · intro θ hagree
      exact hP θ (fun b hb => (hagree b hb).trans (hPo b hb))
    · intro θ hagree
      exact hN θ (fun b hb => (hagree b hb).trans (hNo b hb))
  · obtain ⟨q⟩ := extension_walk_avoiding_F T Q F W
      (fun u hu huF => hhit ⟨u,hu,huF⟩)
    exact Or.inl ((mem_sprinklingUnexploredCluster ω T Q F x z).mpr ⟨hz,⟨q⟩⟩)

/-- Quantitative explored-edge deletion loss from actual increasing-event BK.
The arms retain the full original tube. Neither a connection lower bound nor
an upper bound on the deletion error is supplied as a premise. -/
theorem section8_extension_deletion_probability_cost {d : ℕ} (p : unitInterval)
    (T Q F : Finset (Vertex d)) (x z : Vertex d) :
    (percolation d p).real (connectionToSetEvent (T : Set (Vertex d)) x {z}) ≤
      (percolation d p).real {ω | z ∈ sprinklingUnexploredCluster ω T Q F x} +
      ∑ y ∈ F ∩ T,
        (percolation d p).real (connectionToSetEvent (T : Set (Vertex d)) x {y}) *
        (percolation d p).real (connectionToSetEvent (T : Set (Vertex d)) y {z}) := by
  let J := fun y => {ω : Configuration d | DisjointOccurrence
    (connectionToSetEvent (T : Set (Vertex d)) x {y})
    (connectionToSetEvent (T : Set (Vertex d)) y {z}) ω}
  calc
    _ ≤ (percolation d p).real {ω | z ∈ sprinklingUnexploredCluster ω T Q F x} +
        (percolation d p).real (⋃ y ∈ F ∩ T, J y) :=
      (measureReal_mono (section8_extension_deletion_cover T Q F x z) (measure_ne_top _ _)).trans
        (measureReal_union_le _ _)
    _ ≤ (percolation d p).real {ω | z ∈ sprinklingUnexploredCluster ω T Q F x} +
        ∑ y ∈ F ∩ T, (percolation d p).real (J y) :=
      add_le_add le_rfl (measureReal_biUnion_finset_le (F ∩ T) J)
    _ ≤ _ := add_le_add le_rfl (Finset.sum_le_sum fun y _ =>
      percolation_bk d p _ _ (connectionToSetEvent_increasing _ _ _)
        (connectionToSetEvent_increasing _ _ _))

end NearCritical
