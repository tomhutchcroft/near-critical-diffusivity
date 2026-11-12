module
public import NearCritical.Section9RestrictedQuartetPaths
public import NearCritical.Section8DiagramWalkCertificates

/-! Finite four-terminal tree-graph probability bounds from actual disjoint
walk certificates and proved BK under the original percolation law. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory
open scoped Classical BigOperators

/-- Five genuine quartet legs yield the actual nested occurrence used by BK. -/
theorem restricted_quartet_legs_occurrence {d : ℕ} {ω : Configuration d}
    (D : Set (Vertex d)) {a b c z : Vertex d}
    (h : restrictedQuartetLegs ω D a b c z) :
    ∃ u ∈ D, ∃ v ∈ D, ω ∈ Section8.diagramOccurrence5
      (connectionToSetEvent D a {u}) (connectionToSetEvent D b {u})
      (connectionToSetEvent D u {v}) (connectionToSetEvent D c {v})
      (connectionToSetEvent D z {v}) := by
  obtain ⟨u,hu,v,hv,p,q,r,s,t,hpq,hpr,hps,hpt,hqr,hqs,hqt,hrs,hrt,hst,hp,hq,hr,hs,ht⟩ := h
  exact ⟨u,hu,v,hv,Section8.fiveOpenWalks_diagramOccurrence p q r s t D {u} {u} {v} {v} {v}
    hp rfl hq rfl hr rfl hs rfl ht rfl hpq hpr hps hpt hqr hqs hqt hrs hrt hst⟩

private def quartetPairingEvent {d : ℕ} (D : Set (Vertex d))
    (a b c z u v : Vertex d) : Set (Configuration d) :=
  Section8.diagramOccurrence5
    (connectionToSetEvent D a {u}) (connectionToSetEvent D b {u})
    (connectionToSetEvent D u {v}) (connectionToSetEvent D c {v})
    (connectionToSetEvent D z {v})

/-- The three finite quartet diagrams bound the actual joint connection
probability, including coincident terminals and diagonal branch vertices. -/
theorem restricted_quartet_connection_probability_le {d : ℕ} (p : unitInterval)
    (R : Finset (Vertex d)) (a b c z : Vertex d) :
    let D := (R : Set (Vertex d))
    let P := fun x y => (percolation d p).real (connectionToSetEvent D x {y})
    (percolation d p).real
      ((connectionToSetEvent D a {b} ∩ connectionToSetEvent D a {c}) ∩
        connectionToSetEvent D a {z}) ≤
      (∑ u ∈ R, ∑ v ∈ R, P a u*P b u*P u v*P c v*P z v) +
      (∑ u ∈ R, ∑ v ∈ R, P a u*P c u*P u v*P b v*P z v) +
      (∑ u ∈ R, ∑ v ∈ R, P a u*P z u*P u v*P b v*P c v) := by
  intro D P
  let F := fun a b c z => ⋃ u ∈ R, ⋃ v ∈ R, quartetPairingEvent D a b c z u v
  have hsub : ((connectionToSetEvent D a {b} ∩ connectionToSetEvent D a {c}) ∩
      connectionToSetEvent D a {z}) ⊆ F a b c z ∪ (F a c b z ∪ F a z b c) := by
    rintro ω ⟨⟨⟨ha,b',hb',_,hab⟩,⟨_,c',hc',_,hac⟩⟩,⟨_,z',hz',_,haz⟩⟩
    have hbb : b' = b := hb'
    have hcc : c' = c := hc'
    have hzz : z' = z := hz'
    subst b'; subst c'; subst z'
    have hcase {a b c z : Vertex d} (h : restrictedQuartetLegs ω D a b c z) :
        ω ∈ F a b c z := by
      obtain ⟨u,hu,v,hv,hocc⟩ := restricted_quartet_legs_occurrence D h
      exact Set.mem_iUnion.mpr ⟨u,Set.mem_iUnion.mpr ⟨hu,
        Set.mem_iUnion.mpr ⟨v,Set.mem_iUnion.mpr ⟨hv,hocc⟩⟩⟩⟩
    rcases restricted_connection_quartet_paths D ha hab hac haz with h | h | h
    · exact Or.inl (hcase h)
    · exact Or.inr (Or.inl (hcase h))
    · exact Or.inr (Or.inr (hcase h))
  have hbound (a b c z : Vertex d) : (percolation d p).real (F a b c z) ≤
      ∑ u ∈ R, ∑ v ∈ R, P a u*P b u*P u v*P c v*P z v := by
    refine (measureReal_biUnion_finset_le R _).trans ?_
    apply Finset.sum_le_sum
    intro u _
    refine (measureReal_biUnion_finset_le R _).trans ?_
    apply Finset.sum_le_sum
    intro v _
    exact Section8.diagramOccurrence5_probability_le p
      (connectionToSetEvent D a {u}) (connectionToSetEvent D b {u})
      (connectionToSetEvent D u {v}) (connectionToSetEvent D c {v})
      (connectionToSetEvent D z {v})
      (connectionToSetEvent_increasing _ _ _) (connectionToSetEvent_increasing _ _ _)
      (connectionToSetEvent_increasing _ _ _) (connectionToSetEvent_increasing _ _ _)
      (connectionToSetEvent_increasing _ _ _)
  calc
    _ ≤ (percolation d p).real (F a b c z ∪ (F a c b z ∪ F a z b c)) :=
      measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ (percolation d p).real (F a b c z) +
        (percolation d p).real (F a c b z ∪ F a z b c) := measureReal_union_le _ _
    _ ≤ (percolation d p).real (F a b c z) +
        ((percolation d p).real (F a c b z) + (percolation d p).real (F a z b c)) :=
      add_le_add le_rfl (measureReal_union_le _ _)
    _ ≤ (∑ u ∈ R, ∑ v ∈ R, P a u*P b u*P u v*P c v*P z v) +
        ((∑ u ∈ R, ∑ v ∈ R, P a u*P c u*P u v*P b v*P z v) +
         (∑ u ∈ R, ∑ v ∈ R, P a u*P z u*P u v*P b v*P c v)) :=
      add_le_add (hbound a b c z) (add_le_add (hbound a c b z) (hbound a z b c))
    _ = _ := by ring

/-- The same quartet estimate summed over the two actual terminal families.
All branch and target sums are finite, and no multipoint estimate is assumed. -/
theorem restricted_quartet_target_probability_le {d : ℕ} (p : unitInterval)
    (R A B : Finset (Vertex d)) (a b : Vertex d) :
    let D := (R : Set (Vertex d))
    let P := fun x y => (percolation d p).real (connectionToSetEvent D x {y})
    (percolation d p).real
      ((connectionToSetEvent D a {b} ∩ connectionToSetEvent D a (A : Set (Vertex d))) ∩
        connectionToSetEvent D a (B : Set (Vertex d))) ≤
      ∑ c ∈ A, ∑ z ∈ B,
        ((∑ u ∈ R, ∑ v ∈ R, P a u*P b u*P u v*P c v*P z v) +
         (∑ u ∈ R, ∑ v ∈ R, P a u*P c u*P u v*P b v*P z v) +
         (∑ u ∈ R, ∑ v ∈ R, P a u*P z u*P u v*P b v*P c v)) := by
  intro D P
  let E := fun c z => (connectionToSetEvent D a {b} ∩ connectionToSetEvent D a {c}) ∩
    connectionToSetEvent D a {z}
  have hsub : ((connectionToSetEvent D a {b} ∩ connectionToSetEvent D a (A : Set (Vertex d))) ∩
      connectionToSetEvent D a (B : Set (Vertex d))) ⊆ ⋃ c ∈ A, ⋃ z ∈ B, E c z := by
    rintro ω ⟨⟨hab,⟨ha,c,hc,hcD,hac⟩⟩,⟨_,z,hz,hzD,haz⟩⟩
    exact Set.mem_iUnion.mpr ⟨c,Set.mem_iUnion.mpr ⟨hc,
      Set.mem_iUnion.mpr ⟨z,Set.mem_iUnion.mpr ⟨hz,⟨⟨hab,⟨ha,c,rfl,hcD,hac⟩⟩,⟨ha,z,rfl,hzD,haz⟩⟩⟩⟩⟩⟩
  refine (measureReal_mono hsub (measure_ne_top _ _)).trans ?_
  refine (measureReal_biUnion_finset_le A _).trans ?_
  apply Finset.sum_le_sum
  intro c _
  refine (measureReal_biUnion_finset_le B _).trans ?_
  apply Finset.sum_le_sum
  intro z _
  exact restricted_quartet_connection_probability_le p R a b c z

end NearCritical
