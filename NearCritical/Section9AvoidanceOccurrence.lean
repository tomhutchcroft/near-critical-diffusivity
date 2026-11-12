module
public import NearCritical.Section9AvoidanceLastExit
public import NearCritical.Section8DiagramBK

/-! Finite nested occurrence cover of the actual avoidance event. -/
@[expose] public section
noncomputable section
namespace NearCritical
open scoped Classical

/-- Actual deleted-D boundary candidates, indexed by both ordered endpoints
and the physical available bond. Both physical orientations are retained. -/
def section9AvoidanceLastExitCandidates {d : ℕ} (D C Q F : Finset (Vertex d)) :
    Finset ((Vertex d × Vertex d) × Bond d) :=
  ((D ×ˢ D) ×ˢ sprinklingAvailableBonds D Q F).filter fun t =>
    t.1.1 ∈ C ∧ t.1.2 ∉ C ∧
      ((t.1.1 = t.2.1 ∧ t.1.2 = bondTip t.2) ∨
       (t.1.2 = t.2.1 ∧ t.1.1 = bondTip t.2))

/-- Prefix, crossing bond, and suffix avoidance occur on disjoint forcing
coordinates. The suffix retains the larger nonhit tube T. -/
def section9AvoidanceLastExitOccurrence {d : ℕ}
    (D T C Q F B V : Finset (Vertex d)) (z : Vertex d)
    (t : (Vertex d × Vertex d) × Bond d) : Set (Configuration d) :=
  {ω | DisjointOccurrence
    {θ | t.1.1 ∈ sprinklingUnexploredCluster θ D Q F z}
    {θ | DisjointOccurrence {η | η t.2 = true}
      (section9AvoidanceEvent (D \ C) T Q F B V t.1.2) θ} ω}

/-- Actual avoidance is covered by a finite union of nested disjoint
occurrences at last-exit boundary candidates. This is purely deterministic;
no product inequality for the nonmonotone event is assumed. -/
theorem section9_avoidance_subset_last_exit_occurrence_union {d : ℕ}
    (D T C Q F B V : Finset (Vertex d)) {z : Vertex d}
    (hzD : z ∈ D) (hzC : z ∈ C) (hDT : D ⊆ T) (hBC : Disjoint B C) :
    section9AvoidanceEvent D T Q F B V z ⊆
      ⋃ t ∈ section9AvoidanceLastExitCandidates D C Q F,
        section9AvoidanceLastExitOccurrence D T C Q F B V z t := by
  intro ω hω
  obtain ⟨u,v,b,huD,huC,hvDC,hbAvailable,hbOpen,hbEnds,
    P,N,hP,hN,hPBridge,hPSuffix,hBridgeSuffix,hNClosed,hPrefix,hBridge,hSuffix⟩ :=
    section9_avoidance_last_exit_certificates ω D T C Q F B V
      hzD hzC hDT hBC hω
  let t : (Vertex d × Vertex d) × Bond d := ((u,v),b)
  have ht : t ∈ section9AvoidanceLastExitCandidates D C Q F := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr
      ⟨Finset.mem_product.mpr ⟨huD,(Finset.mem_sdiff.mp hvDC).1⟩,hbAvailable⟩,?_⟩
    exact ⟨huC,(Finset.mem_sdiff.mp hvDC).2,hbEnds⟩
  apply Set.mem_iUnion.mpr
  refine ⟨t,Set.mem_iUnion.mpr ⟨ht,?_⟩⟩
  change DisjointOccurrence
    {θ | u ∈ sprinklingUnexploredCluster θ D Q F z}
    {θ | DisjointOccurrence {η | η b = true}
      (section9AvoidanceEvent (D \ C) T Q F B V v) θ} ω
  refine ⟨(P : Set (Bond d)),
    (({b} : Finset (Bond d)) : Set (Bond d)) ∪
      ((N ∪ section9ClosedAvailableBonds ω T Q F : Finset (Bond d)) : Set (Bond d)),
    P.finite_toSet,
    ({b} : Finset (Bond d)).finite_toSet.union
      (N ∪ section9ClosedAvailableBonds ω T Q F).finite_toSet,?_,hPrefix,?_⟩
  · apply Set.disjoint_left.mpr
    intro c hcP hc
    rcases hc with hcBridge | hcSuffix
    · exact Finset.disjoint_left.mp hPBridge hcP hcBridge
    · exact Finset.disjoint_left.mp hPSuffix hcP hcSuffix
  · exact Section8.forcesOn_disjointOccurrence_union
      ({b} : Finset (Bond d)).finite_toSet
      (N ∪ section9ClosedAvailableBonds ω T Q F).finite_toSet
      (Set.disjoint_left.mpr (Finset.disjoint_left.mp hBridgeSuffix)) hBridge hSuffix

end NearCritical
