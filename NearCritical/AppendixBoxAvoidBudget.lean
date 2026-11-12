module
public import NearCritical.Section8ExtensionDeletionCost
public import NearCritical.Section9PivotalCount
public import NearCritical.Section9AvoidanceCertificate

/-! eq.lower_step3 of lem.box_twopoint_lower (main.tex 6687-6694), in generic
form for any finite `T, Q, C, W` and root `a ∈ T`:
`P[a ↔_T y] - Σ_{v ∈ C ∩ T} P[a ↔_T v] P[v ↔_T y] - Σ_{w' ∈ W} P[a ↔_T w', a ↔_T y]
   ≤ P[section9AvoidanceEvent T T Q C {y} W a]`.
The first error is the actual BK deletion cost, at the first hit of C
(`section8_extension_deletion_probability_cost`). The second is a union bound over the
excluded targets. The sum over `w'` ranges over ALL of `W`; this includes the diagonal
term which the source's `E_boundary` omits. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory
open scoped Classical

/-- Union bound splitting the unexplored connection into the avoidance event and
the joint connections to the excluded targets (generic copy of the private
Section 8 extension split). -/
theorem appendix_box_unexplored_avoidance_split {d : ℕ} (p : unitInterval)
    (T Q F W : Finset (Vertex d)) (a z : Vertex d) (ha : a ∈ T) :
    (percolation d p).real {ω | z ∈ sprinklingUnexploredCluster ω T Q F a} ≤
      (percolation d p).real (section9AvoidanceEvent T T Q F {z} W a) +
      ∑ y ∈ W, (percolation d p).real
        (connectionToSetEvent (T : Set (Vertex d)) a {y} ∩
         connectionToSetEvent (T : Set (Vertex d)) a {z}) := by
  let J := fun y => connectionToSetEvent (T : Set (Vertex d)) a {y} ∩
    connectionToSetEvent (T : Set (Vertex d)) a {z}
  have hsub : {ω | z ∈ sprinklingUnexploredCluster ω T Q F a} ⊆
      section9AvoidanceEvent T T Q F {z} W a ∪ ⋃ y ∈ W, J y := by
    intro ω hz
    by_cases hh : (sprinklingUnexploredCluster ω T Q F a ∩ W).Nonempty
    · obtain ⟨y,hy⟩ := hh
      obtain ⟨hyC,hyW⟩ := Finset.mem_inter.mp hy
      obtain ⟨hyT,hay⟩ := (mem_sprinklingUnexploredCluster ω T Q F a y).mp hyC
      obtain ⟨hzT,haz⟩ := (mem_sprinklingUnexploredCluster ω T Q F a z).mp hz
      have hle : sprinklingUnexploredGraph ω T Q F ≤ restrictedGraph ω (T : Set (Vertex d)) :=
        fun _ _ h => ⟨h.1,h.2.1,h.2.2.1⟩
      exact Or.inr (Set.mem_iUnion.mpr ⟨y,Set.mem_iUnion.mpr
        ⟨hyW,⟨ha,y,rfl,hyT,hay.mono hle⟩,⟨ha,z,rfl,hzT,haz.mono hle⟩⟩⟩)
    · exact Or.inl ⟨⟨z,Finset.mem_inter.mpr ⟨hz,Finset.mem_singleton_self z⟩⟩,hh⟩
  exact (measureReal_mono hsub (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans
      (add_le_add le_rfl (measureReal_biUnion_finset_le W J)))

/-- eq.lower_step3 (generic): the avoidance probability of a root `a` is at least
its restricted connection probability minus the explicit deletion and
excluded-target errors. -/
theorem appendix_box_avoid_lower {d : ℕ} (p : unitInterval)
    (T Q C W : Finset (Vertex d)) (a y : Vertex d) (ha : a ∈ T) :
    (percolation d p).real (connectionToSetEvent (T : Set (Vertex d)) a {y}) -
      (∑ v ∈ C ∩ T,
        (percolation d p).real (connectionToSetEvent (T : Set (Vertex d)) a {v}) *
        (percolation d p).real (connectionToSetEvent (T : Set (Vertex d)) v {y})) -
      (∑ w' ∈ W, (percolation d p).real
        (connectionToSetEvent (T : Set (Vertex d)) a {w'} ∩
         connectionToSetEvent (T : Set (Vertex d)) a {y})) ≤
      (percolation d p).real (section9AvoidanceEvent T T Q C {y} W a) := by
  have hc := section8_extension_deletion_probability_cost p T Q C a y
  have hs := appendix_box_unexplored_avoidance_split p T Q C W a y ha
  linarith

end NearCritical
