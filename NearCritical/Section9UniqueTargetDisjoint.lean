module
public import NearCritical.Section9AvoidanceCertificate
public import NearCritical.Section9ClusterPartition
public import NearCritical.Section9PivotalCount

/-! Unique-boundary connections to one target are mutually exclusive. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory
open scoped Classical BigOperators

/-- Distinct boundary roots cannot both be the unique boundary point of the
same component containing z. No probability or independence input is used. -/
theorem section9_unique_target_events_disjoint {d : ℕ}
    (T Q F W : Finset (Vertex d)) (z : Vertex d)
    {x y : Vertex d} (hyT : y ∈ T) (hyW : y ∈ W) (hxy : x ≠ y) :
    Disjoint (section9AvoidanceEvent T T Q F {z} (W \ {x}) x)
      (section9AvoidanceEvent T T Q F {z} (W \ {y}) y) := by
  apply Set.disjoint_left.mpr
  intro ω hx hy
  obtain ⟨u,hu⟩ := hx.1
  obtain ⟨huC,huz⟩ := Finset.mem_inter.mp hu
  have huz' : u = z := Finset.mem_singleton.mp huz
  subst u
  obtain ⟨v,hv⟩ := hy.1
  obtain ⟨hvC,hvz⟩ := Finset.mem_inter.mp hv
  have hvz' : v = z := Finset.mem_singleton.mp hvz
  subst v
  have hreach := ((mem_sprinklingUnexploredCluster ω T Q F x z).mp huC).2.trans
    ((mem_sprinklingUnexploredCluster ω T Q F y z).mp hvC).2.symm
  apply hx.2
  refine ⟨y,Finset.mem_inter.mpr ⟨?_,?_⟩⟩
  · exact (mem_sprinklingUnexploredCluster ω T Q F x y).mpr ⟨hyT,hreach⟩
  · exact Finset.mem_sdiff.mpr ⟨hyW,by simpa using Ne.symm hxy⟩

/-- The sum of actual unique-boundary probabilities is bounded by the actual
connection-to-B probability. This applies equally to a finite revealed law. -/
theorem section9_unique_target_probability_sum_le {d : ℕ}
    (μ : Measure (Configuration d)) [IsFiniteMeasure μ]
    (T Q F W B : Finset (Vertex d)) (z : Vertex d)
    (hBT : B ⊆ T) (hBW : B ⊆ W) :
    (∑ y ∈ B, μ.real (section9AvoidanceEvent T T Q F {z} (W \ {y}) y)) ≤
      μ.real {ω | (sprinklingUnexploredCluster ω T Q F z ∩ B).Nonempty} := by
  let E := fun y => section9AvoidanceEvent T T Q F {z} (W \ {y}) y
  have hd : Set.PairwiseDisjoint (B : Set (Vertex d)) E := by
    intro x hx y hy hxy
    exact section9_unique_target_events_disjoint T Q F W z (hBT hy) (hBW hy) hxy
  have hm (y : Vertex d) (_hy : y ∈ B) : MeasurableSet (E y) :=
    (measurableSet_sprinklingUnexploredCluster_hits T Q F {z} y).inter
      (measurableSet_sprinklingUnexploredCluster_hits T Q F (W \ {y}) y).compl
  rw [← measureReal_biUnion_finset hd hm]
  apply measureReal_mono _ (measure_ne_top _ _)
  intro ω hω
  obtain ⟨y,hy⟩ := Set.mem_iUnion.mp hω
  obtain ⟨hyB,hyE⟩ := Set.mem_iUnion.mp hy
  obtain ⟨u,hu⟩ := hyE.1
  obtain ⟨huC,huz⟩ := Finset.mem_inter.mp hu
  have huz' : u = z := Finset.mem_singleton.mp huz
  subst u
  refine ⟨y,Finset.mem_inter.mpr ⟨?_,hyB⟩⟩
  exact (mem_sprinklingUnexploredCluster ω T Q F z y).mpr
    ⟨hBT hyB,((mem_sprinklingUnexploredCluster ω T Q F y z).mp huC).2.symm⟩

end NearCritical
