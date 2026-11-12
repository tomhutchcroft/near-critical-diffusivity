module

public import NearCritical.RegularCubeSpanningRate
public import NearCritical.ClusterRevealSupport

/-! Measurability input of prop.regular_cube discharged for the cluster part.

`x` lies in the union of the filtered family iff `x ∈ Q` and the actual cluster
of `x` satisfies `P` (`mem_filtered_biUnion_iff`). That event is a countable
union of cluster-reveal cylinders (`measurableSet_clusterReveal_event`). So the
bad-point events are measurable as soon as membership in the regular-point sets
`R ω i` is. `cube_not_regular_le_of_rate_meas` is prop.regular_cube with that
weaker hypothesis. -/

@[expose] public section
noncomputable section

namespace NearCritical

open MeasureTheory Finset
open scoped ENNReal Classical

attribute [local instance 100000] Classical.propDecidable

lemma mem_filtered_biUnion_iff {d : ℕ} (ω : Configuration d) (Q : Finset (Vertex d))
    (P : Finset (Vertex d) → Prop) (x : Vertex d) :
    x ∈ (filteredClusterFamily ω Q P).biUnion id ↔ x ∈ Q ∧ P (finiteBoxCluster ω Q x) := by
  rw [Finset.mem_biUnion]
  constructor
  · rintro ⟨C, hC, hx⟩
    unfold filteredClusterFamily at hC
    obtain ⟨hCF, hP⟩ := Finset.mem_filter.mp hC
    refine ⟨finiteClusterFamily_component_subset ω Q hCF hx, ?_⟩
    rw [finiteClusterFamily_recover ω Q hCF hx]
    exact hP
  · rintro ⟨hx, hP⟩
    refine ⟨finiteBoxCluster ω Q x, ?_, root_mem_finiteBoxCluster ω Q hx⟩
    unfold filteredClusterFamily
    exact Finset.mem_filter.mpr ⟨(mem_finiteClusterFamily ω Q _).mpr ⟨x, hx, rfl⟩, hP⟩

lemma measurableSet_clusterProp {d : ℕ} (Q : Finset (Vertex d))
    (P : Finset (Vertex d) → Prop) (x : Vertex d) :
    MeasurableSet {ω : Configuration d | x ∈ Q ∧ P (finiteBoxCluster ω Q x)} := by
  by_cases hx : x ∈ Q
  · have h : {ω : Configuration d | x ∈ Q ∧ P (finiteBoxCluster ω Q x)} =
        ⋃ C : Finset (Vertex d), ⋃ (_ : P C), {ω | finiteBoxCluster ω Q x = C} := by
      ext ω
      simp only [Set.mem_iUnion, exists_prop]
      constructor
      · rintro ⟨-, hP⟩
        exact ⟨_, hP, rfl⟩
      · rintro ⟨C, hP, hC⟩
        refine ⟨hx, ?_⟩
        rw [hC]
        exact hP
    rw [h]
    exact MeasurableSet.iUnion fun C => MeasurableSet.iUnion fun _ =>
      measurableSet_clusterReveal_event Q C x hx
  · have h : {ω : Configuration d | x ∈ Q ∧ P (finiteBoxCluster ω Q x)} = ∅ := by
      ext ω
      simp [hx]
    rw [h]
    exact MeasurableSet.empty

lemma measurableSet_badPoint {d : ℕ} {ι : Type*} (Q : Finset (Vertex d))
    (P : Finset (Vertex d) → Prop) (face : ι → Finset (Vertex d))
    (R : Configuration d → ι → Finset (Vertex d)) (i : ι) (x : Vertex d)
    (hR : MeasurableSet {ω | x ∈ R ω i}) :
    MeasurableSet
      {ω | x ∈ (((filteredClusterFamily ω Q P).biUnion id) ∩ face i) \ R ω i} := by
  have h : {ω | x ∈ (((filteredClusterFamily ω Q P).biUnion id) ∩ face i) \ R ω i} =
      {ω : Configuration d | x ∈ Q ∧ P (finiteBoxCluster ω Q x)} ∩
        ({_ω : Configuration d | x ∈ face i} ∩ {ω | x ∈ R ω i}ᶜ) := by
    ext ω
    constructor
    · intro hω
      have h1 := Finset.mem_sdiff.mp hω
      have h2 := Finset.mem_inter.mp h1.1
      exact ⟨(mem_filtered_biUnion_iff ω Q P x).mp h2.1, h2.2, h1.2⟩
    · rintro ⟨h1, h2, h3⟩
      exact Finset.mem_sdiff.mpr
        ⟨Finset.mem_inter.mpr ⟨(mem_filtered_biUnion_iff ω Q P x).mpr h1, h2⟩, h3⟩
  rw [h]
  refine (measurableSet_clusterProp Q P x).inter (MeasurableSet.inter ?_ hR.compl)
  by_cases hxf : x ∈ face i
  · simp [hxf]
  · simp [hxf]

/-- prop.regular_cube on actual clusters: neopzmk from the spanning-window rate,
bad-set measurability reduced to measurability of the regular-point sets.
CONDITIONAL on the rate, prop.choice_c and `hR`. -/
theorem cube_not_regular_le_of_rate_meas {d : ℕ} {φ ι : Type*} [Fintype ι] (p : unitInterval)
    (Q core : Finset (Vertex d)) (hcore : core ⊆ Q) (P0 : Finset (Vertex d) → Prop)
    (face : ι → Finset (Vertex d)) (R : Configuration d → ι → Finset (Vertex d))
    (faces : φ → Finset (Vertex d)) {wa wb a s r : ℝ} (ha : 0 < a) (hs : 0 < s)
    {ε η : ℝ≥0∞}
    (hrate : (percolation d p).real {ω | ((selectedPropertyComponents Q core
      (regularCubeWindowProperty faces P0 face s wa wb) ω).card : ℝ) ≤ a} ≤ r)
    (hr : ENNReal.ofReal r ≤ ε / 2)
    (hR : ∀ i, ∀ x ∈ face i, MeasurableSet {ω | x ∈ R ω i})
    (hbad : ∀ i, ∫⁻ ω, (badCount (filteredClusterFamily ω Q P0) face (R ω) i : ℝ≥0∞)
      ∂percolation d p ≤ η)
    (hη : (Fintype.card ι : ℝ≥0∞) * η / ENNReal.ofReal ((a / 2) * (s / 2)) ≤ ε / 2) :
    percolation d p
      {ω | (regularCount (filteredClusterFamily ω Q P0) core face (R ω) s : ℝ) < a / 2} ≤ ε :=
  cube_not_regular_le_of_rate p Q core hcore P0 face R faces ha hs hrate hr
    (fun i x hx => measurableSet_badPoint Q P0 face R i x (hR i x hx)) hbad hη

end NearCritical
