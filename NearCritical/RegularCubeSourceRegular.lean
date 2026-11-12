module

public import NearCritical.RegularCubeMeasurable
public import NearCritical.NestRegularBoundary

/-! prop.regular_cube with the regular-point sets fixed to source def.regular.

`R ω i` is the set of points of `face i` that are `sourceRegularPoint` points
for the actual heart-cluster union `heartClusterUnion ω Q H`. That union is
built from finitely many actual clusters, each a countable-valued measurable
function of `ω`, so membership in `R ω i` is measurable
(`measurableSet_mem_sourceRegularFace`). This discharges `hR`.
`cube_not_regular_le_source` is prop.regular_cube with the source regularity
notion. Its remaining inputs are the spanning-window rate and prop.choice_c. -/

@[expose] public section
noncomputable section

namespace NearCritical

open MeasureTheory Finset
open scoped ENNReal Classical

attribute [local instance 100000] Classical.propDecidable

/-- Any property of a countable-valued map with measurable level sets is measurable. -/
lemma measurableSet_comp_of_countable {Ω α : Type*} [MeasurableSpace Ω] [Countable α]
    (f : Ω → α) (hf : ∀ a, MeasurableSet {ω | f ω = a}) (P : α → Prop) :
    MeasurableSet {ω | P (f ω)} := by
  have h : {ω | P (f ω)} = ⋃ a : α, ⋃ (_ : P a), {ω | f ω = a} := by
    ext ω
    simp only [Set.mem_iUnion, exists_prop]
    constructor
    · intro hP
      exact ⟨_, hP, rfl⟩
    · rintro ⟨a, hP, ha⟩
      have ha' : f ω = a := ha
      show P (f ω)
      rw [ha']
      exact hP
  rw [h]
  exact MeasurableSet.iUnion fun a => MeasurableSet.iUnion fun _ => hf a

/-- Any property of the actual heart-cluster union is a measurable event. -/
lemma measurableSet_heartClusterUnion_prop {d : ℕ} (Q H : Finset (Vertex d)) (hHQ : H ⊆ Q)
    (P : Finset (Vertex d) → Prop) :
    MeasurableSet {ω : Configuration d | P (heartClusterUnion ω Q H)} := by
  let f : Configuration d → (H → Finset (Vertex d)) := fun ω h => finiteBoxCluster ω Q h
  let Φ : (H → Finset (Vertex d)) → Finset (Vertex d) := fun g =>
    H.biUnion (fun h => if hh : h ∈ H then g ⟨h, hh⟩ else ∅)
  have hΦ : ∀ ω, heartClusterUnion ω Q H = Φ (f ω) := by
    intro ω
    ext y
    simp only [heartClusterUnion, Φ, f, Finset.mem_biUnion]
    constructor
    · rintro ⟨a, ha, hy⟩
      exact ⟨a, ha, by simpa [ha] using hy⟩
    · rintro ⟨a, ha, hy⟩
      exact ⟨a, ha, by simpa [ha] using hy⟩
  have hf : ∀ g, MeasurableSet {ω | f ω = g} := by
    intro g
    have h : {ω | f ω = g} = ⋂ h : H, {ω | finiteBoxCluster ω Q h = g h} := by
      ext ω
      simp only [Set.mem_iInter, f, funext_iff]
      try rfl
    rw [h]
    exact MeasurableSet.iInter fun h => measurableSet_clusterReveal_event Q (g h) h (hHQ h.2)
  have h := measurableSet_comp_of_countable f hf (fun g => P (Φ g))
  have h2 : {ω : Configuration d | P (heartClusterUnion ω Q H)} =
      {ω | (fun g => P (Φ g)) (f ω)} := by
    ext ω
    exact Iff.of_eq (congrArg P (hΦ ω))
  rw [h2]
  exact h

/-- Source def.regular points of `face i` for the actual heart-cluster union. -/
def sourceRegularFace {d : ℕ} {ι : Type*} (Q H S boundary : Finset (Vertex d)) (r : ℕ) (δ : ℝ)
    (face : ι → Finset (Vertex d)) (ω : Configuration d) (i : ι) : Finset (Vertex d) :=
  (face i).filter (sourceRegularPoint (heartClusterUnion ω Q H) S boundary r δ)

lemma measurableSet_mem_sourceRegularFace {d : ℕ} {ι : Type*} (Q H S boundary : Finset (Vertex d))
    (hHQ : H ⊆ Q) (r : ℕ) (δ : ℝ) (face : ι → Finset (Vertex d)) (i : ι) (x : Vertex d) :
    MeasurableSet {ω | x ∈ sourceRegularFace Q H S boundary r δ face ω i} := by
  have h : {ω | x ∈ sourceRegularFace Q H S boundary r δ face ω i} =
      {ω : Configuration d | (fun U => x ∈ face i ∧ sourceRegularPoint U S boundary r δ x)
        (heartClusterUnion ω Q H)} := by
    ext ω
    exact Finset.mem_filter
  rw [h]
  exact measurableSet_heartClusterUnion_prop Q H hHQ
    (fun U => x ∈ face i ∧ sourceRegularPoint U S boundary r δ x)

/-- prop.regular_cube on actual clusters with source def.regular points.
CONDITIONAL on the spanning-window rate (neopzmk) and prop.choice_c. -/
theorem cube_not_regular_le_source {d : ℕ} {φ ι : Type*} [Fintype ι] (p : unitInterval)
    (Q core H S boundary : Finset (Vertex d)) (hcore : core ⊆ Q) (hHQ : H ⊆ Q) (rr : ℕ) (δ : ℝ)
    (P0 : Finset (Vertex d) → Prop) (face : ι → Finset (Vertex d))
    (faces : φ → Finset (Vertex d)) {wa wb a s r : ℝ} (ha : 0 < a) (hs : 0 < s)
    {ε η : ℝ≥0∞}
    (hrate : (percolation d p).real {ω | ((selectedPropertyComponents Q core
      (regularCubeWindowProperty faces P0 face s wa wb) ω).card : ℝ) ≤ a} ≤ r)
    (hr : ENNReal.ofReal r ≤ ε / 2)
    (hbad : ∀ i, ∫⁻ ω, (badCount (filteredClusterFamily ω Q P0) face
      (sourceRegularFace Q H S boundary rr δ face ω) i : ℝ≥0∞) ∂percolation d p ≤ η)
    (hη : (Fintype.card ι : ℝ≥0∞) * η / ENNReal.ofReal ((a / 2) * (s / 2)) ≤ ε / 2) :
    percolation d p
      {ω | (regularCount (filteredClusterFamily ω Q P0) core face
        (sourceRegularFace Q H S boundary rr δ face ω) s : ℝ) < a / 2} ≤ ε :=
  cube_not_regular_le_of_rate_meas p Q core hcore P0 face
    (sourceRegularFace Q H S boundary rr δ face) faces ha hs hrate hr
    (fun i x _ => measurableSet_mem_sourceRegularFace Q H S boundary hHQ rr δ face i x) hbad hη

end NearCritical
