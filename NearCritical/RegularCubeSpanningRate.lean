module

public import NearCritical.RegularCubeConcrete
public import NearCritical.ClusterSpanningCountMean
public import NearCritical.ClusterDistinctCount

/-! Lemma neopzmk input of prop.regular_cube from the spanning-window count.

The window property is chosen as: the cluster satisfies `P0`, has at least `s`
points on every face `face i`, and the window conditions. Every selected
component that meets `core` is then counted by `spanningCount`
(`selected_card_le_spanningCount`, deterministic). So a lower-tail rate for the
selected count, which is exactly the conclusion shape of
`critical_spanningWindow_distinct_failure_rate`, bounds `ℙ[spanningCount < t]`.
`cube_not_regular_le_of_rate` is prop.regular_cube with hspan replaced by that
rate. prop.choice_c (`hbad`) stays explicit. -/

@[expose] public section
noncomputable section

namespace NearCritical

open MeasureTheory Finset
open scoped ENNReal Classical

attribute [local instance 100000] Classical.propDecidable

/-- The window property carrying `P0` and face mass `≥ s` on each face. -/
def regularCubeWindowProperty {d : ℕ} {φ ι : Type*} (faces : φ → Finset (Vertex d))
    (P0 : Finset (Vertex d) → Prop) (face : ι → Finset (Vertex d)) (s a b : ℝ) :
    SimpleGraph (Vertex d) → Finset (Vertex d) → Prop :=
  spanningWindowProperty faces (fun _ C => P0 C ∧ ∀ i, s ≤ ((C ∩ face i).card : ℝ)) a b

theorem selected_card_le_spanningCount {d : ℕ} {φ ι : Type*} [Fintype ι]
    (ω : Configuration d) (Q core : Finset (Vertex d)) (hcore : core ⊆ Q)
    (P0 : Finset (Vertex d) → Prop) (face : ι → Finset (Vertex d)) (s : ℝ)
    (faces : φ → Finset (Vertex d)) (a b : ℝ) :
    (selectedPropertyComponents Q core (regularCubeWindowProperty faces P0 face s a b) ω).card ≤
      spanningCount (filteredClusterFamily ω Q P0) core face s := by
  rw [selectedPropertyComponents_eq_filtered_family Q core hcore]
  unfold spanningCount
  apply Finset.card_le_card
  intro C hC
  simp only [filteredClusterFamily] at hC
  obtain ⟨hCF, ⟨⟨hP0, hface⟩, -⟩, hmeet⟩ := Finset.mem_filter.mp hC
  simp only [filteredClusterFamily, Finset.mem_filter]
  refine ⟨⟨hCF, hP0⟩, ?_, ?_⟩
  · convert hmeet
  · convert hface

theorem spanningCount_lt_le_of_rate {d : ℕ} {φ ι : Type*} [Fintype ι] (p : unitInterval)
    (Q core : Finset (Vertex d)) (hcore : core ⊆ Q)
    (P0 : Finset (Vertex d) → Prop) (face : ι → Finset (Vertex d)) (s : ℝ)
    (faces : φ → Finset (Vertex d)) (a b t r : ℝ)
    (hrate : (percolation d p).real {ω | ((selectedPropertyComponents Q core
      (regularCubeWindowProperty faces P0 face s a b) ω).card : ℝ) ≤ t} ≤ r) :
    percolation d p {ω | (spanningCount (filteredClusterFamily ω Q P0) core face s : ℝ) < t} ≤
      ENNReal.ofReal r := by
  have hsub : {ω | (spanningCount (filteredClusterFamily ω Q P0) core face s : ℝ) < t} ⊆
      {ω | ((selectedPropertyComponents Q core
        (regularCubeWindowProperty faces P0 face s a b) ω).card : ℝ) ≤ t} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω ⊢
    have h1 := selected_card_le_spanningCount ω Q core hcore P0 face s faces a b
    have h2 : ((selectedPropertyComponents Q core
        (regularCubeWindowProperty faces P0 face s a b) ω).card : ℝ) ≤
        (spanningCount (filteredClusterFamily ω Q P0) core face s : ℝ) := by
      exact_mod_cast h1
    linarith
  have hr0 : 0 ≤ r := le_trans measureReal_nonneg hrate
  refine le_trans (measure_mono hsub) ?_
  exact (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) hr0).2 hrate

/-- prop.regular_cube on actual clusters with Lemma neopzmk supplied by a
selected spanning-window count rate. CONDITIONAL on that rate and prop.choice_c. -/
theorem cube_not_regular_le_of_rate {d : ℕ} {φ ι : Type*} [Fintype ι] (p : unitInterval)
    (Q core : Finset (Vertex d)) (hcore : core ⊆ Q) (P0 : Finset (Vertex d) → Prop)
    (face : ι → Finset (Vertex d)) (R : Configuration d → ι → Finset (Vertex d))
    (faces : φ → Finset (Vertex d)) {wa wb a s r : ℝ} (ha : 0 < a) (hs : 0 < s)
    {ε η : ℝ≥0∞}
    (hrate : (percolation d p).real {ω | ((selectedPropertyComponents Q core
      (regularCubeWindowProperty faces P0 face s wa wb) ω).card : ℝ) ≤ a} ≤ r)
    (hr : ENNReal.ofReal r ≤ ε / 2)
    (hm : ∀ i, ∀ x ∈ face i, MeasurableSet
      {ω | x ∈ (((filteredClusterFamily ω Q P0).biUnion id) ∩ face i) \ R ω i})
    (hbad : ∀ i, ∫⁻ ω, (badCount (filteredClusterFamily ω Q P0) face (R ω) i : ℝ≥0∞)
      ∂percolation d p ≤ η)
    (hη : (Fintype.card ι : ℝ≥0∞) * η / ENNReal.ofReal ((a / 2) * (s / 2)) ≤ ε / 2) :
    percolation d p
      {ω | (regularCount (filteredClusterFamily ω Q P0) core face (R ω) s : ℝ) < a / 2} ≤ ε :=
  cube_not_regular_le p Q core P0 face R ha hs
    ((spanningCount_lt_le_of_rate p Q core hcore P0 face s faces wa wb a r hrate).trans hr)
    hm hbad hη

end NearCritical
