module

public import NearCritical.RegularCubeProbability
public import NearCritical.FiniteClusterFamily

/-! prop.regular_cube for ACTUAL percolation clusters: `Ks ω` is the project's
`filteredClusterFamily ω Q P` (clusters of the cube `Q` with property `P`, e.g.
meeting `Λ_{c n}`), whose disjointness is PROVED (`finiteClusterFamily_disjoint`).
Measurability of the bad counts is reduced to per-vertex membership events.
Inputs still explicit: Lemma neopzmk (spanning count) and prop.choice_c
(first moment of non-regular boundary points). -/

@[expose] public section
noncomputable section

namespace NearCritical

open MeasureTheory Finset
open scoped ENNReal Classical

attribute [local instance 100000] Classical.propDecidable

theorem measurable_card_of_mem {Ω V : Type*} [MeasurableSpace Ω] (U : Finset V)
    (B : Ω → Finset V) (hBU : ∀ ω, B ω ⊆ U) (hm : ∀ x ∈ U, MeasurableSet {ω | x ∈ B ω}) :
    Measurable (fun ω => ((B ω).card : ℝ≥0∞)) := by
  have heq : (fun ω => ((B ω).card : ℝ≥0∞)) =
      fun ω => ∑ x ∈ U, ({ω' | x ∈ B ω'} : Set Ω).indicator (fun _ => (1 : ℝ≥0∞)) ω := by
    funext ω
    have hf : U.filter (fun x => x ∈ B ω) = B ω := by
      ext x
      simp only [mem_filter]
      exact ⟨fun h => h.2, fun h => ⟨hBU ω h, h⟩⟩
    rw [← hf, card_filter]
    push_cast
    refine sum_congr rfl fun x _ => ?_
    by_cases hx : x ∈ B ω <;> simp [Set.indicator, hx]
  rw [heq]
  exact Finset.measurable_sum _ fun x hx => measurable_const.indicator (hm x hx)

theorem cube_not_regular_le {d : ℕ} {ι : Type*} [Fintype ι] (p : unitInterval)
    (Q core : Finset (Vertex d)) (P : Finset (Vertex d) → Prop) (face : ι → Finset (Vertex d))
    (R : Configuration d → ι → Finset (Vertex d)) {a s : ℝ} (ha : 0 < a) (hs : 0 < s)
    {ε η : ℝ≥0∞}
    (hspan : percolation d p
      {ω | (spanningCount (filteredClusterFamily ω Q P) core face s : ℝ) < a} ≤ ε / 2)
    (hm : ∀ i, ∀ x ∈ face i, MeasurableSet
      {ω | x ∈ (((filteredClusterFamily ω Q P).biUnion id) ∩ face i) \ R ω i})
    (hbad : ∀ i, ∫⁻ ω, (badCount (filteredClusterFamily ω Q P) face (R ω) i : ℝ≥0∞)
      ∂percolation d p ≤ η)
    (hη : (Fintype.card ι : ℝ≥0∞) * η / ENNReal.ofReal ((a / 2) * (s / 2)) ≤ ε / 2) :
    percolation d p
      {ω | (regularCount (filteredClusterFamily ω Q P) core face (R ω) s : ℝ) < a / 2} ≤ ε :=
  regular_cube_not_regular_le (percolation d p) (fun ω => filteredClusterFamily ω Q P)
    (fun ω C hC E hE hne => finiteClusterFamily_disjoint ω Q (mem_filter.1 hC).1
      (mem_filter.1 hE).1 hne)
    core face R ha hs hspan
    (fun i => measurable_card_of_mem (face i)
      (fun ω => (((filteredClusterFamily ω Q P).biUnion id) ∩ face i) \ R ω i)
      (fun ω => sdiff_subset.trans inter_subset_right) (hm i))
    hbad hη

end NearCritical
