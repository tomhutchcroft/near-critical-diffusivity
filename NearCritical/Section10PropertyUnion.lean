module

public import NearCritical.Section10PreGoodCandidates

/-! Step 1 of `prop.proba.pregood`: the property probability from three
failure bounds.

`StepOneProperty` is the conjunction of the diameter bound, the split-face
lower counts and the face upper counts. `stepOne_property_of_failures`: if,
on the spanning event of a root `x`, each of the three conditions fails with
probability at most `a_i P[spanning]`, then

  `(1 - a₁ - a₂ - a₃) P[spanning] <= P[StepOneProperty and spanning]`,

which is the hypothesis `hproperty` of `hcand_of_raw` with
`delta = 1 - a₁ - a₂ - a₃`. No measurability is needed.

The three failure bounds are the paper's: the diameter (lem.spanning.diam,
from the cited longest-path moment), the upper face counts (Markov, from the
cited boundary first moment) and the lower split-face counts (the
`delta n^2` argument). They are hypotheses here.
-/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open MeasureTheory
open scoped Classical

lemma measure_le_of_three_failures {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] (S : Set Ω) (A B C : Ω → Prop) :
    μ.real S ≤ μ.real ({ω | A ω ∧ B ω ∧ C ω} ∩ S) + μ.real (S ∩ {ω | ¬ A ω}) +
      μ.real (S ∩ {ω | ¬ B ω}) + μ.real (S ∩ {ω | ¬ C ω}) := by
  have hsub : S ⊆ (({ω | A ω ∧ B ω ∧ C ω} ∩ S) ∪ (S ∩ {ω | ¬ A ω})) ∪
      (S ∩ {ω | ¬ B ω}) ∪ (S ∩ {ω | ¬ C ω}) := by
    intro ω hω
    by_cases hA : A ω
    · by_cases hB : B ω
      · by_cases hC : C ω
        · exact Or.inl (Or.inl (Or.inl ⟨⟨hA, hB, hC⟩, hω⟩))
        · exact Or.inr ⟨hω, hC⟩
      · exact Or.inl (Or.inr ⟨hω, hB⟩)
    · exact Or.inl (Or.inl (Or.inr ⟨hω, hA⟩))
  have h1 := measureReal_mono (μ := μ) hsub (measure_ne_top μ _)
  have h2 := measureReal_union_le (μ := μ)
    ((({ω | A ω ∧ B ω ∧ C ω} ∩ S) ∪ (S ∩ {ω | ¬ A ω})) ∪ (S ∩ {ω | ¬ B ω}))
    (S ∩ {ω | ¬ C ω})
  have h3 := measureReal_union_le (μ := μ)
    (({ω | A ω ∧ B ω ∧ C ω} ∩ S) ∪ (S ∩ {ω | ¬ A ω})) (S ∩ {ω | ¬ B ω})
  have h4 := measureReal_union_le (μ := μ)
    ({ω | A ω ∧ B ω ∧ C ω} ∩ S) (S ∩ {ω | ¬ A ω})
  linarith

/-- **Property probability of Step 1 from the three failure bounds.** -/
theorem stepOne_property_of_failures {d : ℕ} (p : unitInterval) (typ : TypicalParameters)
    (t : ℕ) (z : Vertex d) (U : Finset (Vertex d)) (x : Vertex d)
    (S : Set (Configuration d)) {a₁ a₂ a₃ : ℝ}
    (hdiam : (percolation d p).real (S ∩ {ω | ¬
        ((spanningFaceDiameter
          (restrictedGraph ω (finiteBoxCluster ω U x : Set (Vertex d)))
          (finiteBoxCluster ω U x) (typicalFace t z) : ℝ) ≤
          typ.diameterUpper * (2 * (t : ℝ)) ^ 2)}) ≤ a₁ * (percolation d p).real S)
    (hlow : (percolation d p).real (S ∩ {ω | ¬ ∀ i : (Fin d × Bool) × Bool,
        2 * (typ.boundaryLower * (2 * (t : ℝ)) ^ 2) ≤
          ((finiteBoxCluster ω U x ∩ typPatch t z i).card : ℝ)}) ≤
      a₂ * (percolation d p).real S)
    (hup : (percolation d p).real (S ∩ {ω | ¬ ∀ face : Fin d × Bool,
        ((finiteBoxCluster ω U x ∩ typicalFace t z face).card : ℝ) ≤
          typ.boundaryUpper * (2 * (t : ℝ)) ^ 2}) ≤ a₃ * (percolation d p).real S) :
    (1 - a₁ - a₂ - a₃) * (percolation d p).real S ≤
      (percolation d p).real
        ({ω | rootedClusterProperty U x (StepOneProperty typ t z) ω} ∩ S) := by
  have h := measure_le_of_three_failures (percolation d p) S
    (fun ω => (spanningFaceDiameter
        (restrictedGraph ω (finiteBoxCluster ω U x : Set (Vertex d)))
        (finiteBoxCluster ω U x) (typicalFace t z) : ℝ) ≤
        typ.diameterUpper * (2 * (t : ℝ)) ^ 2)
    (fun ω => ∀ i : (Fin d × Bool) × Bool,
        2 * (typ.boundaryLower * (2 * (t : ℝ)) ^ 2) ≤
          ((finiteBoxCluster ω U x ∩ typPatch t z i).card : ℝ))
    (fun ω => ∀ face : Fin d × Bool,
        ((finiteBoxCluster ω U x ∩ typicalFace t z face).card : ℝ) ≤
          typ.boundaryUpper * (2 * (t : ℝ)) ^ 2)
  have hset : {ω : Configuration d |
        (spanningFaceDiameter
          (restrictedGraph ω (finiteBoxCluster ω U x : Set (Vertex d)))
          (finiteBoxCluster ω U x) (typicalFace t z) : ℝ) ≤
          typ.diameterUpper * (2 * (t : ℝ)) ^ 2 ∧
        (∀ i : (Fin d × Bool) × Bool,
          2 * (typ.boundaryLower * (2 * (t : ℝ)) ^ 2) ≤
            ((finiteBoxCluster ω U x ∩ typPatch t z i).card : ℝ)) ∧
        ∀ face : Fin d × Bool,
          ((finiteBoxCluster ω U x ∩ typicalFace t z face).card : ℝ) ≤
            typ.boundaryUpper * (2 * (t : ℝ)) ^ 2} =
      {ω | rootedClusterProperty U x (StepOneProperty typ t z) ω} := rfl
  rw [hset] at h
  linarith

end NearCritical.Section10
