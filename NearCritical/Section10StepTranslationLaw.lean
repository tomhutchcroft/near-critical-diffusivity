module

public import NearCritical.Section10StepTranslation

/-! Translation of opened pivotal pairs, and invariance of the coupled law.

* `orientedLatticePairs_translate`, `sprinkledPivotalPairs_translate`,
  `sprinkledPivotalPairs_nonempty_translate`: the opened pivotal pairs of a step
  at `a` are the shifted pairs of the same step at the origin for the
  translated configurations.
* `sprinkleOr_translate`: translation commutes with `z.1 OR z.2`.
* `coupled_integral_translate`: the coupled law is invariant under translating
  both layers.

Together these transfer a probability statement about a step at the origin
(as in the Section 9 theorems) to the step at any lattice point.
-/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open MeasureTheory
open scoped Classical

theorem orientedLatticePairs_translate {d : ℕ} (a : Vertex d) (M : Finset (Vertex d)) :
    orientedLatticePairs (translateSites a M) = (orientedLatticePairs M).image (shiftPair a) := by
  ext e
  rw [Finset.mem_image]
  constructor
  · intro he
    obtain ⟨h1, h2, hadj⟩ := (mem_orientedLatticePairs (translateSites a M) e.1 e.2).mp he
    obtain ⟨x, hx, hx'⟩ := (mem_translateSites_iff a M e.1).mp h1
    obtain ⟨y, hy, hy'⟩ := (mem_translateSites_iff a M e.2).mp h2
    refine ⟨(x, y), (mem_orientedLatticePairs M x y).mpr ⟨hx, hy, ?_⟩, ?_⟩
    · rw [← hx', ← hy'] at hadj
      exact (latticeAdj_translate a x y).mp hadj
    · exact Prod.ext hx' hy'
  · rintro ⟨e0, he0, rfl⟩
    obtain ⟨h1, h2, hadj⟩ := (mem_orientedLatticePairs M e0.1 e0.2).mp he0
    exact (mem_orientedLatticePairs (translateSites a M) _ _).mpr
      ⟨(mem_translateSites a M e0.1).mpr h1, (mem_translateSites a M e0.2).mpr h2,
        (latticeAdj_translate a e0.1 e0.2).mpr hadj⟩

theorem sprinkledPivotalPairs_translate {d : ℕ} (a : Vertex d) (ω η : Configuration d)
    (E : Finset (Vertex d × Vertex d)) (L R Q₁ F₁ Q₃ F₃ A B : Finset (Vertex d)) :
    sprinkledPivotalPairs ω η (E.image (shiftPair a)) (translateSites a L) (translateSites a R)
        (translateSites a Q₁) (translateSites a F₁) (translateSites a Q₃)
        (translateSites a F₃) (translateSites a A) (translateSites a B) =
      (sprinkledPivotalPairs (translateConfiguration a ω) (translateConfiguration a η) E
        L R Q₁ F₁ Q₃ F₃ A B).image (shiftPair a) := by
  ext e
  simp only [sprinkledPivotalPairs, sprinklingPivotalPairs, Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro ⟨⟨⟨e0, he0, rfl⟩, hp⟩, ho⟩
    exact ⟨e0, ⟨⟨he0, (sprinklingPivotalPair_translate a ω L R Q₁ F₁ Q₃ F₃ A B e0).mp hp⟩,
      (openGraph_translate_adj a η e0.1 e0.2).mpr ho⟩, rfl⟩
  · rintro ⟨e0, ⟨⟨he0, hp⟩, ho⟩, rfl⟩
    exact ⟨⟨⟨e0, he0, rfl⟩, (sprinklingPivotalPair_translate a ω L R Q₁ F₁ Q₃ F₃ A B e0).mpr hp⟩,
      (openGraph_translate_adj a η e0.1 e0.2).mp ho⟩

theorem sprinkledPivotalPairs_nonempty_translate {d : ℕ} (a : Vertex d)
    (ω η : Configuration d) (M L R Q₁ F₁ Q₃ F₃ A B : Finset (Vertex d)) :
    (sprinkledPivotalPairs ω η (orientedLatticePairs (translateSites a M))
        (translateSites a L) (translateSites a R) (translateSites a Q₁) (translateSites a F₁)
        (translateSites a Q₃) (translateSites a F₃) (translateSites a A)
        (translateSites a B)).Nonempty ↔
      (sprinkledPivotalPairs (translateConfiguration a ω) (translateConfiguration a η)
        (orientedLatticePairs M) L R Q₁ F₁ Q₃ F₃ A B).Nonempty := by
  rw [orientedLatticePairs_translate, sprinkledPivotalPairs_translate, Finset.image_nonempty]

lemma sprinkleOr_translate {d : ℕ} (a : Vertex d) (ω ζ : Configuration d) :
    translateConfiguration a (sprinkleOrConfiguration ω ζ) =
      sprinkleOrConfiguration (translateConfiguration a ω) (translateConfiguration a ζ) := rfl

/-- The coupled law is invariant under translating both layers. -/
theorem coupled_integral_translate {d : ℕ} (p q : unitInterval) (a : Vertex d)
    (f : Configuration d × Configuration d → ℝ) (hf : Measurable f) :
    (∫ z, f (translateConfiguration a z.1, translateConfiguration a z.2)
      ∂((percolation d p).prod (percolation d q))) =
      ∫ z, f z ∂((percolation d p).prod (percolation d q)) := by
  have hmap : ((percolation d p).prod (percolation d q)).map
      (Prod.map (translateConfiguration a) (translateConfiguration a)) =
      (percolation d p).prod (percolation d q) := by
    rw [← Measure.map_prod_map _ _ (measurable_translateConfiguration a)
      (measurable_translateConfiguration a), percolation_map_translation,
      percolation_map_translation]
  have h := integral_map (μ := (percolation d p).prod (percolation d q))
    ((measurable_translateConfiguration a).prodMap
      (measurable_translateConfiguration a)).aemeasurable
    (f := f) hf.aestronglyMeasurable
  rw [hmap] at h
  exact h.symm

end NearCritical.Section10
