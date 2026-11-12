module

public import NearCritical.Section10SpreadBridgeEntry
public import NearCritical.Section10StepTranslationLaw

/-! Transfer the H2 and H3 events to the actual translated tubes of a route. -/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open MeasureTheory Set
open scoped Classical

/-- Translating the geometry translates the full bridge vertex set. -/
theorem section9SprinklingCluster_translate {d : ℕ} (a : Vertex d) (ω η : Configuration d)
    (M L R Q₁ F₁ Q₃ F₃ A B : Finset (Vertex d)) :
    section9SprinklingCluster ω η (orientedLatticePairs (translateSites a M))
      (translateSites a L) (translateSites a R) (translateSites a Q₁) (translateSites a F₁)
      (translateSites a Q₃) (translateSites a F₃) (translateSites a A) (translateSites a B) =
    translateSites a (section9SprinklingCluster (translateConfiguration a ω) (translateConfiguration a η)
      (orientedLatticePairs M) L R Q₁ F₁ Q₃ F₃ A B) := by
  ext z
  rw [mem_section9SprinklingCluster, mem_translateSites_iff]
  rw [orientedLatticePairs_translate, sprinkledPivotalPairs_translate]
  constructor
  · rintro ⟨e, he, hz⟩
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp he
    dsimp only [shiftPair, Prod.fst, Prod.snd] at hz
    rw [sprinklingUnexploredCluster_translate, sprinklingUnexploredCluster_translate] at hz
    rcases hz with hl | hr
    · obtain ⟨u, hu, rfl⟩ := (mem_translateSites_iff _ _ _).mp hl
      exact ⟨u, (mem_section9SprinklingCluster _ _ _ _ _ _ _ _ _ _ _ u).mpr ⟨f, hf, Or.inl hu⟩, rfl⟩
    · obtain ⟨u, hu, rfl⟩ := (mem_translateSites_iff _ _ _).mp hr
      exact ⟨u, (mem_section9SprinklingCluster _ _ _ _ _ _ _ _ _ _ _ u).mpr ⟨f, hf, Or.inr hu⟩, rfl⟩
  · rintro ⟨u, hu, rfl⟩
    obtain ⟨f, hf, hu⟩ := (mem_section9SprinklingCluster _ _ _ _ _ _ _ _ _ _ _ u).mp hu
    refine ⟨shiftPair a f, Finset.mem_image.mpr ⟨f, hf, rfl⟩, ?_⟩
    dsimp only [shiftPair, Prod.fst, Prod.snd]
    rw [sprinklingUnexploredCluster_translate, sprinklingUnexploredCluster_translate]
    rcases hu with hl | hr
    · exact Or.inl ((mem_translateSites_iff _ _ _).mpr ⟨u, hl, rfl⟩)
    · exact Or.inr ((mem_translateSites_iff _ _ _).mpr ⟨u, hr, rfl⟩)

/-- The H3 probability on a translated tube equals the origin probability
under the actual pair of independent Bernoulli fields. -/
theorem rawBridgeMeet_translate_probability {d : ℕ} (p q : unitInterval) (a : Vertex d)
    (M L R Q₁ F₁ Q₃ F₃ X Y B : Finset (Vertex d)) :
    let C (X : Finset (Vertex d)) (z : Configuration d × Configuration d) :=
      section9SprinklingCluster z.1 z.2 (orientedLatticePairs M) L R Q₁ F₁ Q₃ F₃ X B
    let C' (X : Finset (Vertex d)) (z : Configuration d × Configuration d) :=
      section9SprinklingCluster z.1 z.2 (orientedLatticePairs (translateSites a M))
        (translateSites a L) (translateSites a R) (translateSites a Q₁) (translateSites a F₁)
        (translateSites a Q₃) (translateSites a F₃) (translateSites a X) (translateSites a B)
    let μ := (percolation d p).prod (percolation d q)
    μ.real {z | (C' X z ∩ C' Y z).Nonempty} = μ.real {z | (C X z ∩ C Y z).Nonempty} := by
  intro C C' μ
  let f := Prod.map (translateConfiguration a) (translateConfiguration a)
  let F := {z | (C X z ∩ C Y z).Nonempty}
  have hF : MeasurableSet F := (rawBridgeMeet_readsOnly M L R Q₁ F₁ Q₃ F₃ X Y B).measurableSet
  have heq : {z | (C' X z ∩ C' Y z).Nonempty} = f ⁻¹' F := by
    ext z
    change (C' X z ∩ C' Y z).Nonempty ↔ (C X (f z) ∩ C Y (f z)).Nonempty
    have hc (A : Finset (Vertex d)) : C' A z = translateSites a (C A (f z)) :=
      section9SprinklingCluster_translate a z.1 z.2 M L R Q₁ F₁ Q₃ F₃ A B
    rw [hc, hc, translateSites_inter_nonempty]
  have hf : Measurable f :=
    (measurable_translateConfiguration a).prodMap (measurable_translateConfiguration a)
  have hmap : μ.map f = μ := by
    dsimp only [μ, f]
    rw [← Measure.map_prod_map _ _ (measurable_translateConfiguration a)
      (measurable_translateConfiguration a), percolation_map_translation, percolation_map_translation]
  rw [heq, ← map_measureReal_apply hf hF, hmap]

end NearCritical.Section10
