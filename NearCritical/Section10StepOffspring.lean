module

public import NearCritical.Section10OriginOffspring
public import NearCritical.Section10StepTranslationLaw

/-! The offspring lower bound at a translated step.

* `openedCount_translate_prob`: under the product law, the opened-target count
  event for translated data has the same probability as for the original data.
* `translated_offspring_failure_le`: for a step whose tubes, cubes, revealed
  sets and source set are the translates by `a` of origin data, the offspring
  failure probability is at most `eps` as soon as the origin count event (with
  target patches pulled back by `-a`) has probability at least `1 - eps`.
-/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open MeasureTheory
open scoped Classical

lemma translateSites_neg_cancel {d : ℕ} (a : Vertex d) (U : Finset (Vertex d)) :
    translateSites a (translateSites (-a) U) = U := by
  unfold translateSites
  rw [Finset.image_image]
  have h : ((fun x : Vertex d => a + x) ∘ fun x : Vertex d => -a + x) = id := by
    funext x
    simp
  rw [h, Finset.image_id]

theorem openedCount_translate_prob {d : ℕ} (p q : unitInterval) (a : Vertex d)
    (M L R Q₁ F₁ Q₃ F₃ A : Finset (Vertex d)) {ι : Type*} (I : Finset ι)
    (targets : ι → Finset (Vertex d)) (m : ℕ) :
    ((percolation d p).prod (percolation d q)).real
      {z : Configuration d × Configuration d | (m : ℝ) < ((I.filter fun j =>
        (sprinkledPivotalPairs z.1 (sprinkleOrConfiguration z.1 z.2)
          (orientedLatticePairs (translateSites a M)) (translateSites a L) (translateSites a R)
          (translateSites a Q₁) (translateSites a F₁) (translateSites a Q₃)
          (translateSites a F₃) (translateSites a A)
          (translateSites a (targets j))).Nonempty).card : ℝ)} =
    ((percolation d p).prod (percolation d q)).real
      {z : Configuration d × Configuration d | (m : ℝ) < ((I.filter fun j =>
        (sprinkledPivotalPairs z.1 (sprinkleOrConfiguration z.1 z.2)
          (orientedLatticePairs M) L R Q₁ F₁ Q₃ F₃ A (targets j)).Nonempty).card : ℝ)} := by
  set S₀ : Set (Configuration d × Configuration d) := {z | (m : ℝ) < ((I.filter fun j =>
    (sprinkledPivotalPairs z.1 (sprinkleOrConfiguration z.1 z.2)
      (orientedLatticePairs M) L R Q₁ F₁ Q₃ F₃ A (targets j)).Nonempty).card : ℝ)} with hS₀
  have hmeas : MeasurableSet S₀ := by
    have hP : ReadsOnly (stepReadSet M L R Q₁ F₁ Q₃ F₃)
        (fun z : Configuration d × Configuration d => (m : ℝ) < ((I.filter fun j =>
          ((stepView M L R Q₁ F₁ Q₃ F₃ z).2.2.1 A (targets j)).Nonempty).card : ℝ)) :=
      (stepView_readsOnly M L R Q₁ F₁ Q₃ F₃).comp (fun v => (m : ℝ) < ((I.filter fun j =>
        (v.2.2.1 A (targets j)).Nonempty).card : ℝ))
    exact hP.measurableSet
  have hpre : {z : Configuration d × Configuration d | (m : ℝ) < ((I.filter fun j =>
        (sprinkledPivotalPairs z.1 (sprinkleOrConfiguration z.1 z.2)
          (orientedLatticePairs (translateSites a M)) (translateSites a L) (translateSites a R)
          (translateSites a Q₁) (translateSites a F₁) (translateSites a Q₃)
          (translateSites a F₃) (translateSites a A)
          (translateSites a (targets j))).Nonempty).card : ℝ)} =
      {z | (translateConfiguration a z.1, translateConfiguration a z.2) ∈ S₀} := by
    ext z
    show _ ↔ (m : ℝ) < ((I.filter fun j =>
      (sprinkledPivotalPairs (translateConfiguration a z.1)
        (sprinkleOrConfiguration (translateConfiguration a z.1) (translateConfiguration a z.2))
        (orientedLatticePairs M) L R Q₁ F₁ Q₃ F₃ A (targets j)).Nonempty).card : ℝ)
    have hfil : (I.filter fun j =>
        (sprinkledPivotalPairs z.1 (sprinkleOrConfiguration z.1 z.2)
          (orientedLatticePairs (translateSites a M)) (translateSites a L) (translateSites a R)
          (translateSites a Q₁) (translateSites a F₁) (translateSites a Q₃)
          (translateSites a F₃) (translateSites a A)
          (translateSites a (targets j))).Nonempty) =
        I.filter fun j =>
          (sprinkledPivotalPairs (translateConfiguration a z.1)
            (sprinkleOrConfiguration (translateConfiguration a z.1)
              (translateConfiguration a z.2))
            (orientedLatticePairs M) L R Q₁ F₁ Q₃ F₃ A (targets j)).Nonempty := by
      refine Finset.filter_congr (fun j _ => ?_)
      rw [sprinkledPivotalPairs_nonempty_translate, sprinkleOr_translate]
    show (m : ℝ) < _ ↔ _
    rw [hfil]
  rw [hpre]
  have hint := coupled_integral_translate p q a (Set.indicator S₀ (fun _ => (1:ℝ)))
    (measurable_const.indicator hmeas)
  have hpm : MeasurableSet {z : Configuration d × Configuration d |
      (translateConfiguration a z.1, translateConfiguration a z.2) ∈ S₀} :=
    ((measurable_translateConfiguration a).comp measurable_fst |>.prodMk
      ((measurable_translateConfiguration a).comp measurable_snd)) hmeas
  have h1 : (∫ z, Set.indicator S₀ (fun _ => (1:ℝ))
      (translateConfiguration a z.1, translateConfiguration a z.2)
      ∂((percolation d p).prod (percolation d q))) =
      ((percolation d p).prod (percolation d q)).real
        {z | (translateConfiguration a z.1, translateConfiguration a z.2) ∈ S₀} := by
    have hfun : (fun z : Configuration d × Configuration d => Set.indicator S₀ (fun _ => (1:ℝ))
        (translateConfiguration a z.1, translateConfiguration a z.2)) =
        Set.indicator {z | (translateConfiguration a z.1, translateConfiguration a z.2) ∈ S₀}
          (fun _ => (1:ℝ)) := by
      funext z
      simp only [Set.indicator, Set.mem_setOf_eq]
    rw [hfun, integral_indicator_const _ hpm, smul_eq_mul, mul_one]
  have h2 : (∫ z, Set.indicator S₀ (fun _ => (1:ℝ)) z
      ∂((percolation d p).prod (percolation d q))) =
      ((percolation d p).prod (percolation d q)).real S₀ := by
    rw [integral_indicator_const _ hmeas, smul_eq_mul, mul_one]
  rw [← h1, hint, h2]

/-- **Offspring failure at a translated step.** -/
theorem translated_offspring_failure_le {d : ℕ} (p q : unitInterval) (a : Vertex d)
    (M L R Q₁ F₁ Q₃ F₃ A : Finset (Vertex d)) (cand : Finset (Finset (Vertex d)))
    (tgt : Finset (Vertex d) → Finset (Vertex d)) (N m : ℕ) (hNm : N ≤ m + 1) {ε : ℝ}
    (hopen : 1 - ε ≤ ((percolation d p).prod (percolation d q)).real
      {z : Configuration d × Configuration d | (m : ℝ) < ((cand.filter fun c =>
        (sprinkledPivotalPairs z.1 (sprinkleOrConfiguration z.1 z.2)
          (orientedLatticePairs M) L R Q₁ F₁ Q₃ F₃ A
          (translateSites (-a) (tgt c))).Nonempty).card : ℝ)}) :
    ((percolation d p).prod (percolation d q)).real
      {z : Configuration d × Configuration d |
        ¬ N ≤ (sprinklingOffspring
          (stepView (translateSites a M) (translateSites a L) (translateSites a R)
            (translateSites a Q₁) (translateSites a F₁) (translateSites a Q₃)
            (translateSites a F₃) z).1
          (stepView (translateSites a M) (translateSites a L) (translateSites a R)
            (translateSites a Q₁) (translateSites a F₁) (translateSites a Q₃)
            (translateSites a F₃) z).2.1 (translateSites a A) cand tgt
          ((stepView (translateSites a M) (translateSites a L) (translateSites a R)
            (translateSites a Q₁) (translateSites a F₁) (translateSites a Q₃)
            (translateSites a F₃) z).2.2.1 (translateSites a A)
            (sprinklingTargetBoundary cand tgt))).card} ≤ ε := by
  refine offspringFailure_le p q _ _ _ _ _ _ _ _ cand tgt N m hNm ?_
  have h := openedCount_translate_prob p q a M L R Q₁ F₁ Q₃ F₃ A cand
    (fun c => translateSites (-a) (tgt c)) m
  simp only [translateSites_neg_cancel] at h
  rw [h]
  exact hopen

end NearCritical.Section10
