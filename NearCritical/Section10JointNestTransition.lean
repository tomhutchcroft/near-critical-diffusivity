module

public import NearCritical.Section10RepresentativeTransition

@[expose] public section
noncomputable section
namespace NearCritical.Section10
open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

variable {α : Type*} [Fintype α] [MeasurableSpace (Finset α)]
  [MeasurableSingletonClass (Finset α)]

/-- Retain the tube sample together with its uniformly selected next nest. -/
def jointNestTubeTransition {d : ℕ} (p : unitInterval) (T : Finset (Bond d))
    (success : (T → Bool) → Prop) (offspring : (T → Bool) → Finset α) (k : ℕ) :
    Measure ((T → Bool) × Finset α) :=
  (Measure.pi (fun _ : T => bernoulliMeasure true false p)).bind
    (fun ξ => (survivingNestStepSelection (success ξ) (offspring ξ) k).map
      (fun nest => (ξ, nest)))

/-- Failed tube samples, non-offspring choices, and wrong nest sizes all
have zero mass under the joint transition. -/
theorem jointNestTubeTransition_invalid {d : ℕ} (p : unitInterval)
    (T : Finset (Bond d)) (success : (T → Bool) → Prop)
    (offspring : (T → Bool) → Finset α) (k : ℕ) :
    jointNestTubeTransition p T success offspring k
      {z | ¬ (success z.1 ∧ z.2 ⊆ offspring z.1 ∧ z.2.card = k)} = 0 := by
  let bad := {z : (T → Bool) × Finset α |
    ¬ (success z.1 ∧ z.2 ⊆ offspring z.1 ∧ z.2.card = k)}
  have hbad : MeasurableSet bad := (Set.to_countable _).measurableSet
  have hf : Measurable (fun ξ =>
      (survivingNestStepSelection (success ξ) (offspring ξ) k).map
        (fun nest => (ξ, nest))) := measurable_of_countable _
  rw [jointNestTubeTransition, Measure.bind_apply hbad hf.aemeasurable]
  have hz (ξ : T → Bool) :
      (survivingNestStepSelection (success ξ) (offspring ξ) k).map
        (fun nest => (ξ, nest)) bad = 0 := by
    have hmap : Measurable (fun nest : Finset α => (ξ, nest)) :=
      measurable_const.prodMk measurable_id
    rw [Measure.map_apply hmap hbad]
    unfold survivingNestStepSelection nestStepSelection
    split_ifs with hs hk <;> try simp
    rw [uniformNestChoice_apply]
    have he : ((offspring ξ).powersetCard k).filter
        (fun nest => nest ∈ (fun nest => (ξ, nest)) ⁻¹' bad) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro nest hn
      obtain ⟨hn, hbadnest⟩ := Finset.mem_filter.mp hn
      have hnest := Finset.mem_powersetCard.mp hn
      change ¬ (success ξ ∧ nest ⊆ offspring ξ ∧ nest.card = k) at hbadnest
      exact hbadnest ⟨hs, hnest.1, hnest.2⟩
    rw [he]
    simp
  simp_rw [hz]
  simp

end NearCritical.Section10
