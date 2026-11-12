module

public import NearCritical.Section10NestStepSelection
public import Mathlib.MeasureTheory.Measure.GiryMonad

@[expose] public section
noncomputable section
namespace NearCritical.Section10
open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

variable {α : Type*} [Fintype α] [MeasurableSpace (Finset α)]
  [MeasurableSingletonClass (Finset α)]

/-- The tube outcome is sampled from its Bernoulli law, followed by the
uniform next-nest choice on successful outcomes. Failed outcomes contribute zero. -/
def nestTubeTransition {d : ℕ} (p : unitInterval) (T : Finset (Bond d))
    (success : (T → Bool) → Prop) (offspring : (T → Bool) → Finset α) (k : ℕ) :
    Measure (Finset α) :=
  (Measure.pi (fun _ : T => bernoulliMeasure true false p)).bind
    (fun ξ => survivingNestStepSelection (success ξ) (offspring ξ) k)

/-- The constructed transition has exactly the probability of tube success
as its total mass. -/
theorem nestTubeTransition_mass {d : ℕ} (p : unitInterval) (T : Finset (Bond d))
    (success : (T → Bool) → Prop) (offspring : (T → Bool) → Finset α) (k : ℕ)
    (hcard : ∀ ξ, success ξ → k ≤ (offspring ξ).card) :
    nestTubeTransition p T success offspring k Set.univ =
      (Measure.pi (fun _ : T => bernoulliMeasure true false p)) {ξ | success ξ} := by
  let μ := Measure.pi (fun _ : T => bernoulliMeasure true false p)
  have hf : Measurable (fun ξ => survivingNestStepSelection (success ξ) (offspring ξ) k) :=
    measurable_of_countable _
  rw [nestTubeTransition, Measure.bind_apply MeasurableSet.univ hf.aemeasurable]
  simp_rw [survivingNestStepSelection_mass _ _ (hcard _)]
  have hm : MeasurableSet {ξ : T → Bool | success ξ} := (Set.toFinite _).measurableSet
  change (∫⁻ ξ, ({ξ | success ξ} : Set (T → Bool)).indicator (fun _ => (1 : ENNReal)) ξ ∂μ) =
    μ {ξ | success ξ}
  rw [lintegral_indicator hm]
  simp

/-- Every sampled next nest has the prescribed size. The construction also
enforces the offspring inclusion separately at each sampled tube outcome. -/
theorem nestTubeTransition_wrong_card {d : ℕ} (p : unitInterval) (T : Finset (Bond d))
    (success : (T → Bool) → Prop) (offspring : (T → Bool) → Finset α) (k : ℕ) :
    nestTubeTransition p T success offspring k {nest | nest.card ≠ k} = 0 := by
  have hf : Measurable (fun ξ => survivingNestStepSelection (success ξ) (offspring ξ) k) :=
    measurable_of_countable _
  have hm : MeasurableSet {nest : Finset α | nest.card ≠ k} :=
    (Set.to_countable _).measurableSet
  rw [nestTubeTransition, Measure.bind_apply hm hf.aemeasurable]
  have hz (ξ : T → Bool) :
      survivingNestStepSelection (success ξ) (offspring ξ) k {nest | nest.card ≠ k} = 0 := by
    unfold survivingNestStepSelection nestStepSelection
    split_ifs <;> try simp
    rw [uniformNestChoice_apply]
    have he : ((offspring ξ).powersetCard k).filter (fun nest => nest ∈ {nest | nest.card ≠ k}) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro nest hn
      obtain ⟨hn, hbad⟩ := Finset.mem_filter.mp hn
      exact hbad (Finset.mem_powersetCard.mp hn).2
    simp only [Set.mem_setOf_eq] at he ⊢
    rw [he]
    simp
  simp_rw [hz]
  simp

end NearCritical.Section10
