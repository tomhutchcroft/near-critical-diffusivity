module

public import NearCritical.NestUniformChoice
public import NearCritical.NestFreshTube

@[expose] public section
noncomputable section
namespace NearCritical.Section10
open MeasureTheory ProbabilityTheory

variable {α : Type*} [MeasurableSpace (Finset α)]
  [MeasurableSingletonClass (Finset α)]

/-- The next-nest subprobability after revealing the offspring.
This selection is available when the offspring set contains at least k elements. -/
def nestStepSelection (offspring : Finset α) (k : ℕ) : Measure (Finset α) :=
  if k ≤ offspring.card then uniformNestChoice offspring k else 0

theorem nestStepSelection_mass (offspring : Finset α) (k : ℕ) :
    nestStepSelection offspring k Set.univ = if k ≤ offspring.card then 1 else 0 := by
  unfold nestStepSelection
  split_ifs with hk
  · letI := uniformNestChoice_probability offspring k hk
    exact measure_univ
  · simp

/-- Averaging the surviving selection mass over finite reveal outcomes gives
exactly the mass of the reveals with enough offspring. -/
theorem nestStepSelection_average_mass {β : Type*} (outcomes : Finset β)
    (weight : β → ENNReal) (offspring : β → Finset α) (k : ℕ) :
    (∑ b ∈ outcomes, weight b * nestStepSelection (offspring b) k Set.univ) =
      ∑ b ∈ outcomes, if k ≤ (offspring b).card then weight b else 0 := by
  apply Finset.sum_congr rfl
  intro b _
  rw [nestStepSelection_mass]
  split_ifs <;> simp

/-- The chain samples a next nest only when the revealed bridge is typical. -/
def survivingNestStepSelection (typical : Prop) (offspring : Finset α) (k : ℕ) :
    Measure (Finset α) := by
  classical
  exact if typical then nestStepSelection offspring k else 0

theorem survivingNestStepSelection_mass {typical : Prop} (offspring : Finset α) (k : ℕ)
    (hcard : typical → k ≤ offspring.card) :
    survivingNestStepSelection typical offspring k Set.univ =
      (by classical exact if typical then 1 else 0) := by
  classical
  by_cases h : typical
  · simp [survivingNestStepSelection, h, nestStepSelection_mass, hcard h]
  · simp [survivingNestStepSelection, h]

/-- For a fixed past and sign, averaging the gated selection over the
Bernoulli tube law yields the exact success normalizer of the paper. -/
theorem survivingNestStepSelection_freshTube_mass {d : ℕ} (p : unitInterval)
    (S T : Finset (Bond d)) (success : (S → Bool) → (T → Bool) → Prop)
    (η : S → Bool) (offspring : (T → Bool) → Finset α) (k : ℕ)
    (hcard : ∀ ξ, success η ξ → k ≤ (offspring ξ).card) :
    (∫ ξ, (survivingNestStepSelection (success η ξ) (offspring ξ) k).real Set.univ
      ∂(Measure.pi (fun _ : T => bernoulliMeasure true false p))) =
      freshTubeSuccessProbability p S T success η := by
  classical
  have hm : MeasurableSet {ξ : T → Bool | success η ξ} := (Set.toFinite _).measurableSet
  have he : (fun ξ => (survivingNestStepSelection (success η ξ) (offspring ξ) k).real
      Set.univ) = ({ξ : T → Bool | success η ξ} : Set (T → Bool)).indicator
        (fun _ => (1 : ℝ)) := by
    funext ξ
    rw [Measure.real, survivingNestStepSelection_mass (offspring ξ) k (hcard ξ)]
    by_cases h : success η ξ <;> simp [Set.indicator, h]
  rw [he, integral_indicator_const _ hm, smul_eq_mul, mul_one]
  rfl

/-- Dividing the surviving transition by its positive success mass
normalizes the total next-nest mass for this fixed past and sign. -/
theorem survivingNestStepSelection_freshTube_normalized {d : ℕ} (p : unitInterval)
    (S T : Finset (Bond d)) (success : (S → Bool) → (T → Bool) → Prop)
    (η : S → Bool) (offspring : (T → Bool) → Finset α) (k : ℕ)
    (hcard : ∀ ξ, success η ξ → k ≤ (offspring ξ).card)
    (hs : 0 < freshTubeSuccessProbability p S T success η) :
    (∫ ξ, (freshTubeSuccessProbability p S T success η)⁻¹ *
      (survivingNestStepSelection (success η ξ) (offspring ξ) k).real Set.univ
      ∂(Measure.pi (fun _ : T => bernoulliMeasure true false p))) = 1 := by
  rw [integral_const_mul, survivingNestStepSelection_freshTube_mass p S T success η offspring k hcard]
  exact inv_mul_cancel₀ hs.ne'

end NearCritical.Section10
