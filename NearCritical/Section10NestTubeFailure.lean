module

public import NearCritical.Section10NestTransitionSuccess

@[expose] public section
noncomputable section
namespace NearCritical.Section10
open MeasureTheory ProbabilityTheory
open scoped Classical

variable {α : Type*} [Fintype α] [MeasurableSpace (Finset α)]
  [MeasurableSingletonClass (Finset α)]

local instance : MeasurableSpace (Option (Finset α)) := ⊤
local instance : MeasurableSingletonClass (Option (Finset α)) := ⟨fun _ => trivial⟩

/-- The live-to-death row entry is the probability of failure under the
actual fresh Bernoulli tube law. -/
theorem nestTubeRow_death_eq_failure {d : ℕ} (p : unitInterval)
    (T : Finset (Bond d)) (success : Finset α → (T → Bool) → Prop)
    (offspring : Finset α → (T → Bool) → Finset α) (k : ℕ) (nest : Finset α) :
    nestTubeRow p T success offspring k (some nest) none =
      (Measure.pi (fun _ : T => bernoulliMeasure true false p)).real
        {ξ | ¬ success nest ξ} := by
  let μ := Measure.pi (fun _ : T => bernoulliMeasure true false p)
  have hm : MeasurableSet {ξ : T → Bool | success nest ξ} :=
    (Set.toFinite _).measurableSet
  have he : {ξ : T → Bool | ¬ success nest ξ} = {ξ | success nest ξ}ᶜ := by
    ext ξ
    simp
  change ((nestTubeTransitionWithDeath p T (success nest) (offspring nest) k) {none}).toReal =
    (μ {ξ | ¬ success nest ξ}).toReal
  rw [nestTubeTransitionWithDeath_none, he, measure_compl hm (measure_ne_top μ _)]
  simp only [measure_univ]
  rfl

/-- A geometric tube-failure estimate gives the raw success bound used in
the normalized trace weights, including the absorbing state. -/
theorem nestTubeRow_success_lower_of_failure {d : ℕ} (p : unitInterval)
    (T : Finset (Bond d)) (success : Finset α → (T → Bool) → Prop)
    (offspring : Finset α → (T → Bool) → Finset α) (k : ℕ)
    (hcard : ∀ nest ξ, success nest ξ → k ≤ (offspring nest ξ).card)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hfailure : ∀ nest,
      (Measure.pi (fun _ : T => bernoulliMeasure true false p)).real
        {ξ | ¬ success nest ξ} ≤ ε / 4)
    (x : Option (Finset α)) :
    1-ε/4 ≤ nestSuccessProbability (nestTubeRow p T success offspring k)
      nestTransitionSuccess x := by
  apply nestTubeRow_success_lower p T success offspring k hcard hε
  intro nest
  rw [nestTubeRow_death_eq_failure]
  exact hfailure nest

end NearCritical.Section10
