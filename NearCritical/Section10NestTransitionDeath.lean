module

public import NearCritical.Section10NestTransitionLaw

@[expose] public section
noncomputable section
namespace NearCritical.Section10
open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

variable {α : Type*} [Fintype α] [MeasurableSpace (Finset α)]
  [MeasurableSingletonClass (Finset α)]

local instance : MeasurableSpace (Option (Finset α)) := ⊤
local instance : MeasurableSingletonClass (Option (Finset α)) :=
  ⟨fun _ => trivial⟩

/-- Complete the surviving transition by sending unsuccessful tube outcomes
to the absorbing death state. -/
def nestTubeTransitionWithDeath {d : ℕ} (p : unitInterval)
    (T : Finset (Bond d)) (success : (T → Bool) → Prop)
    (offspring : (T → Bool) → Finset α) (k : ℕ) : Measure (Option (Finset α)) :=
  (nestTubeTransition p T success offspring k).map some +
    (1 - (Measure.pi (fun _ : T => bernoulliMeasure true false p)) {ξ | success ξ}) •
      Measure.dirac none

/-- Every tube sample either produces the selected next nest or kills the
chain, giving a probability transition from the concrete sampling construction. -/
theorem nestTubeTransitionWithDeath_probability {d : ℕ} (p : unitInterval)
    (T : Finset (Bond d)) (success : (T → Bool) → Prop)
    (offspring : (T → Bool) → Finset α) (k : ℕ)
    (hcard : ∀ ξ, success ξ → k ≤ (offspring ξ).card) :
    IsProbabilityMeasure (nestTubeTransitionWithDeath p T success offspring k) := by
  let μ := Measure.pi (fun _ : T => bernoulliMeasure true false p)
  have hs : μ {ξ | success ξ} ≤ 1 := by
    calc
      _ ≤ μ Set.univ := measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
  constructor
  simp only [nestTubeTransitionWithDeath, Measure.add_apply, Measure.smul_apply,
    Measure.map_apply (measurable_of_countable (some : Finset α → Option (Finset α))) MeasurableSet.univ, Set.preimage_univ,
    Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
  rw [nestTubeTransition_mass p T success offspring k hcard]
  exact add_tsub_cancel_of_le hs

/-- The completed transition assigns the exact failure probability to death. -/
theorem nestTubeTransitionWithDeath_none {d : ℕ} (p : unitInterval)
    (T : Finset (Bond d)) (success : (T → Bool) → Prop)
    (offspring : (T → Bool) → Finset α) (k : ℕ) :
    nestTubeTransitionWithDeath p T success offspring k {none} =
      1 - (Measure.pi (fun _ : T => bernoulliMeasure true false p)) {ξ | success ξ} := by
  have he : (some : Finset α → Option (Finset α)) ⁻¹' {none} = ∅ := by
    ext nest
    simp
  rw [nestTubeTransitionWithDeath, Measure.add_apply,
    Measure.map_apply (measurable_of_countable (some : Finset α → Option (Finset α)))
      (measurableSet_singleton none), he]
  simp

end NearCritical.Section10
