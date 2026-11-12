module

public import NearCritical.Section10NestTransitionDeath
public import NearCritical.NestChainLaw

@[expose] public section
noncomputable section
namespace NearCritical.Section10
open MeasureTheory ProbabilityTheory
open scoped Classical BigOperators

variable {α : Type*} [Fintype α] [MeasurableSpace (Finset α)]
  [MeasurableSingletonClass (Finset α)]

local instance : MeasurableSpace (Option (Finset α)) := ⊤
local instance : MeasurableSingletonClass (Option (Finset α)) := ⟨fun _ => trivial⟩

/-- Concrete sampling kernel, including an absorbing death state. -/
def nestTubeKernel {d : ℕ} (p : unitInterval) (T : Finset (Bond d))
    (success : Finset α → (T → Bool) → Prop)
    (offspring : Finset α → (T → Bool) → Finset α) (k : ℕ) :
    Option (Finset α) → Measure (Option (Finset α))
  | none => Measure.dirac none
  | some nest => nestTubeTransitionWithDeath p T (success nest) (offspring nest) k

/-- Real transition rows computed from singleton masses of the sampling kernel. -/
def nestTubeRow {d : ℕ} (p : unitInterval) (T : Finset (Bond d))
    (success : Finset α → (T → Bool) → Prop)
    (offspring : Finset α → (T → Bool) → Finset α) (k : ℕ)
    (x y : Option (Finset α)) : ℝ :=
  (nestTubeKernel p T success offspring k x).real {y}

theorem nestTubeKernel_probability {d : ℕ} (p : unitInterval) (T : Finset (Bond d))
    (success : Finset α → (T → Bool) → Prop)
    (offspring : Finset α → (T → Bool) → Finset α) (k : ℕ)
    (hcard : ∀ nest ξ, success nest ξ → k ≤ (offspring nest ξ).card)
    (x : Option (Finset α)) :
    IsProbabilityMeasure (nestTubeKernel p T success offspring k x) := by
  cases x with
  | none => exact inferInstanceAs (IsProbabilityMeasure (Measure.dirac none))
  | some nest => exact nestTubeTransitionWithDeath_probability p T _ _ k (hcard nest)

theorem nestTubeRow_nonneg {d : ℕ} (p : unitInterval) (T : Finset (Bond d))
    (success : Finset α → (T → Bool) → Prop)
    (offspring : Finset α → (T → Bool) → Finset α) (k : ℕ)
    (x y : Option (Finset α)) :
    0 ≤ nestTubeRow p T success offspring k x y :=
  ENNReal.toReal_nonneg

/-- The concrete rows satisfy the normalization required by the finite trace law. -/
theorem nestTubeRow_sum {d : ℕ} (p : unitInterval) (T : Finset (Bond d))
    (success : Finset α → (T → Bool) → Prop)
    (offspring : Finset α → (T → Bool) → Finset α) (k : ℕ)
    (hcard : ∀ nest ξ, success nest ξ → k ≤ (offspring nest ξ).card)
    (x : Option (Finset α)) :
    ∑ y, nestTubeRow p T success offspring k x y = 1 := by
  letI := nestTubeKernel_probability p T success offspring k hcard x
  simp [nestTubeRow]

end NearCritical.Section10
