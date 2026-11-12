module

public import NearCritical.Section10NestTransitionRows

@[expose] public section
noncomputable section
namespace NearCritical.Section10
open MeasureTheory ProbabilityTheory
open scoped Classical BigOperators

variable {α : Type*} [Fintype α] [MeasurableSpace (Finset α)]
  [MeasurableSingletonClass (Finset α)]

/-- Live chains must survive the next step. After death, subsequent weight
factors are one because a previous factor already vanished. -/
def nestTransitionSuccess (x y : Option (Finset α)) : Prop :=
  x = none ∨ y ≠ none

/-- For any probability row, the normalizer for this success predicate is
one at death and one minus the death-transition mass at a live state. -/
theorem nestTransitionSuccess_normalizer
    (P : Option (Finset α) → Option (Finset α) → ℝ)
    (hrow : ∀ x, ∑ y, P x y = 1) (x : Option (Finset α)) :
    nestSuccessProbability P nestTransitionSuccess x =
      if x = none then 1 else 1 - P x none := by
  by_cases hx : x = none
  · simp [nestSuccessProbability, nestTransitionSuccess, hx, hrow]
  · have hz : (∑ y : Option (Finset α), if y = none then P x y else 0) = P x none := by
      simp
    have hsplit : nestSuccessProbability P nestTransitionSuccess x + P x none = 1 := by
      rw [← hz, ← hrow x]
      unfold nestSuccessProbability
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro y _
      by_cases hy : y = none <;> simp [nestTransitionSuccess, hx, hy]
    simp only [if_neg hx]
    linarith

/-- Concrete sampling rows inherit a raw success lower bound from their
death probability. This includes the absorbing state required by trace recursion. -/
theorem nestTubeRow_success_lower {d : ℕ} (p : unitInterval)
    (T : Finset (Bond d)) (success : Finset α → (T → Bool) → Prop)
    (offspring : Finset α → (T → Bool) → Finset α) (k : ℕ)
    (hcard : ∀ nest ξ, success nest ξ → k ≤ (offspring nest ξ).card)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hdeath : ∀ nest, nestTubeRow p T success offspring k (some nest) none ≤ ε / 4)
    (x : Option (Finset α)) :
    1-ε/4 ≤ nestSuccessProbability (nestTubeRow p T success offspring k)
      nestTransitionSuccess x := by
  rw [nestTransitionSuccess_normalizer _ (nestTubeRow_sum p T success offspring k hcard)]
  cases x with
  | none => simpa using (sub_le_self (1 : ℝ) (by linarith : 0 ≤ ε/4))
  | some nest =>
    simp only [Option.some_ne_none, if_false]
    have h := hdeath nest
    linarith

end NearCritical.Section10
