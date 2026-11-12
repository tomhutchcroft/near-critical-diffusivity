module

public import NearCritical.NestChainLaw
public import NearCritical.Section10SharedStepCount

@[expose] public section
noncomputable section
namespace NearCritical.Section10
open MeasureTheory
open scoped Classical BigOperators

/-- Product of the normalized success factors along a finite paired history. -/
def pairTraceWeight {X : Type*} [Fintype X] (P : ℕ → X → X → ℝ)
    (S T : ℕ → X → X → Prop) (shared : ℕ → Bool) :
    (n : ℕ) → X → NestTrace X n → ℝ
  | 0, _, _ => 1
  | n+1, x, z =>
      jointStepSuccessWeight (P n) (S n) (T n) (shared n) x z.1 *
        pairTraceWeight P S T shared n z.1 z.2

/-- Summing literal trace masses and weight products gives the pair recurrence. -/
theorem pairTrace_weighted_sum {X : Type*} [Fintype X]
    (P : ℕ → X → X → ℝ) (S T : ℕ → X → X → Prop)
    (shared : ℕ → Bool) (n : ℕ) (x : X) :
    ∑ z : NestTrace X n, nestTraceMass P n x z * pairTraceWeight P S T shared n x z =
      pairRemainingMass P S T shared n x := by
  induction n generalizing x with
  | zero =>
    let : Unique (NestTrace X 0) := inferInstanceAs (Unique PUnit)
    simp [nestTraceMass, pairTraceWeight, pairRemainingMass]
  | succ n ih =>
    change (∑ z : X × NestTrace X n,
      (P n x z.1 * nestTraceMass P n z.1 z.2) *
      (jointStepSuccessWeight (P n) (S n) (T n) (shared n) x z.1 *
        pairTraceWeight P S T shared n z.1 z.2)) = _
    rw [Fintype.sum_prod_type]
    change (∑ y : X, ∑ z : NestTrace X n,
      (P n x y * nestTraceMass P n y z) *
        (jointStepSuccessWeight (P n) (S n) (T n) (shared n) x y *
          pairTraceWeight P S T shared n y z)) = _
    unfold pairRemainingMass
    apply Finset.sum_congr rfl
    intro y _
    have he (z : NestTrace X n) :
        (P n x y * nestTraceMass P n y z) *
          (jointStepSuccessWeight (P n) (S n) (T n) (shared n) x y *
            pairTraceWeight P S T shared n y z) =
        (P n x y * jointStepSuccessWeight (P n) (S n) (T n) (shared n) x y) *
          (nestTraceMass P n y z * pairTraceWeight P S T shared n y z) := by ring
    simp_rw [he]
    rw [← Finset.mul_sum, ih]

/-- The pair recurrence is an actual expectation under the finite trace law. -/
theorem pairTraceLaw_integral_weight {X : Type*} [Fintype X]
    (P : ℕ → X → X → ℝ) (S T : ℕ → X → X → Prop)
    (shared : ℕ → Bool) (n : ℕ)
    (hP : ∀ k < n, ∀ x y, 0 ≤ P k x y)
    (hrow : ∀ k < n, ∀ x, ∑ y, P k x y = 1) (x : X) :
    (∫ z, pairTraceWeight P S T shared n x z
      ∂(nestTraceLaw P n hP hrow x).toMeasure) =
        pairRemainingMass P S T shared n x := by
  rw [PMF.integral_eq_sum]
  simp only [nestTraceLaw_apply,
    ENNReal.toReal_ofReal (nestTraceMass_nonneg P n hP x _), smul_eq_mul]
  exact pairTrace_weighted_sum P S T shared n x

/-- Raw step success estimates control the expected pair weight. -/
theorem pairTraceLaw_integral_weight_le {X : Type*} [Fintype X]
    (P : ℕ → X → X → ℝ) (S T : ℕ → X → X → Prop)
    (shared : ℕ → Bool) (n : ℕ)
    (hP : ∀ k < n, ∀ x y, 0 ≤ P k x y)
    (hrow : ∀ k < n, ∀ x, ∑ y, P k x y = 1)
    {ε : ℝ} (hε : 0 ≤ ε) (hsmall : ε ≤ 1/4)
    (hS : ∀ k < n, ∀ x, 1-ε/4 ≤ nestSuccessProbability (P k) (S k) x)
    (hT : ∀ k < n, ∀ x, 1-ε/4 ≤ nestSuccessProbability (P k) (T k) x)
    (x : X) :
    (∫ z, pairTraceWeight P S T shared n x z
      ∂(nestTraceLaw P n hP hrow x).toMeasure) ≤
        (1+ε/2)^(sharedStepCount shared n) := by
  rw [pairTraceLaw_integral_weight]
  exact pairRemainingMass_le P S T shared hε hsmall n hP hS hT x

end NearCritical.Section10
