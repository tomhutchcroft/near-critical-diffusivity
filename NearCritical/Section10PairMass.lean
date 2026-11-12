module

public import NearCritical.NestChainWeights

/-! Section10 prop.nw.pair Step1: normalized shared-step weights and their
iterated mass bound. Actual pair-history kernel identification remains open. -/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open scoped Classical BigOperators
variable {X : Type*} [Fintype X]

private lemma successWeight_nonneg (P : X → X → ℝ) (A : X → X → Prop)
    (hP : ∀ x y, 0 ≤ P x y) (x y : X) : 0 ≤ nestSuccessWeight P A x y := by
  dsimp [nestSuccessWeight]
  split_ifs
  · exact inv_nonneg.mpr (nestSuccessProbability_nonneg P A hP x)
  · exact le_rfl

def jointStepSuccessWeight (P : X → X → ℝ) (A B : X → X → Prop)
    (shared : Bool) (x y : X) : ℝ :=
  if shared then nestSuccessWeight P A x y*nestSuccessWeight P B x y
  else nestSuccessWeight P A x y

theorem jointStepSuccessWeight_nonneg (P : X → X → ℝ) (A B : X → X → Prop)
    (shared : Bool) (hP : ∀ x y, 0 ≤ P x y) (x y : X) :
    0 ≤ jointStepSuccessWeight P A B shared x y := by
  cases shared with
  | false => exact successWeight_nonneg P A hP x y
  | true => exact mul_nonneg (successWeight_nonneg P A hP x y) (successWeight_nonneg P B hP x y)

/-- Shared successes may be arbitrarily correlated. One mean-one normalized
indicator and the other bounded by rho suffice; no pair expectation assumed. -/
theorem jointStepSuccessWeight_mass_le (P : X → X → ℝ) (A B : X → X → Prop)
    (shared : Bool) (hP : ∀ x y, 0 ≤ P x y) {ε : ℝ} (hε : 0 ≤ ε) (hsmall : ε ≤ 1/4)
    (hA : ∀ x, 1-ε/4 ≤ nestSuccessProbability P A x)
    (hB : ∀ x, 1-ε/4 ≤ nestSuccessProbability P B x) (x : X) :
    (∑ y, P x y*jointStepSuccessWeight P A B shared x y) ≤
      if shared then 1+ε/2 else 1 := by
  have hsA : 0 < nestSuccessProbability P A x := by have h := hA x; linarith
  cases shared with
  | false => exact (nestSuccessWeight_mean_one P A x hsA).le
  | true =>
    change (∑ y, P x y*(nestSuccessWeight P A x y*nestSuccessWeight P B x y)) ≤ 1+ε/2
    have hm (y : X) : P x y*(nestSuccessWeight P A x y*nestSuccessWeight P B x y) ≤
        (P x y*nestSuccessWeight P A x y)*(1+ε/2) := by
      calc
        _ = (P x y*nestSuccessWeight P A x y)*nestSuccessWeight P B x y := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (nestSuccessWeight_bounds P B hε hsmall hB x y).2
          (mul_nonneg (hP x y) (successWeight_nonneg P A hP x y))
    have hh := Finset.sum_le_sum (fun y (_ : y ∈ (Finset.univ : Finset X)) => hm y)
    rwa [← Finset.sum_mul,nestSuccessWeight_mean_one P A x hsA,one_mul] at hh

def sharedStepCount (shared : ℕ → Bool) (n : ℕ) : ℕ :=
  ((Finset.range n).filter (fun k => shared k = true)).card

private lemma sharedStepCount_succ (shared : ℕ → Bool) (n : ℕ) :
    sharedStepCount shared (n+1) = sharedStepCount shared n+(if shared n then 1 else 0) := by
  cases hs : shared n <;> simp [sharedStepCount,Finset.range_add_one,Finset.filter_insert,hs]

/-- Finite history recursion, in the same decreasing-index convention as
nestWeightedPathExpectation. A state may encode the entire pair history. -/
def pairRemainingMass (P : ℕ → X → X → ℝ) (A B : ℕ → X → X → Prop)
    (shared : ℕ → Bool) : ℕ → X → ℝ
  | 0,_ => 1
  | n+1,x => ∑ y, P n x y*jointStepSuccessWeight (P n) (A n) (B n) (shared n) x y*
      pairRemainingMass P A B shared n y

/-- Computed normalized indicators and raw success lower bounds imply the
full pair mass bound; stepwise or terminal mass estimates are not premises. -/
theorem pairRemainingMass_le (P : ℕ → X → X → ℝ) (A B : ℕ → X → X → Prop)
    (shared : ℕ → Bool) {ε : ℝ} (hε : 0 ≤ ε) (hsmall : ε ≤ 1/4) (n : ℕ)
    (hP : ∀ k < n, ∀ x y, 0 ≤ P k x y)
    (hA : ∀ k < n, ∀ x, 1-ε/4 ≤ nestSuccessProbability (P k) (A k) x)
    (hB : ∀ k < n, ∀ x, 1-ε/4 ≤ nestSuccessProbability (P k) (B k) x) (x : X) :
    pairRemainingMass P A B shared n x ≤ (1+ε/2)^(sharedStepCount shared n) := by
  induction n generalizing x with
  | zero => simp [pairRemainingMass,sharedStepCount]
  | succ n ih =>
    have hρ : 0 ≤ 1+ε/2 := by linarith
    have ht (y : X) := ih (fun k hk => hP k (by omega))
      (fun k hk => hA k (by omega)) (fun k hk => hB k (by omega)) y
    have hrow := jointStepSuccessWeight_mass_le (P n) (A n) (B n) (shared n)
      (hP n (by omega)) hε hsmall (hA n (by omega)) (hB n (by omega)) x
    calc
      _ ≤ ∑ y, (P n x y*jointStepSuccessWeight (P n) (A n) (B n) (shared n) x y)*
          (1+ε/2)^(sharedStepCount shared n) := by
        apply Finset.sum_le_sum
        intro y _
        exact mul_le_mul_of_nonneg_left (ht y)
          (mul_nonneg (hP n (by omega) x y)
            (jointStepSuccessWeight_nonneg (P n) (A n) (B n) (shared n) (hP n (by omega)) x y))
      _ = (∑ y, P n x y*jointStepSuccessWeight (P n) (A n) (B n) (shared n) x y)*
          (1+ε/2)^(sharedStepCount shared n) := (Finset.sum_mul ..).symm
      _ ≤ (if shared n then 1+ε/2 else 1)*(1+ε/2)^(sharedStepCount shared n) :=
        mul_le_mul_of_nonneg_right hrow (pow_nonneg hρ _)
      _ = (1+ε/2)^(sharedStepCount shared (n+1)) := by
        rw [sharedStepCount_succ]
        cases hs : shared n <;> simp [hs,pow_succ,mul_comm]

/-- With the source combinatorial shared-step count, the exponent is at most
2N. The source route geometry must establish this raw count separately. -/
theorem pairRemainingMass_le_common_levels (P : ℕ → X → X → ℝ) (A B : ℕ → X → X → Prop)
    (shared : ℕ → Bool) {ε : ℝ} (hε : 0 ≤ ε) (hsmall : ε ≤ 1/4) (n N : ℕ)
    (hP : ∀ k < n, ∀ x y, 0 ≤ P k x y)
    (hA : ∀ k < n, ∀ x, 1-ε/4 ≤ nestSuccessProbability (P k) (A k) x)
    (hB : ∀ k < n, ∀ x, 1-ε/4 ≤ nestSuccessProbability (P k) (B k) x)
    (hcount : sharedStepCount shared n ≤ 2*N) (x : X) :
    pairRemainingMass P A B shared n x ≤ (1+ε/2)^(2*N) := by
  exact (pairRemainingMass_le P A B shared hε hsmall n hP hA hB x).trans
    (pow_le_pow_right₀ (by linarith : 1 ≤ 1+ε/2) hcount)

end NearCritical.Section10
