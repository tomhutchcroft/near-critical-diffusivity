module

public import NearCritical.FiniteExpectation
public import Mathlib.Tactic

/-! Finite-history normalized success weights for source eq.nw.weights,
lem.nw.mean and eq.nw.iota. The actual exploration law must instantiate the
finite transition data; that probabilistic construction is not asserted here. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Finset

/-- Conditional success probability, computed from a finite transition row.
The state may encode the entire revealed history. -/
def nestSuccessProbability {X : Type*} [Fintype X] (P : X → X → ℝ)
    (success : X → X → Prop) (x : X) : ℝ := by
  classical
  exact ∑ y, if success x y then P x y else 0

/-- The source normalized indicator, including zero weight on failure. -/
def nestSuccessWeight {X : Type*} [Fintype X] (P : X → X → ℝ)
    (success : X → X → Prop) (x y : X) : ℝ := by
  classical
  exact if success x y then (nestSuccessProbability P success x)⁻¹ else 0

lemma nestSuccessProbability_nonneg {X : Type*} [Fintype X]
    (P : X → X → ℝ) (success : X → X → Prop) (hP : ∀ x y, 0≤P x y) (x : X) :
    0≤nestSuccessProbability P success x := by
  classical
  apply Finset.sum_nonneg
  intro y hy
  split
  · exact hP x y
  · exact le_rfl

lemma nestSuccessProbability_le_one {X : Type*} [Fintype X]
    (P : X → X → ℝ) (success : X → X → Prop) (hP : ∀ x y, 0≤P x y)
    (hrow : ∀ x, ∑ y, P x y=1) (x : X) : nestSuccessProbability P success x ≤ 1 := by
  classical
  rw [← hrow x]
  apply Finset.sum_le_sum
  intro y hy
  split
  · exact le_rfl
  · exact hP x y

/-- The conditional mean-one calculation uses the actual computed success
probability, not an assumed conditional-mean conclusion. -/
theorem nestSuccessWeight_mean_one {X : Type*} [Fintype X]
    (P : X → X → ℝ) (success : X → X → Prop) (x : X)
    (hs : 0<nestSuccessProbability P success x) :
    ∑ y, P x y * nestSuccessWeight P success x y = 1 := by
  classical
  calc
    _ = (∑ y, if success x y then P x y else 0) * (nestSuccessProbability P success x)⁻¹ := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro y hy
      by_cases h : success x y <;> simp [nestSuccessWeight,h]
    _ = 1 := mul_inv_cancel₀ hs.ne'

/-- Expected remaining product of normalized success indicators. This is the
finite conditional path expectation: each transition contributes its probability
P times its source weight iota. Time/state may encode full exploration history. -/
def nestWeightedPathExpectation {X : Type*} [Fintype X]
    (P : ℕ → X → X → ℝ) (success : ℕ → X → X → Prop) : ℕ → X → ℝ
  | 0,_ => 1
  | n+1,x => ∑ y, P n x y * nestSuccessWeight (P n) (success n) x y *
      nestWeightedPathExpectation P success n y

/-- The product has mean one without independence between successive successes.
Strict positivity is required only at the stages actually included in the product. -/
theorem nestWeightedPathExpectation_eq_one {X : Type*} [Fintype X]
    (P : ℕ → X → X → ℝ) (success : ℕ → X → X → Prop) (N : ℕ)
    (hs : ∀ n<N, ∀ x, 0<nestSuccessProbability (P n) (success n) x) (x : X) :
    nestWeightedPathExpectation P success N x = 1 := by
  induction N generalizing x with
  | zero => rfl
  | succ n ih =>
    simp only [nestWeightedPathExpectation]
    have ht : ∀ y, nestWeightedPathExpectation P success n y=1 :=
      fun y => ih (fun k hk z => hs k (by omega) z) y
    simp only [ht,mul_one]
    exact nestSuccessWeight_mean_one (P n) (success n) x (hs n (by omega) x)

/-- Source eq.nw.iota: success at least 1-epsilon/4 yields the uniform weight
bound 1+epsilon/2. Failure has weight zero. -/
theorem nestSuccessWeight_bounds {X : Type*} [Fintype X]
    (P : X → X → ℝ) (success : X → X → Prop) {ε : ℝ}
    (hε : 0≤ε) (hεsmall : ε≤1/4)
    (hs : ∀ x, 1-ε/4 ≤ nestSuccessProbability P success x) (x y : X) :
    0≤nestSuccessWeight P success x y ∧ nestSuccessWeight P success x y ≤ 1+ε/2 := by
  classical
  have hbase : 0<1-ε/4 := by linarith
  have hpos : 0<nestSuccessProbability P success x := hbase.trans_le (hs x)
  by_cases h : success x y
  · simp only [nestSuccessWeight,ite_eq_left h]
    refine ⟨inv_nonneg.mpr hpos.le,?_⟩
    rw [inv_eq_one_div]
    apply (div_le_iff₀ hpos).2
    have hfactor : 0≤1+ε/2 := by linarith
    have hprod := mul_le_mul_of_nonneg_left (hs x) hfactor
    nlinarith
  · simp only [nestSuccessWeight,ite_eq_right h]
    constructor <;> linarith

/-- Averaging routewise mean-one products against a normalized route law keeps
mean one. Actual route/exploration and cube-weight independence remain separate. -/
theorem nest_route_weight_average {R X : Type*} [Fintype R] [Fintype X]
    (μ : R → ℝ) (hμ : ∑ r, μ r=1)
    (P : R → ℕ → X → X → ℝ) (success : R → ℕ → X → X → Prop)
    (N : R → ℕ) (start : R → X)
    (hs : ∀ r n, n<N r → ∀ x, 0<nestSuccessProbability (P r n) (success r n) x) :
    ∑ r, μ r * nestWeightedPathExpectation (P r) (success r) (N r) (start r) = 1 := by
  have he (r : R) := nestWeightedPathExpectation_eq_one (P r) (success r) (N r)
    (fun n hn x => hs r n hn x) (start r)
  simpa only [he,mul_one] using hμ

end NearCritical
