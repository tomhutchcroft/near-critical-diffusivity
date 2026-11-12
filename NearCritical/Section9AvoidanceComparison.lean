module

public import Mathlib.Data.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! Source lem.avoid Step 3: the finite comparison after the probabilistic
last-exit/resampling estimates. Those preceding estimates are not proved here. -/
@[expose] public section
noncomputable section
namespace NearCritical
open scoped BigOperators

/-- Finite comparison with the source positive-part numerator. Here p models
the actual avoidance probabilities, w the summed connection weights, and a the
uniform probability scale. The weighted comparison is an explicit prerequisite.
A zero energy denominator gives zero under Lean's real division convention. -/
theorem section9Avoidance_positive_part_comparison {ι : Type*} (E : Finset ι)
    (w p : ι → ℝ) (a t : ℝ) (ha : 0 < a)
    (hp : ∀ e ∈ E, 0 ≤ p e ∧ p e ≤ a)
    (hcompare : a*t ≤ ∑ e ∈ E, w e*p e) :
    a*(max t 0)^2 / (∑ e ∈ E, (w e)^2) ≤ ∑ e ∈ E, p e := by
  have hP : 0 ≤ ∑ e ∈ E, p e := Finset.sum_nonneg (fun e he => (hp e he).1)
  have hD : 0 ≤ ∑ e ∈ E, (w e)^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  by_cases henergy : (∑ e ∈ E, (w e)^2) = 0
  · simp only [henergy, div_zero]
    exact hP
  have henergypos : 0 < ∑ e ∈ E, (w e)^2 := lt_of_le_of_ne hD (Ne.symm henergy)
  by_cases ht : t ≤ 0
  · simpa only [max_eq_right ht, zero_pow (by decide : (2:ℕ) ≠ 0), mul_zero, zero_div] using hP
  have htpos : 0 < t := lt_of_not_ge ht
  rw [max_eq_left htpos.le]
  apply (div_le_iff₀ henergypos).mpr
  have hpp : (∑ e ∈ E, (p e)^2) ≤ a*(∑ e ∈ E, p e) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro e he
    have hmul := mul_le_mul_of_nonneg_right (hp e he).2 (hp e he).1
    simpa only [pow_two] using hmul
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq E w p
  have hupper : (∑ e ∈ E, w e*p e)^2 ≤
      (∑ e ∈ E, (w e)^2)*(a*(∑ e ∈ E, p e)) :=
    hcs.trans (mul_le_mul_of_nonneg_left hpp hD)
  have hlower : (a*t)^2 ≤ (∑ e ∈ E, w e*p e)^2 := by
    simpa only [pow_two] using mul_self_le_mul_self (by positivity : 0 ≤ a*t) hcompare
  have hsquare := hlower.trans hupper
  apply (mul_le_mul_iff_right₀ ha).mp
  nlinarith only [hsquare]

end NearCritical
