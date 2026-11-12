module
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-! Exact scalar normalization of the source avoidance numerator. -/
@[expose] public section
noncomputable section
namespace NearCritical

/-- The normalization is valid even for an empty target scale s=0. -/
theorem section9_avoidance_normalized_numerator (U s t z : ℝ)
    (hU : 0 < U) (hs : 0 ≤ s) (hz : 0 ≤ z) :
    (U*s)*(max ((s*t*z)/(U*s)) 0)^2 = (s/U)*(max t 0)^2*z^2 := by
  by_cases hs0 : s = 0
  · simp [hs0]
  have hspos : 0 < s := lt_of_le_of_ne hs (Ne.symm hs0)
  have hquot : (s*t*z)/(U*s) = (t*z)/U := by
    field_simp [ne_of_gt hU,hs0]
    <;> ring
  have hmax : max ((t*z)/U) 0 = (max t 0)*z/U := by
    by_cases ht : 0 ≤ t
    · rw [max_eq_left ht,max_eq_left (div_nonneg (mul_nonneg ht hz) hU.le)]
    · have ht0 : t ≤ 0 := le_of_not_ge ht
      rw [max_eq_right ht0,max_eq_right (div_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg ht0 hz) hU.le),zero_mul,zero_div]
  rw [hquot,hmax]
  field_simp [ne_of_gt hU]
  <;> ring

/-- The bad-hit power factors into the baseline power and n^(4-d), exactly. -/
theorem section9_avoidance_error_power_factor (d : ℕ) (n : ℝ) (hn : 0 < n) :
    n^(6-2*(d : ℝ)) = n^((2 : ℝ)-(d : ℝ))*n^((4 : ℝ)-(d : ℝ)) := by
  rw [← Real.rpow_add hn]
  congr 1
  ring

end NearCritical
