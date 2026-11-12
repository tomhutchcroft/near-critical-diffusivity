module

public import NearCritical.SubcriticalKernelIntegral
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! Explicit suppression of the subcritical starting value in the new
conductivity upper-bound argument. No probability envelope is asserted here. -/
@[expose] public section
noncomputable section
namespace NearCritical

/-- The source shift Ctilde*h^-2*(log h)^2, with Ctilde=(7/c)^2. -/
def subcriticalSeedParameter (pc c h : ℝ) : ℝ := pc-(7*Real.log h/(c*h))^2

lemma subcriticalSeedParameter_le (pc c h : ℝ) : subcriticalSeedParameter pc c h ≤ pc := by
  unfold subcriticalSeedParameter
  exact sub_le_self _ (sq_nonneg _)

lemma subcritical_seed_exponent {pc c h : ℝ} (hc : 0 < c) (hh : 1 ≤ h) :
    c*h*Real.sqrt (pc-subcriticalSeedParameter pc c h) = 7*Real.log h := by
  have hh0 : 0 < h := lt_of_lt_of_le zero_lt_one hh
  have hz : 0 ≤ 7*Real.log h/(c*h) := by
    exact div_nonneg (mul_nonneg (by norm_num) (Real.log_nonneg hh)) (mul_pos hc hh0).le
  have he : pc-subcriticalSeedParameter pc c h = (7*Real.log h/(c*h))^2 := by
    unfold subcriticalSeedParameter
    ring
  rw [he, Real.sqrt_sq hz]
  field_simp

lemma exp_neg_seven_log {h : ℝ} (hh : 0 < h) :
    Real.exp (-(7:ℝ)*Real.log h) = 1/h^7 := by
  rw [neg_mul, Real.exp_neg]
  have he : Real.exp ((7:ℝ)*Real.log h) = h^7 := by
    simpa only [Nat.cast_ofNat, Real.exp_log hh] using (Real.exp_nat_mul (Real.log h) 7)
  rw [he, one_div]

/-- The initial envelope is even O(h^-8), hence smaller than the h^-6 scale.
Constants and the large subcritical shift are explicit. -/
theorem subcritical_seed_envelope_le {pc c h C : ℝ} (hc : 0 < c) (hh : 1 ≤ h)
    (hC : 0 ≤ C) :
    (C/h^2)*Real.log h*Real.exp (-c*h*Real.sqrt (pc-subcriticalSeedParameter pc c h)) ≤
      C/h^8 := by
  have hh0 : 0 < h := lt_of_lt_of_le zero_lt_one hh
  have hexp : -c*h*Real.sqrt (pc-subcriticalSeedParameter pc c h) = -(7*Real.log h) := by
    nlinarith [subcritical_seed_exponent (pc := pc) hc hh]
  rw [hexp, ← neg_mul, exp_neg_seven_log hh0]
  have hl : Real.log h ≤ h := (Real.log_le_sub_one_of_pos hh0).trans (by linarith)
  calc
    _ ≤ (C/h^2)*h*(1/h^7) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hl (div_nonneg hC (sq_nonneg _)))
        (by positivity)
    _ = _ := by field_simp

/-- Conversion to the seed scale used by the square-root integration argument. -/
theorem subcritical_seed_envelope_le_six {pc c h C : ℝ} (hc : 0 < c) (hh : 1 ≤ h)
    (hC : 0 ≤ C) :
    (C/h^2)*Real.log h*Real.exp (-c*h*Real.sqrt (pc-subcriticalSeedParameter pc c h)) ≤
      C/h^6 := by
  apply (subcritical_seed_envelope_le hc hh hC).trans
  apply div_le_div_of_nonneg_left hC (by positivity)
  calc
    h^6 = h^6*1 := by ring
    _ ≤ h^6*h^2 := mul_le_mul_of_nonneg_left (one_le_pow₀ hh) (by positivity)
    _ = h^8 := by ring

/-- The exact square-root seed hypothesis needed by the proved finite-volume
upper deduction. A may be the actual inhomogeneous conductivity at the shift. -/
theorem subcritical_seed_sqrt_bound {A pc c h C : ℝ} (hc : 0 < c) (hh : 1 ≤ h)
    (hC : 0 ≤ C)
    (hA : A ≤ (C/h^2)*Real.log h*
      Real.exp (-c*h*Real.sqrt (pc-subcriticalSeedParameter pc c h))) :
    Real.sqrt A ≤ Real.sqrt C/h^3 := by
  calc
    _ ≤ Real.sqrt (C/h^6) :=
      Real.sqrt_le_sqrt (hA.trans (subcritical_seed_envelope_le_six hc hh hC))
    _ = _ := by
      rw [Real.sqrt_div hC]
      congr 1
      rw [show h^6 = (h^3)^2 by ring, Real.sqrt_sq (by positivity)]

end NearCritical
