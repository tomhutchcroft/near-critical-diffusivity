module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic

/-! Arithmetic of the diameter bound of `lem.sprinkling.AB.geo`: with
`|E| <~ T^d`, `|A| <~ T^2`, `|B| <~ T^(d-4)`, `q <~ T^-2` and the Green factors
`(T/8)^(4-d) (T/8)^(2-d)`, the first-moment numerator is at most `C T^2`.
Dimension `d = m + 6`.
-/
@[expose] public section
namespace NearCritical.Section10

lemma green_factor_eq (m : ℕ) {T : ℝ} (hT : 0 < T) :
    (T / 8) ^ ((4 : ℝ) - ((m + 6 : ℕ) : ℝ)) * (T / 8) ^ ((2 : ℝ) - ((m + 6 : ℕ) : ℝ)) =
      8 ^ (2 * m + 6) / T ^ (2 * m + 6) := by
  have h8 : (0:ℝ) < T / 8 := by positivity
  rw [← Real.rpow_add h8]
  have he : (4 : ℝ) - ((m + 6 : ℕ) : ℝ) + ((2 : ℝ) - ((m + 6 : ℕ) : ℝ)) =
      -((2 * m + 6 : ℕ) : ℝ) := by
    push_cast
    ring
  rw [he, Real.rpow_neg h8.le, Real.rpow_natCast, div_pow, inv_div]

theorem diam_numerator_le (m : ℕ) {T G K kk bU cU q q0 E A B : ℝ} (hT : 1 ≤ T)
    (hG : 0 ≤ G) (hK : 0 ≤ K) (hkk : 0 ≤ kk) (hbU : 0 ≤ bU) (hcU : 0 ≤ cU) (hq0 : 0 ≤ q0)
    (hE0 : 0 ≤ E) (hA0 : 0 ≤ A) (hB0 : 0 ≤ B) (hq : 0 ≤ q)
    (hE : E ≤ 2 * ((m + 6 : ℕ) : ℝ) * (7 * T) ^ (m + 6))
    (hA : A ≤ kk * (bU * (2 * T) ^ 2))
    (hB : B ≤ (cU * (2 * T) ^ m) * (2 * (bU * (2 * T) ^ 2)))
    (hqle : q ≤ q0 / T ^ 2) :
    E * (A * (B * (2 * (G ^ 2 * K * (T / 8) ^ ((4 : ℝ) - ((m + 6 : ℕ) : ℝ)) *
        (G * (T / 8) ^ ((2 : ℝ) - ((m + 6 : ℕ) : ℝ))) * q)))) ≤
      (2 * ((m + 6 : ℕ) : ℝ) * 7 ^ (m + 6) * (kk * bU * 4) * (cU * 2 ^ m * (2 * bU * 4)) *
        (2 * G ^ 3 * K * 8 ^ (2 * m + 6) * q0)) * T ^ 2 := by
  have hT0 : 0 < T := by linarith
  have hP := green_factor_eq m hT0
  set r1 := (T / 8) ^ ((4 : ℝ) - ((m + 6 : ℕ) : ℝ)) with hr1
  set r2 := (T / 8) ^ ((2 : ℝ) - ((m + 6 : ℕ) : ℝ)) with hr2
  have hr1' : 0 ≤ r1 := Real.rpow_nonneg (by positivity) _
  have hr2' : 0 ≤ r2 := Real.rpow_nonneg (by positivity) _
  have hrw : E * (A * (B * (2 * (G ^ 2 * K * r1 * (G * r2) * q)))) =
      E * A * B * (2 * G ^ 3 * K * (r1 * r2) * q) := by ring
  rw [hrw, hP]
  have hfac : 0 ≤ 2 * G ^ 3 * K * (8 ^ (2 * m + 6) / T ^ (2 * m + 6)) := by positivity
  have hEb : 0 ≤ 2 * ((m + 6 : ℕ) : ℝ) * (7 * T) ^ (m + 6) := by positivity
  have hAb : 0 ≤ kk * (bU * (2 * T) ^ 2) := by positivity
  have hBb : 0 ≤ (cU * (2 * T) ^ m) * (2 * (bU * (2 * T) ^ 2)) := by positivity
  have h1 : E * A * B * (2 * G ^ 3 * K * (8 ^ (2 * m + 6) / T ^ (2 * m + 6)) * q) ≤
      (2 * ((m + 6 : ℕ) : ℝ) * (7 * T) ^ (m + 6)) * (kk * (bU * (2 * T) ^ 2)) *
        ((cU * (2 * T) ^ m) * (2 * (bU * (2 * T) ^ 2))) *
        (2 * G ^ 3 * K * (8 ^ (2 * m + 6) / T ^ (2 * m + 6)) * (q0 / T ^ 2)) := by
    have hEAB : E * A * B ≤ (2 * ((m + 6 : ℕ) : ℝ) * (7 * T) ^ (m + 6)) *
        (kk * (bU * (2 * T) ^ 2)) * ((cU * (2 * T) ^ m) * (2 * (bU * (2 * T) ^ 2))) :=
      mul_le_mul (mul_le_mul hE hA hA0 hEb) hB hB0 (mul_nonneg hEb hAb)
    exact mul_le_mul hEAB (mul_le_mul_of_nonneg_left hqle hfac)
      (mul_nonneg hfac hq) (mul_nonneg (mul_nonneg hEb hAb) hBb)
  refine h1.trans (le_of_eq ?_)
  have hTne : T ≠ 0 := hT0.ne'
  have hpow : T ^ (2 * m + 6) = T ^ m * T ^ m * T ^ 6 := by ring
  rw [hpow]
  field_simp
  ring

end NearCritical.Section10
