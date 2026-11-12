module

public import NearCritical.Section10DifferenceFourier
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity

/-! Spectral gap on the fundamental cube for the actual Section 10
difference walk. This is the analytic input for the Green majorant. -/
@[expose] public section
noncomputable section
namespace NearCritical.Section10

open UnitAddTorus
open scoped ComplexConjugate

/-- Characteristic function of one source lazy coordinate step. -/
def lazyCoordinateCharacteristic (D : ℕ) (t : UnitAddTorus (Fin D)) : ℂ :=
  ∑ a, (lazyCoordinateWeight D a : ℂ) * mFourier (lazyCoordinateStep D a) t

/-- Independence of the two symbols and subtraction of their increments
give a nonnegative real Fourier multiplier for the difference walk. -/
theorem differenceCharacteristic_eq_normSq (D : ℕ) (t : UnitAddTorus (Fin D)) :
    differenceCharacteristic D t = (Complex.normSq (lazyCoordinateCharacteristic D t) : ℂ) := by
  classical
  rw [← Complex.mul_conj]
  unfold differenceCharacteristic lazyCoordinateCharacteristic
  rw [Fintype.sum_prod_type, map_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  simp only [differenceStepWeight, differenceStep, sub_eq_add_neg, mFourier_add,
    mFourier_neg, Complex.ofReal_mul, map_mul, Complex.conj_ofReal]
  ring

private theorem unit_character (D : ℕ) (x : Fin D → ℝ) (j : Fin D) :
    mFourier (Pi.single j 1) (fun i => (x i : AddCircle (1 : ℝ))) =
      Complex.exp ((↑(2 * Real.pi * x j) : ℂ) * Complex.I) := by
  classical
  rw [mFourier_single, fourier_coe_apply]
  congr 1
  push_cast
  ring

/-- The quadratic unit-period cosine bound includes both signs of the
coordinate and both endpoints of the fundamental interval. -/
theorem unitInterval_one_sub_cos_lower {u : ℝ} (hu : |u| ≤ 1/2) :
    8 * u^2 ≤ 1 - Real.cos (2 * Real.pi * u) := by
  have hπ := Real.pi_pos
  have hx : 0 ≤ Real.pi * |u| := mul_nonneg hπ.le (abs_nonneg _)
  have hx' : Real.pi * |u| ≤ Real.pi / 2 := by
    linarith [mul_le_mul_of_nonneg_left hu hπ.le]
  have hs := Real.mul_le_sin hx hx'
  have hnorm : 2 / Real.pi * (Real.pi * |u|) = 2 * |u| := by
    field_simp [hπ.ne'] <;> ring
  rw [hnorm] at hs
  have hsq := (sq_le_sq₀ (show 0 ≤ 2 * |u| by positivity)
    ((show 0 ≤ 2 * |u| by positivity).trans hs)).mpr hs
  have hcos : Real.cos (2 * Real.pi * u) = Real.cos (2 * (Real.pi * |u|)) := by
    rw [← Real.cos_abs (x := 2 * Real.pi * u), abs_mul, abs_mul,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_of_pos hπ, mul_assoc]
  rw [hcos, Real.cos_two_mul_eq_one_sub]
  rw [mul_pow, sq_abs] at hsq
  linarith

/-- The actual multiplier has gap at least `(4/D) ∑ xᵢ²` on the
fundamental cube. In particular this controls the inverse gap away from
the origin without assuming coordinate independence of the step. -/
theorem differenceCharacteristic_spectral_gap {D : ℕ} (hD : 0 < D)
    (x : Fin D → ℝ) (hx : ∀ j, |x j| ≤ 1/2) :
    (4 / (D : ℝ)) * (∑ j, (x j)^2) ≤
      1 - (differenceCharacteristic D (fun j => (x j : AddCircle (1 : ℝ)))).re := by
  classical
  have hd : 0 < (D : ℝ) := by exact_mod_cast hD
  let v := fun j : Fin D => Complex.exp ((↑(2 * Real.pi * x j) : ℂ) * Complex.I)
  let z : ℂ := (↑((D : ℝ)⁻¹) : ℂ) * ∑ j, v j
  have hv (j : Fin D) : ‖v j‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  have hsum : ‖∑ j, v j‖ ≤ (D : ℝ) := by
    simpa only [hv, Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin, mul_one]
      using (norm_sum_le Finset.univ v)
  have hz : ‖z‖ ≤ 1 := by
    dsimp [z]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hd.le)]
    calc
      _ ≤ (D : ℝ)⁻¹ * (D : ℝ) := mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hd.le)
      _ = 1 := inv_mul_cancel₀ hd.ne'
  have hzs : Complex.normSq z ≤ 1 := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [mul_nonneg (sub_nonneg.mpr hz) (norm_nonneg z)]
  have hφ : lazyCoordinateCharacteristic D (fun j => (x j : AddCircle (1 : ℝ))) =
      (↑(1/2 : ℝ) : ℂ) * (1 + z) := by
    unfold lazyCoordinateCharacteristic
    rw [Fintype.sum_option]
    simp only [lazyCoordinateWeight, lazyCoordinateStep, mFourier_zero,
      ContinuousMap.one_apply, mul_one, unit_character]
    dsimp [z, v]
    rw [← Finset.mul_sum]
    push_cast
    have hdC : (D : ℂ) ≠ 0 := by exact_mod_cast hD.ne'
    field_simp [hdC] <;> ring
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    ring
  have hzre : z.re = (D : ℝ)⁻¹ * ∑ j, Real.cos (2 * Real.pi * x j) := by
    have hvre (j : Fin D) : (v j).re = Real.cos (2 * Real.pi * x j) :=
      Complex.exp_ofReal_mul_I_re _
    simp [z, Complex.mul_re, Complex.re_sum, hvre]
  have hsumCos : 8 * (∑ j, (x j)^2) ≤ (D : ℝ) - ∑ j, Real.cos (2 * Real.pi * x j) := by
    simpa only [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const,
      nsmul_eq_mul, Finset.card_univ, Fintype.card_fin, mul_one] using
      (Finset.sum_le_sum fun j (_ : j ∈ (Finset.univ : Finset (Fin D))) =>
        unitInterval_one_sub_cos_lower (hx j))
  have hsumScaled := mul_le_mul_of_nonneg_left hsumCos (inv_nonneg.mpr hd.le)
  have hinv : (D : ℝ)⁻¹ * (D : ℝ) = 1 := inv_mul_cancel₀ hd.ne'
  rw [differenceCharacteristic_eq_normSq, Complex.ofReal_re, hφ, map_mul,
    Complex.normSq_ofReal, Complex.normSq_add]
  simp only [Complex.normSq_one, one_mul, Complex.conj_re]
  rw [hzre]
  rw [mul_sub, hinv] at hsumScaled
  rw [div_eq_mul_inv]
  nlinarith [hzs]

end NearCritical.Section10
