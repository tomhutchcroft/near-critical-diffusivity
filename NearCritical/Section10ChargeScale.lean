module

public import NearCritical.Section10FiniteLower
public import NearCritical.Section10BoxArithmetic
public import NearCritical.PreGoodUpperCount

@[expose] public section
noncomputable section

namespace NearCritical.Section10

/-- The finite cube normalizing factor is its side length to the
power (2-d). -/
theorem cubeFlowNormalization_eq_inv_pow {d : ℕ} (hd : 2 ≤ d) (r : ℕ) :
    cubeFlowNormalization d r = ((2*(r:ℝ)+1)^(d-2))⁻¹ := by
  unfold cubeFlowNormalization
  rw [card_centeredBox_exact]
  push_cast
  let L := 2*(r:ℝ)+1
  have hL : 0 < L := by dsimp only [L]; positivity
  change L^2 / L^d = (L^(d-2))⁻¹
  have h : L^d = L^(d-2)*L^2 := by rw [← pow_add,Nat.sub_add_cancel hd]
  rw [h]
  field_simp [hL.ne']

/-- The side of the issued crossing box is at most twice the product
of the coarse side length and the microscopic scale. -/
theorem boxRadius_side_le {t M : ℕ} (ht : 1 ≤ t) (hM : 1 ≤ M) :
    2*boxRadius t M+1 ≤ 2*(M*t) := by
  have ht' : 2*((t-1)/2)+1 ≤ t := by omega
  calc
    2*boxRadius t M+1 = 2*((M-1)*t) + (2*((t-1)/2)+1) := by unfold boxRadius; ring
    _ ≤ 2*((M-1)*t) + t := Nat.add_le_add_left ht' _
    _ ≤ 2*((M-1)*t) + 2*t := by omega
    _ = 2*(((M-1)+1)*t) := by ring
    _ = _ := by rw [Nat.sub_add_cancel hM]

/-- Convert the overlap scale in the paper to the exact normalization
of the translated cube and the sixth power of the correlation scale. -/
theorem boxRadius_charge_scale_le {d t M : ℕ} (hd : 2 ≤ d) (ht : 1 ≤ t) (hM : 1 ≤ M)
    {c L : ℝ} (hc : 0 ≤ c) (hL : 0 ≤ L) (htL : (t:ℝ) ≤ c*L) :
    (t:ℝ)^2 * (t:ℝ)^(6-(d:ℝ)) / (M:ℝ)^(d-2) ≤
      (2:ℝ)^(d-2) * c^6 * cubeFlowNormalization d (boxRadius t M) * L^6 := by
  let n := d-2
  let S := 2*(boxRadius t M:ℝ)+1
  let V := (M:ℝ)*(t:ℝ)
  have ht₀ : 0 < (t:ℝ) := by exact_mod_cast (show 0 < t by omega)
  have hM₀ : 0 < (M:ℝ) := by exact_mod_cast (show 0 < M by omega)
  have hS₀ : 0 < S := by dsimp only [S]; positivity
  have hV₀ : 0 < V := mul_pos hM₀ ht₀
  have hS : S ≤ 2*V := by
    dsimp only [S,V]
    exact_mod_cast boxRadius_side_le ht hM
  have hn : (n:ℝ) = (d:ℝ)-2 := Nat.cast_sub hd
  have he : (2:ℝ)+(6-(d:ℝ)) = (6:ℝ) + -(n:ℝ) := by linarith
  have hpow : (t:ℝ)^2 * (t:ℝ)^(6-(d:ℝ)) = (t:ℝ)^6 * ((t:ℝ)^n)⁻¹ := by
    rw [← Real.rpow_ofNat (t:ℝ) 2, ← Real.rpow_add ht₀, he, Real.rpow_add ht₀,
      Real.rpow_neg ht₀.le, Real.rpow_ofNat (t:ℝ) 6, Real.rpow_natCast]
  have hInv : (V^n)⁻¹ ≤ (2:ℝ)^n*(S^n)⁻¹ := by
    have h₁ := inv_anti₀ (pow_pos hS₀ n) (pow_le_pow_left₀ hS₀.le hS n)
    calc
      _ = (2:ℝ)^n*((2*V)^n)⁻¹ := by
        rw [mul_pow (2:ℝ) V n]
        field_simp [(pow_pos hV₀ n).ne', (pow_pos (by norm_num : (0:ℝ) < 2) n).ne']
      _ ≤ _ := mul_le_mul_of_nonneg_left h₁ (pow_nonneg (by norm_num) _)
  rw [cubeFlowNormalization_eq_inv_pow hd,hpow]
  change (t:ℝ)^6*((t:ℝ)^n)⁻¹ / (M:ℝ)^n ≤ (2:ℝ)^n*c^6*(S^n)⁻¹*L^6
  have hEq : (t:ℝ)^6*((t:ℝ)^n)⁻¹ / (M:ℝ)^n = (t:ℝ)^6*(V^n)⁻¹ := by
    dsimp only [V]
    rw [mul_pow]
    field_simp [ht₀.ne',hM₀.ne'] <;> ring
  rw [hEq]
  calc
    _ ≤ (c*L)^6 * ((2:ℝ)^n*(S^n)⁻¹) :=
      mul_le_mul (pow_le_pow_left₀ ht₀.le htL _) hInv (inv_nonneg.mpr (pow_nonneg hV₀.le _))
        (pow_nonneg (mul_nonneg hc hL) _)
    _ = _ := by rw [mul_pow]; ring

end NearCritical.Section10
