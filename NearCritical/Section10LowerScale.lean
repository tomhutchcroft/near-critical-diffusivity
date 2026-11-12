module

public import NearCritical.ChemicalUpperBound

/-! Section10 eq.lowerObject: exact inverse-sixth correlation scale to cubic
gap conversion. Reuses the EXISTING source floor scale chemicalCorrelationScale. -/
@[expose] public section
noncomputable section
namespace NearCritical.Section10

/-- The literal source floor correlation scale is at least one throughout the
supercritical parameter interval. Its inverse powers have positive denominators. -/
theorem chemicalCorrelationScale_pos {d : ℕ} (p : unitInterval) (hp : criticalPoint d < p) :
    1 ≤ chemicalCorrelationScale d p := by
  have hg : 0 < (p:ℝ)-(criticalPoint d:ℝ) := sub_pos.mpr hp
  have hg1 : (p:ℝ)-(criticalPoint d:ℝ) ≤ 1 := by
    linarith [p.2.2,(criticalPoint d).2.1]
  have hs : 0 < Real.sqrt ((p:ℝ)-(criticalPoint d:ℝ)) := Real.sqrt_pos.mpr hg
  have hs1 : Real.sqrt ((p:ℝ)-(criticalPoint d:ℝ)) ≤ 1 := by
    nlinarith [Real.sq_sqrt hg.le,Real.sqrt_nonneg ((p:ℝ)-(criticalPoint d:ℝ))]
  have hi : (1:ℝ) ≤ (Real.sqrt ((p:ℝ)-(criticalPoint d:ℝ)))⁻¹ := by
    rw [inv_eq_one_div]
    exact (le_div_iff₀ hs).mpr (by simpa using hs1)
  exact (Nat.one_le_floor_iff _).mpr hi

/-- Literal rounding strengthens the inverse-sixth lower bound. No asymptotic
floor equivalence or unproved correlation-length comparison is assumed. -/
theorem chemicalCorrelationScale_inverse_six_lower {d : ℕ} (p : unitInterval)
    (hp : criticalPoint d < p) :
    ((p:ℝ)-(criticalPoint d:ℝ))^3 ≤ 1/(chemicalCorrelationScale d p:ℝ)^6 := by
  have hg : 0 < (p:ℝ)-(criticalPoint d:ℝ) := sub_pos.mpr hp
  have hs : 0 < Real.sqrt ((p:ℝ)-(criticalPoint d:ℝ)) := Real.sqrt_pos.mpr hg
  have hstar : 0 < (chemicalCorrelationScale d p:ℝ) := by
    exact_mod_cast (show 0 < chemicalCorrelationScale d p by
      have h := chemicalCorrelationScale_pos p hp
      omega)
  have hf : (chemicalCorrelationScale d p:ℝ) ≤
      1/Real.sqrt ((p:ℝ)-(criticalPoint d:ℝ)) := by
    simpa only [inv_eq_one_div] using chemicalCorrelationScale_le d p
  have hm := (le_div_iff₀ hs).mp hf
  have hm0 : 0 ≤ (chemicalCorrelationScale d p:ℝ)*Real.sqrt ((p:ℝ)-(criticalPoint d:ℝ)) :=
    mul_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _)
  have hsq := (sq_le_sq₀ hm0 (by norm_num : (0:ℝ) ≤ 1)).mpr hm
  rw [mul_pow,Real.sq_sqrt hg.le] at hsq
  have hprod : ((p:ℝ)-(criticalPoint d:ℝ))*(chemicalCorrelationScale d p:ℝ)^2 ≤ 1 := by
    nlinarith only [hsq]
  have hc := pow_le_pow_left₀ (mul_nonneg hg.le (sq_nonneg _)) hprod 3
  have hb : ((p:ℝ)-(criticalPoint d:ℝ))^3*(chemicalCorrelationScale d p:ℝ)^6 ≤ 1 := by
    convert hc using 1 <;> ring
  exact (le_div_iff₀ (pow_pos hstar 6)).mpr hb

/-- Final quantitative conversion in eq.lowerObject, for any established
finite-volume or limiting conductivity lower bound at the source scale. -/
theorem cubic_lower_of_inverse_scale_bound {d : ℕ} (p : unitInterval)
    (hp : criticalPoint d < p) {b c : ℝ} (hc : 0 ≤ c)
    (hbound : c/(chemicalCorrelationScale d p:ℝ)^6 ≤ b) :
    c*((p:ℝ)-(criticalPoint d:ℝ))^3 ≤ b := by
  calc
    _ ≤ c*(1/(chemicalCorrelationScale d p:ℝ)^6) :=
      mul_le_mul_of_nonneg_left (chemicalCorrelationScale_inverse_six_lower p hp) hc
    _ = c/(chemicalCorrelationScale d p:ℝ)^6 := by ring
    _ ≤ b := hbound

end NearCritical.Section10
