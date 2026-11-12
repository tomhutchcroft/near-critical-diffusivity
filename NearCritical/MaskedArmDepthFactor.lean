module

public import NearCritical.MaskedArmCutBounds

@[expose] public section
namespace NearCritical

/-- Above the lower cut, the normalized starting depth absorbs the missing
inverse power of height in the two-segment estimate. -/
theorem maskedArm_inverse_height_le_depth {δ : ℝ} {H : ℕ} {k : ℤ}
    (hδ : 0 < δ) (hH : 0 < H)
    (hk : ⌊δ*(H : ℝ)/2⌋ ≤ k) :
    1/(H : ℝ)^2 ≤ (2/δ)*((k : ℝ)+1)/(H : ℝ)^3 := by
  have hHR : 0 < (H : ℝ) := by exact_mod_cast hH
  have hkR : ((⌊δ*(H : ℝ)/2⌋ : ℤ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hcut := (maskedArm_cut_rounding δ H hδ.le).2.2.1
  have hdepth : (H : ℝ) ≤ (2/δ)*((k : ℝ)+1) := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hδ).mpr
    linarith
  apply (le_div_iff₀ (pow_pos hHR 3)).mpr
  convert hdepth using 1 <;> field_simp <;> ring

end NearCritical
