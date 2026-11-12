module

public import NearCritical.MaskedArmCutBounds

@[expose] public section
namespace NearCritical

/-- The ordinary suffix factor contributes two inverse powers of height. -/
theorem maskedArm_suffix_scale_le {δ C : ℝ} {H : ℕ}
    (hδ : 0 < δ) (hH : 0 < H) (hC : 0 ≤ C) :
    let m : ℤ := ⌊δ*(H : ℝ)/2⌋
    let n : ℤ := (H : ℤ)-m-1
    C/((H : ℝ)-(n : ℝ))^2 ≤ (4*C/δ^2)/(H : ℝ)^2 := by
  dsimp only
  obtain ⟨_, _, hcut, _, _⟩ := maskedArm_cut_rounding δ H hδ.le
  have hHR : 0 < (H : ℝ) := by exact_mod_cast hH
  have hgap : δ*(H : ℝ)/2 ≤ (H : ℝ) -
      (((H : ℤ)-⌊δ*(H : ℝ)/2⌋-1 : ℤ) : ℝ) := by
    push_cast
    linarith
  have hpos : 0 < δ*(H : ℝ)/2 := by positivity
  calc
    _ ≤ C/(δ*(H : ℝ)/2)^2 :=
      div_le_div_of_nonneg_left hC (sq_pos_of_pos hpos)
        ((sq_le_sq₀ hpos.le (hpos.le.trans hgap)).mpr hgap)
    _ = _ := by field_simp; ring

/-- The water-cube window implies the slab window at both strict bulk cuts. -/
theorem maskedArm_window_le {H : ℕ} {m n : ℤ} {ε : ℝ}
    (hH : 0 < H) (hm : 0 ≤ m) (hmn : m ≤ n) (hn : n < (H : ℤ))
    (hε : 0 ≤ ε) :
    ε/(H : ℝ)^2 ≤ ε/(((m : ℝ)+1)*((n : ℝ)+1)) := by
  have hmR : 0 ≤ (m : ℝ) := by exact_mod_cast hm
  have hnR : 0 ≤ (n : ℝ) := by exact_mod_cast hm.trans hmn
  have hnH : (n : ℝ)+1 ≤ (H : ℝ) := by
    exact_mod_cast (show n+1 ≤ (H : ℤ) by omega)
  have hmH : (m : ℝ)+1 ≤ (H : ℝ) := by
    exact_mod_cast (show m+1 ≤ (H : ℤ) by omega)
  apply div_le_div_of_nonneg_left hε (by positivity)
  simpa only [pow_two] using mul_le_mul hmH hnH (by linarith) (by positivity)

end NearCritical
