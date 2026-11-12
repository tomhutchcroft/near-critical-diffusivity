module

public import NearCritical.MaskedArmCutBounds

@[expose] public section
namespace NearCritical

/-- At large heights, both cuts are admissible, even when the bulk threshold
is integral. The same upper cut works for every source in the lower half. -/
theorem maskedArm_cuts_admissible (δ : ℝ) (H : ℕ) (k : ℤ)
    (hδ : 0 ≤ δ) (hlarge : 2 ≤ (1-δ)*(H : ℝ))
    (hk : 2*k ≤ (H : ℤ)) :
    let m : ℤ := ⌊δ*(H : ℝ)/2⌋
    let n : ℤ := (H : ℤ)-m-1
    0 ≤ m ∧ m ≤ n ∧ k ≤ n ∧ n < (H : ℤ) := by
  obtain ⟨hm, htop, _, _, hsep⟩ := maskedArm_cut_rounding δ H hδ
  have hksep := maskedArm_upper_cut_separation δ H k hk
  refine ⟨hm, ?_, ?_, htop⟩
  · have h : (0 : ℝ) ≤
        (((H : ℤ)-⌊δ*(H : ℝ)/2⌋-1 : ℤ) : ℝ) -
          ((⌊δ*(H : ℝ)/2⌋ : ℤ) : ℝ) := by linarith
    exact_mod_cast sub_nonneg.mp h
  · have h : (0 : ℝ) ≤
        (((H : ℤ)-⌊δ*(H : ℝ)/2⌋-1 : ℤ) : ℝ) - (k : ℝ) := by linarith
    exact_mod_cast sub_nonneg.mp h

end NearCritical
