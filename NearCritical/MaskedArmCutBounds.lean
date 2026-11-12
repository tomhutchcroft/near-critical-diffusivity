module

public import NearCritical.TwoPhaseCriticalInitial

/-! Integer rounding for the actual strict bulk band. These are numerical
lemmas only; actual path and probability reductions are supplied separately. -/
@[expose] public section
namespace NearCritical

lemma maskedArm_cut_rounding (δ : ℝ) (H : ℕ) (hδ : 0 ≤ δ) :
    let m : ℤ := ⌊δ*(H : ℝ)/2⌋
    let n : ℤ := (H : ℤ)-m-1
    0 ≤ m ∧ n < (H : ℤ) ∧
      δ*(H : ℝ)/2 ≤ (m : ℝ)+1 ∧
      (H : ℤ)-n = m+1 ∧
      (1-δ)*(H : ℝ)-1 ≤ (n : ℝ)-(m : ℝ) := by
  dsimp only
  let m : ℤ := ⌊δ*(H : ℝ)/2⌋
  have hm0 : 0 ≤ m := Int.floor_nonneg.mpr (by positivity)
  have hmle : (m : ℝ) ≤ δ*(H : ℝ)/2 := Int.floor_le _
  have hmlt : δ*(H : ℝ)/2 < (m : ℝ)+1 := Int.lt_floor_add_one _
  refine ⟨hm0,by omega,hmlt.le,by omega,?_⟩
  push_cast
  nlinarith

/-- At the upper cut, every source at height at most H/2 retains at least
half the macroscopic subcritical separation, with an explicit one-layer loss. -/
lemma maskedArm_upper_cut_separation (δ : ℝ) (H : ℕ) (k : ℤ)
    (hk : 2*k ≤ (H : ℤ)) :
    let m : ℤ := ⌊δ*(H : ℝ)/2⌋
    let n : ℤ := (H : ℤ)-m-1
    (1-δ)*(H : ℝ)/2-1 ≤ (n : ℝ)-(k : ℝ) := by
  dsimp only
  have hm : ((⌊δ*(H : ℝ)/2⌋ : ℤ) : ℝ) ≤ δ*(H : ℝ)/2 := Int.floor_le _
  have hkR : 2*(k : ℝ) ≤ (H : ℝ) := by exact_mod_cast hk
  push_cast
  nlinarith

/-- A one-layer rounding loss costs a scale-independent exponential factor.
This reuses the critical-start scalar lemma rather than differentiating any
infinite mass or treating a rounded separation as exact. -/
lemma maskedArm_exp_one_layer_loss {a s L ell : ℝ}
    (ha : 0 ≤ a) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hgap : L-1 ≤ ell) :
    Real.exp (-a*s*ell) ≤ Real.exp a*Real.exp (-a*s*L) := by
  have h := twoPhase_suffix_exponential_rounding ha hs0 hs1
    (show 2*L ≤ 2*ell+2 by linarith)
  have he : -(a/2)*s*(2*L) = -a*s*L := by ring
  simpa only [he] using h

end NearCritical
