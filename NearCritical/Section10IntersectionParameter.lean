module

public import Mathlib.Tactic

/-! Corrected parameter choice for Section10 eq.nw.eps0. The source half bound
is stronger than warranted by a general EIT parameter q<1; convergence needs <1.
 -/
@[expose] public section
namespace NearCritical.Section10

/-- An elementary bound for the exact source amplification factor. -/
theorem route_amplification_bound {ε : ℝ} (hε : 0 ≤ ε) (hsmall : ε ≤ 1/4) :
    ((1+ε)/(1-ε/4))^2 ≤ 1+8*ε := by
  have hd : 0 < 1-ε/4 := by linarith
  have hr0 : 0 ≤ (1+ε)/(1-ε/4) := div_nonneg (by linarith) hd.le
  have hr : (1+ε)/(1-ε/4) ≤ 1+2*ε := by
    apply (div_le_iff₀ hd).mpr
    nlinarith [mul_nonneg hε (sub_nonneg.mpr hsmall)]
  have hs : ((1+ε)/(1-ε/4))^2 ≤ (1+2*ε)^2 :=
    (sq_le_sq₀ hr0 (by linarith)).mpr hr
  nlinarith [mul_nonneg hε (sub_nonneg.mpr hsmall)]

/-- For every geometric EIT rate q<1, a positive source epsilon makes the
amplified rate strictly less than one, as needed in both pair-series estimates.
The explicit slack (1+q)/2 replaces the unsupported universal half bound. -/
theorem exists_intersection_epsilon {q : ℝ} (hq : 0 ≤ q) (hq1 : q < 1) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1/4 ∧
      ((1+ε)/(1-ε/4))^2*q ≤ (1+q)/2 ∧
      ((1+ε)/(1-ε/4))^2*q < 1 := by
  let ε : ℝ := (1-q)/16
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hsmall : ε ≤ 1/4 := by dsimp [ε]; linarith
  have hb := mul_le_mul_of_nonneg_right (route_amplification_bound hε.le hsmall) hq
  have hslack : ((1+ε)/(1-ε/4))^2*q ≤ (1+q)/2 := by
    dsimp [ε] at hb ⊢
    nlinarith [sq_nonneg (1-q)]
  exact ⟨ε,hε,hsmall,hslack,hslack.trans_lt (by linarith)⟩

end NearCritical.Section10
