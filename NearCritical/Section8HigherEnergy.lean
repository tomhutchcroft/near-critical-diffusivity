module
public import NearCritical.Section8Convolution

/-! Deterministic higher-energy estimates for Section 8's diagram contractions. -/
@[expose] public section
noncomputable section
namespace NearCritical.Section8
open scoped Classical

/-- Quartic mass of the regularized fourth-order Green kernel in an actual
finite supremum ball. The center is retained. -/
theorem sum_fourth_green_ball_le {d : ℕ} (hd : 2 ≤ d) (N : ℕ)
    (s : Finset (Vertex d)) (u : Vertex d)
    (hs : ∀ x ∈ s, latticeDistance u x ≤ (N : ℝ)) :
    ∑ x ∈ s, (max 1 (latticeDistance u x))^((4 : ℝ)-(d : ℝ)) ≤
      (1+2*(d : ℝ)*3^(d-1))*(N+1 : ℝ)^4 := by
  let K : ℝ := 2*(d : ℝ)*3^(d-1)
  have hN : (1 : ℝ) ≤ N+1 := by
    have hn : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    linarith
  have hpoint (x : Vertex d) (hx : x ∈ s) :
      (max 1 (latticeDistance u x))^((4 : ℝ)-(d : ℝ)) ≤
        (N+1 : ℝ)^2*(max 1 (latticeDistance u x))^((2 : ℝ)-(d : ℝ)) := by
    have hM : 0 < max 1 (latticeDistance u x) := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
    have hMN : max 1 (latticeDistance u x) ≤ (N+1 : ℝ) :=
      max_le hN ((hs x hx).trans (by linarith))
    have he : (4 : ℝ)-(d : ℝ) = 2+((2 : ℝ)-(d : ℝ)) := by ring
    rw [he,Real.rpow_add hM,Real.rpow_two]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hM.le hMN 2) (by positivity)
  calc
    _ ≤ ∑ x ∈ s, (N+1 : ℝ)^2*(max 1 (latticeDistance u x))^((2 : ℝ)-(d : ℝ)) :=
      Finset.sum_le_sum hpoint
    _ = (N+1 : ℝ)^2*(∑ x ∈ s, (max 1 (latticeDistance u x))^((2 : ℝ)-(d : ℝ))) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ (N+1 : ℝ)^2*(1+K*(N+1 : ℝ)^2) :=
      mul_le_mul_of_nonneg_left (sum_green_ball_le hd N s u hs) (by positivity)
    _ ≤ _ := by
      have hsq : (N+1 : ℝ)^2 ≤ (N+1 : ℝ)^4 := by nlinarith [sq_nonneg ((N+1 : ℝ)^2-1)]
      dsimp [K]
      nlinarith only [hsq]

/-- Squaring the truncated fourth-order kernel costs a factor r^(6-d),
leaving a second-order kernel. This also covers zero distance. -/
theorem truncated_fourth_green_sq_le {d : ℕ} (hd : 6 ≤ d)
    (r R : ℝ) (hr : 1 ≤ r) :
    ((max r R)^((4 : ℝ)-(d : ℝ)))^2 ≤
      r^((6 : ℝ)-(d : ℝ))*(max r R)^((2 : ℝ)-(d : ℝ)) := by
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hM : 0 < max r R := hr0.trans_le (le_max_left _ _)
  have ha : (6 : ℝ)-(d : ℝ) ≤ 0 := by
    have hdR : (6 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hcomp := Real.rpow_le_rpow_of_nonpos hr0 (le_max_left r R) ha
  calc
    _ = (max r R)^((6 : ℝ)-(d : ℝ))*(max r R)^((2 : ℝ)-(d : ℝ)) := by
      rw [← Real.rpow_natCast ((max r R)^((4 : ℝ)-(d : ℝ))) 2,
        ← Real.rpow_mul hM.le,← Real.rpow_add hM]
      congr 1
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hcomp (by positivity)

end NearCritical.Section8
