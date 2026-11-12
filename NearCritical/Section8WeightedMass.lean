module
public import NearCritical.Section8Convolution

/-! The depth-weighted finite mass in source niebbnr and rho1. Radius and
depth comparisons are deterministic geometry conditions, not moment inputs. -/
@[expose] public section
noncomputable section
namespace NearCritical.Section8
open scoped Classical

/-- Cubic mass bound, uniform in every positive truncation scale. It retains
the origin term and the literal integer energy exponent. -/
theorem sum_truncated_green_depth_le {d : ℕ} (hd : 2 ≤ d) (r : ℕ) (hr : 1 ≤ r)
    (N : ℕ) (s : Finset (Vertex d)) (x : Vertex d) (ell : Vertex d → ℝ)
    (hRadius : ∀ y ∈ s, latticeDistance x y ≤ (N : ℝ))
    (hDepth : ∀ y ∈ s, ell y ≤ latticeDistance x y) :
    ∑ y ∈ s, (max (r : ℝ) (latticeDistance x y))^((2 : ℤ)-(d : ℤ))*(1+ell y) ≤
      (1+2*(d : ℝ)*3^(d-1))*(N+1 : ℝ)^3 := by
  let K : ℝ := 2*(d : ℝ)*3^(d-1)
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have ha : (2 : ℝ)-(d : ℝ) ≤ 0 := by linarith
  have hw (y : Vertex d) :
      (max (r : ℝ) (latticeDistance x y))^((2 : ℤ)-(d : ℤ)) ≤
        (max 1 (latticeDistance x y))^((2 : ℝ)-(d : ℝ)) := by
    simpa only [← Real.rpow_intCast,Int.cast_sub,Int.cast_ofNat,Int.cast_natCast] using
      Real.rpow_le_rpow_of_nonpos (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
        (max_le_max hr1 (le_rfl : latticeDistance x y ≤ latticeDistance x y)) ha
  calc
    _ ≤ ∑ y ∈ s, (max 1 (latticeDistance x y))^((2 : ℝ)-(d : ℝ))*(N+1 : ℝ) := by
      apply Finset.sum_le_sum
      intro y hy
      have hR : 0 ≤ latticeDistance x y := latticeDistance_nonneg x y
      calc
        _ ≤ (max (r : ℝ) (latticeDistance x y))^((2 : ℤ)-(d : ℤ))*(1+latticeDistance x y) :=
          mul_le_mul_of_nonneg_left (by linarith [hDepth y hy]) (by positivity)
        _ ≤ (max 1 (latticeDistance x y))^((2 : ℝ)-(d : ℝ))*(1+latticeDistance x y) :=
          mul_le_mul_of_nonneg_right (hw y) (by linarith)
        _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith [hRadius y hy]) (by positivity)
    _ = (N+1 : ℝ)*(∑ y ∈ s, (max 1 (latticeDistance x y))^((2 : ℝ)-(d : ℝ))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _hy
      ring
    _ ≤ (N+1 : ℝ)*(1+K*(N+1 : ℝ)^2) :=
      mul_le_mul_of_nonneg_left (sum_green_ball_le hd N s x hRadius) (by positivity)
    _ ≤ _ := by
      have hn : (0 : ℝ) ≤ N := Nat.cast_nonneg N
      have hc : (N+1 : ℝ) ≤ (N+1 : ℝ)^3 := by
        nlinarith [sq_nonneg (N : ℝ),mul_nonneg hn (sq_nonneg (N : ℝ))]
      dsimp [K]
      nlinarith only [hc]

end NearCritical.Section8
