module
public import NearCritical.Section8F1

/-! The cited half-space two-point upper input, and its one-sided consequence.
The input is source lem.halfspace_twopoint (Panis2026, Theorem 1.4), including
its coordinate-isometric versions. No box or heart estimate is assumed. -/
@[expose] public section
noncomputable section
namespace NearCritical.Section8
open Set MeasureTheory

/-- Signed depth in an integer coordinate half-space. -/
def coordinateDepth {d : ℕ} (i : Fin d) (cut : ℤ) (positive : Bool)
    (x : Vertex d) : ℝ :=
  if positive then (x i : ℝ)-(cut : ℝ) else (cut : ℝ)-(x i : ℝ)

def coordinateHalfSpace {d : ℕ} (i : Fin d) (cut : ℤ) (positive : Bool) : Set (Vertex d) :=
  {x | 0 ≤ coordinateDepth i cut positive x}

/-- STANDARD upper half of source lem.halfspace_twopoint, Panis2026 Theorem
1.4, under coordinate permutation, translation and reflection. This is an
explicit literature hypothesis; its use does not prove that external theorem.
Source applications require d>6 and the stated critical asymptotics. -/
def PanisHalfSpaceTwoPointUpper (d : ℕ) (C : ℝ) : Prop :=
  ∀ (i : Fin d) (cut : ℤ) (positive : Bool) (x y : Vertex d),
    x ∈ coordinateHalfSpace i cut positive → y ∈ coordinateHalfSpace i cut positive →
    (percolation d (criticalPoint d)).real
      (connectionToSetEvent (coordinateHalfSpace i cut positive) x {y}) ≤
    C*((1+min (coordinateDepth i cut positive x) (latticeDistance x y))*
       (1+min (coordinateDepth i cut positive y) (latticeDistance x y)))/
      (1+(latticeDistance x y)^d)

/-- Algebraic regularization of the cited half-space kernel, including R=0. -/
theorem halfSpace_kernel_one_sided {d : ℕ} (C h k R : ℝ)
    (hC : 0 ≤ C) (hh : 0 ≤ h) (hk : 0 ≤ k) (hR : 0 ≤ R) :
    C*((1+min h R)*(1+min k R))/(1+R^d) ≤
      (2*C)*(1+h)*(max 1 R)^((1 : ℝ)-(d : ℝ)) := by
  let M := max 1 R
  have hM : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hden : 0 < 1+R^d := by positivity
  have hMd : M^d ≤ 1+R^d := by
    dsimp [M]
    rcases le_total R 1 with h | h
    · rw [max_eq_left h,one_pow]
      exact le_add_of_nonneg_right (pow_nonneg hR d)
    · rw [max_eq_right h]
      linarith
  have hprod : (1+min h R)*(1+min k R) ≤ (1+h)*(2*M) := by
    have hfirst : 1+min h R ≤ 1+h := by linarith [min_le_left h R]
    have hsecond : 1+min k R ≤ 2*M := by
      have h1 : 1 ≤ M := le_max_left _ _
      have h2 : R ≤ M := le_max_right _ _
      linarith [min_le_right k R]
    exact mul_le_mul hfirst hsecond (by positivity) (by positivity)
  have he : M / M^d = M^((1 : ℝ)-(d : ℝ)) := by
    rw [Real.rpow_sub hM,Real.rpow_one,Real.rpow_natCast]
  calc
    _ ≤ C*((1+h)*(2*M))/(1+R^d) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hprod hC) hden.le
    _ ≤ C*((1+h)*(2*M))/M^d :=
      div_le_div_of_nonneg_left (by positivity) (pow_pos hM d) hMd
    _ = _ := by rw [← he]; ring

/-- Actual critical restricted-domain one-sided connection bound. The domain
may be any subset of the coordinate half-space, including the heart annulus. -/
theorem restricted_halfSpace_one_sided {d : ℕ} (C : ℝ) (hC : 0 ≤ C)
    (panis : PanisHalfSpaceTwoPointUpper d C)
    (i : Fin d) (cut : ℤ) (positive : Bool) (D : Set (Vertex d))
    (hD : D ⊆ coordinateHalfSpace i cut positive) (x y : Vertex d)
    (hx : x ∈ D) (hy : y ∈ D) :
    (percolation d (criticalPoint d)).real (connectionToSetEvent D x {y}) ≤
      (2*C)*(1+coordinateDepth i cut positive x)*
        (max 1 (latticeDistance x y))^((1 : ℝ)-(d : ℝ)) := by
  exact (measureReal_mono (connectionToSetEvent_mono hD (Subset.refl _) x)).trans
    ((panis i cut positive x y (hD hx) (hD hy)).trans
      (halfSpace_kernel_one_sided C _ _ _ hC (hD hx) (hD hy) (latticeDistance_nonneg x y)))

end NearCritical.Section8
