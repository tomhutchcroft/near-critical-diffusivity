module
public import NearCritical.Section8CubePlaneGeometry
public import NearCritical.Section8BoundaryKernels

/-! Actual midpoint-plane connection mass, uniform in the cube scale. -/
@[expose] public section
noncomputable section
namespace NearCritical.Section8
open Set MeasureTheory
open scoped Classical

private theorem midpoint_count_decay_le {d n : ℕ} (hd : 1 ≤ d) (hn : 1 ≤ n) :
    (2*(n : ℝ)+1)^(d-1) * ((n : ℝ)/3)^((1 : ℝ)-(d : ℝ)) ≤
      (9 : ℝ)^(d-1) := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : 0 < (n : ℝ)/3 := by positivity
  have he : (1 : ℝ)-(d : ℝ) = -((d-1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hd, Nat.cast_one]
    ring
  rw [he, Real.rpow_neg (le_of_lt hnpos), Real.rpow_natCast, ← div_eq_mul_inv]
  apply (div_le_iff₀ (pow_pos hnpos (d-1))).mpr
  calc
    _ ≤ (9*((n : ℝ)/3))^(d-1) := by gcongr <;> linarith
    _ = _ := by rw [mul_pow]

/-- The actual midpoint prefix mass has a constant independent of the cube
radius and of the finite subdomain. The halfspace and midpoint coordinates
may differ; either midpoint orientation is covered by absolute displacement. -/
theorem cube_midpoint_connection_mass_le {d n : ℕ} (hd : 1 ≤ d) (hn : 1 ≤ n)
    (C : ℝ) (hC : 0 ≤ C) (panis : PanisHalfSpaceTwoPointUpper d C)
    (Q : Finset (Vertex d)) (x : Vertex d) (hx : x ∈ Q)
    (i j : Fin d) (cut wall : ℤ) (positive : Bool)
    (hQ : ∀ y ∈ Q, ∀ k, x k-(n : ℤ) ≤ y k ∧ y k ≤ x k+(n : ℤ))
    (hD : (Q : Set (Vertex d)) ⊆ coordinateHalfSpace j wall positive)
    (hcut : |(x i : ℝ)-(cut : ℝ)| = ((n/2 : ℕ) : ℝ)) :
    (∑ y ∈ Q.filter (fun y => y i = cut),
      (percolation d (criticalPoint d)).real
        (connectionToSetEvent (Q : Set (Vertex d)) x {y})) ≤
      (2*C*(9 : ℝ)^(d-1))*(1+coordinateDepth j wall positive x) := by
  let M := Q.filter (fun y => y i = cut)
  let a := (2*C)*(1+coordinateDepth j wall positive x)
  let b := ((n : ℝ)/3)^((1 : ℝ)-(d : ℝ))
  have hdepth : 0 ≤ coordinateDepth j wall positive x := hD hx
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have heach (y : Vertex d) (hy : y ∈ M) :
      (percolation d (criticalPoint d)).real
        (connectionToSetEvent (Q : Set (Vertex d)) x {y}) ≤ a*b := by
    obtain ⟨hyQ, hycut⟩ := Finset.mem_filter.mp hy
    have hmid : |(x i : ℝ)-(y i : ℝ)| = ((n/2 : ℕ) : ℝ) := by
      rw [hycut]
      exact hcut
    have hdist := cube_midpoint_clipped_distance_lower hn x y i hmid
    have hp := restricted_halfSpace_one_sided C hC panis j wall positive
      (Q : Set (Vertex d)) hD x y hx hyQ
    exact hp.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos (by positivity : 0 < (n : ℝ)/3)
        hdist (by linarith)) ha)
  have hcard : (M.card : ℝ) ≤ (2*(n : ℝ)+1)^(d-1) := by
    exact_mod_cast translated_cube_plane_card_le Q x i cut hQ
  calc
    _ ≤ ∑ _y ∈ M, a*b := Finset.sum_le_sum (fun y hy => heach y hy)
    _ = (M.card : ℝ)*(a*b) := by simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2*(n : ℝ)+1)^(d-1)*(a*b) :=
      mul_le_mul_of_nonneg_right hcard (mul_nonneg ha hb)
    _ = a*((2*(n : ℝ)+1)^(d-1)*b) := by ring
    _ ≤ a*(9 : ℝ)^(d-1) :=
      mul_le_mul_of_nonneg_left (midpoint_count_decay_le hd hn) ha
    _ = _ := by dsimp [a]; ring

end NearCritical.Section8
