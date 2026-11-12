module
public import NearCritical.Section8CubeExitGeometry
public import NearCritical.Section8CubeAllFaceMass

/-! Two boundary-depth gains from actual first-exit BK at a separated scale. -/
@[expose] public section
noncomputable section
namespace NearCritical.Section8
open Set MeasureTheory
open scoped Classical

theorem cubeCut_distance_le {d n : ℕ} (Q : Finset (Vertex d)) (x z : Vertex d)
    (hz : z ∈ cubeCut Q x n) : latticeDistance x z ≤ (n : ℝ) := by
  have hb := (Finset.mem_filter.mp hz).2
  apply (dist_pi_le_iff (Nat.cast_nonneg n : (0 : ℝ) ≤ n)).mpr
  intro i
  change dist (x i : ℝ) (z i : ℝ) ≤ (n : ℝ)
  rw [Real.dist_eq]
  apply abs_le.mpr
  constructor
  · exact_mod_cast (show -(n : ℤ) ≤ x i-z i by have h := hb i; omega)
  · exact_mod_cast (show x i-z i ≤ (n : ℤ) by have h := hb i; omega)

/-- The two depth factors are obtained after actual BK decomposition, not by
multiplying two upper estimates for the same event. -/
theorem two_halfspaces_connection_le_scale {d n : ℕ} (hd : 1 ≤ d) (hn : 1 ≤ n)
    (C A B : ℝ) (hC : 0 ≤ C) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (panis : PanisHalfSpaceTwoPointUpper d C)
    (arm : ∀ i : Fin d, HalfSpaceCriticalArmInput i A)
    (second : ∀ i : Fin d, SlabBoundarySecondMomentUpper i B)
    (Q : Finset (Vertex d)) (x y : Vertex d) (hx : x ∈ Q) (hy : y ∈ Q)
    (ix iy : Fin d) (wx wy : ℤ) (sx sy : Bool)
    (hDx : (Q : Set (Vertex d)) ⊆ coordinateHalfSpace ix wx sx)
    (hDy : (Q : Set (Vertex d)) ⊆ coordinateHalfSpace iy wy sy)
    (hsep : 2*(n : ℝ) ≤ latticeDistance x y) :
    (percolation d (criticalPoint d)).real (connectionToSetEvent (Q : Set (Vertex d)) x {y}) ≤
      ((2*(d : ℝ))*(4*C*(A+B)*(9 : ℝ)^(d-1))*(2*C))*
        (1+coordinateDepth ix wx sx x)*(1+coordinateDepth iy wy sy y)*
        (n : ℝ)^(-(d : ℝ)) := by
  let T := cubeCut Q x n
  let F := T.filter (fun z => ∃ i : Fin d, z i = x i+(n : ℤ) ∨ z i = x i-(n : ℤ))
  let f := fun z => (percolation d (criticalPoint d)).real
    (connectionToSetEvent (T : Set (Vertex d)) x {z})
  let g := fun z => (percolation d (criticalPoint d)).real
    (connectionToSetEvent (Q : Set (Vertex d)) z {y})
  let L := (2*C)*(1+coordinateDepth iy wy sy y)*(n : ℝ)^((1 : ℝ)-(d : ℝ))
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hdepthy : 0 ≤ coordinateDepth iy wy sy y := hDy hy
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hTQ : T ⊆ Q := Finset.filter_subset _ _
  have hxT : x ∈ T := by
    apply Finset.mem_filter.mpr
    refine ⟨hx,?_⟩
    intro i
    constructor <;> omega
  have hyT : y ∉ T := by
    intro hyt
    have hdist := cubeCut_distance_le Q x y hyt
    linarith
  have hprefix := cube_all_face_mass_le hd hn C A B hC hA hB panis T x hxT
    ix wx sx arm second
    (fun z hz => (Finset.mem_filter.mp hz).2)
    (fun z hz => hDx (hTQ hz))
  have hsuffix (z : Vertex d) (hz : z ∈ F) : g z ≤ L := by
    have hzT := (Finset.mem_filter.mp hz).1
    have hzQ := hTQ hzT
    have hdist := cubeCut_distance_le Q x z hzT
    have htri := latticeDistance_triangle x z y
    rw [latticeDistance_comm z y] at htri
    have hzy : (n : ℝ) ≤ max 1 (latticeDistance y z) := by
      have hzylower : (n : ℝ) ≤ latticeDistance y z := by linarith
      exact hzylower.trans (le_max_right _ _)
    have hp := restricted_halfSpace_one_sided C hC panis iy wy sy
      (Q : Set (Vertex d)) hDy y z hy hzQ
    rw [connectionToSetEvent_singleton_symm (Q : Set (Vertex d)) y z] at hp
    exact hp.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos hnpos hzy (by linarith)) (by positivity))
  have hpower : (n : ℝ)^((1 : ℝ)-(d : ℝ)) = (n : ℝ)^(-(d : ℝ))*(n : ℝ) := by
    rw [show (1 : ℝ)-(d : ℝ) = -(d : ℝ)+1 by ring, Real.rpow_add hnpos, Real.rpow_one]
  calc
    _ ≤ ∑ z ∈ F, f z*g z := finite_connection_cube_exit_bk (criticalPoint d) Q x y hx hyT
    _ ≤ ∑ z ∈ F, f z*L := Finset.sum_le_sum (fun z hz =>
      mul_le_mul_of_nonneg_left (hsuffix z hz) measureReal_nonneg)
    _ = (∑ z ∈ F, f z)*L := by rw [Finset.sum_mul]
    _ ≤ ((2*(d : ℝ))*
        ((4*C*(A+B)*(9 : ℝ)^(d-1))*(1+coordinateDepth ix wx sx x)/(n : ℝ)))*L :=
      mul_le_mul_of_nonneg_right hprefix hL
    _ = _ := by
      dsimp [L]
      rw [hpower]
      field_simp [ne_of_gt hnpos]
      <;> ring

end NearCritical.Section8
