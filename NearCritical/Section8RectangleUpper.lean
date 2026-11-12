module
public import NearCritical.Section8RectangleDepthGeometry
public import NearCritical.Section8TwoSidedDistance

/-! Source one-sided and two-sided upper bounds for arbitrary real rectangles. -/
@[expose] public section
noncomputable section
namespace NearCritical.Section8
open Set MeasureTheory
open scoped Classical

/-- Source lem.box_twopoint_onesided, uniform over real aspect ratios. -/
theorem source_rectangle_one_sided_upper {d : ℕ} (hd : 1 ≤ d)
    (C : ℝ) (hC : 0 ≤ C) (panis : PanisHalfSpaceTwoPointUpper d C) :
    ∃ K : ℝ, 0 < K ∧ ∀ (α β : Fin d → ℝ),
      (∀ i, 0 < α i) → (∀ i, 0 < β i) →
      ∀ (n : ℕ), 1 ≤ n → ∀ (x y : Vertex d),
      x ∈ section8Rectangle α β n → y ∈ section8Rectangle α β n → x ≠ y →
      (percolation d (criticalPoint d)).real
        (connectionToSetEvent (section8Rectangle α β n) x {y}) ≤
        K*(1+sourceRectangleDepth hd α β n x)*
          (latticeDistance x y)^((1 : ℝ)-(d : ℝ)) := by
  refine ⟨2*C+1,by positivity,?_⟩
  intro α β _hα _hβ n _hn x y hx hy hxy
  obtain ⟨i,w,s,hD,hdepth⟩ := sourceRectangle_nearest_halfSpace hd α β n x hx
  have hdx : 0 ≤ coordinateDepth i w s x := hD hx
  have hlx : 0 ≤ sourceRectangleDepth hd α β n x := hdx.trans hdepth
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hR := latticeDistance_pos hxy
  have hp := restricted_halfSpace_one_sided C hC panis i w s
    (section8Rectangle α β n) hD x y hx hy
  have hcoef : (2*C)*(1+coordinateDepth i w s x) ≤
      (2*C+1)*(1+sourceRectangleDepth hd α β n x) := by
    gcongr <;> linarith
  have hkernel : (max 1 (latticeDistance x y))^((1 : ℝ)-(d : ℝ)) ≤
      (latticeDistance x y)^((1 : ℝ)-(d : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hR (le_max_right _ _) (by linarith)
  exact hp.trans (mul_le_mul hcoef hkernel (Real.rpow_nonneg (by positivity) _) (by positivity))

/-- Source lem.box_twopoint_twosided, with the real minimum boundary margins
and a strictly positive constant independent of the aspect ratios and scale. -/
theorem source_rectangle_two_sided_upper {d : ℕ} (hd : 1 ≤ d)
    (C A B : ℝ) (hC : 0 ≤ C) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (panis : PanisHalfSpaceTwoPointUpper d C)
    (arm : ∀ i : Fin d, HalfSpaceCriticalArmInput i A)
    (second : ∀ i : Fin d, SlabBoundarySecondMomentUpper i B) :
    ∃ K : ℝ, 0 < K ∧ ∀ (α β : Fin d → ℝ),
      (∀ i, 0 < α i) → (∀ i, 0 < β i) →
      ∀ (n : ℕ), 1 ≤ n → ∀ (x y : Vertex d),
      x ∈ section8Rectangle α β n → y ∈ section8Rectangle α β n → x ≠ y →
      (percolation d (criticalPoint d)).real
        (connectionToSetEvent (section8Rectangle α β n) x {y}) ≤
        K*(1+sourceRectangleDepth hd α β n x)*(1+sourceRectangleDepth hd α β n y)*
          (latticeDistance x y)^(-(d : ℝ)) := by
  let K := 4*C+((2*(d : ℝ))*(4*C*(A+B)*(9 : ℝ)^(d-1))*(2*C))*(4 : ℝ)^d
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨K+1,by positivity,?_⟩
  intro α β _hα _hβ n _hn x y hx hy hxy
  obtain ⟨ix,wx,sx,hDx,hdx⟩ := sourceRectangle_nearest_halfSpace hd α β n x hx
  obtain ⟨iy,wy,sy,hDy,hdy⟩ := sourceRectangle_nearest_halfSpace hd α β n y hy
  let Q := sourceRectangleFinset α β n
  have hQ : (Q : Set (Vertex d)) = section8Rectangle α β n := sourceRectangleFinset_coe α β n
  have hxQ : x ∈ Q := by change x ∈ (Q : Set (Vertex d)); rw [hQ]; exact hx
  have hyQ : y ∈ Q := by change y ∈ (Q : Set (Vertex d)); rw [hQ]; exact hy
  have hQx : (Q : Set (Vertex d)) ⊆ coordinateHalfSpace ix wx sx := by rw [hQ]; exact hDx
  have hQy : (Q : Set (Vertex d)) ⊆ coordinateHalfSpace iy wy sy := by rw [hQ]; exact hDy
  have hp := two_halfspaces_connection_le_distance hd C A B hC hA hB panis arm second
    Q x y hxQ hyQ ix iy wx wy sx sy hQx hQy
  rw [hQ] at hp
  have hdx0 : 0 ≤ coordinateDepth ix wx sx x := hDx hx
  have hdy0 : 0 ≤ coordinateDepth iy wy sy y := hDy hy
  have hlx : 0 ≤ sourceRectangleDepth hd α β n x := hdx0.trans hdx
  have hly : 0 ≤ sourceRectangleDepth hd α β n y := hdy0.trans hdy
  have hcoef : K*(1+coordinateDepth ix wx sx x)*(1+coordinateDepth iy wy sy y) ≤
      (K+1)*(1+sourceRectangleDepth hd α β n x)*(1+sourceRectangleDepth hd α β n y) := by
    gcongr <;> linarith
  have hR := latticeDistance_pos hxy
  have hkernel : (max 1 (latticeDistance x y))^(-(d : ℝ)) ≤
      (latticeDistance x y)^(-(d : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hR (le_max_right _ _)
      (neg_nonpos.mpr (Nat.cast_nonneg d))
  exact hp.trans (mul_le_mul hcoef hkernel (Real.rpow_nonneg (by positivity) _) (by positivity))

end NearCritical.Section8
