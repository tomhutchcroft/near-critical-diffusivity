module
public import NearCritical.Section8BoundaryKernels

/-! Depth cancellation in the outer-boundary diagram contractions. -/
@[expose] public section
noncomputable section
namespace NearCritical.Section8
open Set MeasureTheory

/-- Coordinate depth changes by at most supremum distance. -/
theorem coordinateDepth_le_add_distance {d : ℕ} (i : Fin d) (cut : ℤ)
    (positive : Bool) (x y : Vertex d) :
    coordinateDepth i cut positive y ≤ coordinateDepth i cut positive x+latticeDistance x y := by
  have hc : |(x i : ℝ)-(y i : ℝ)| ≤ latticeDistance x y := by
    simpa only [latticeDistance,vertexReal,Real.dist_eq] using
      dist_le_pi_dist (vertexReal x) (vertexReal y) i
  have hab := abs_le.mp hc
  cases positive <;> simp only [coordinateDepth,Bool.false_eq_true,ite_false,ite_true] <;> linarith

private lemma weighted_kernel_algebra {d : ℕ} (G C t h k R : ℝ)
    (hG : 0 ≤ G) (hC : 0 ≤ C) (hh : 1 ≤ h) (hk : 0 ≤ k)
    (hR : 0 ≤ R) (hdepth : k ≤ h+R)
    (global : t ≤ G*(max 1 R)^((2 : ℝ)-(d : ℝ)))
    (oneSided : t ≤ (2*C)*h*(max 1 R)^((1 : ℝ)-(d : ℝ))) :
    t*k ≤ (2*G+4*C)*h*(max 1 R)^((2 : ℝ)-(d : ℝ)) := by
  let M := max 1 R
  have hM : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hRM : R ≤ M := le_max_right _ _
  have hpow : M*M^((1 : ℝ)-(d : ℝ)) = M^((2 : ℝ)-(d : ℝ)) := by
    calc
      _ = M^(1 : ℝ)*M^((1 : ℝ)-(d : ℝ)) := by rw [Real.rpow_one]
      _ = M^((1 : ℝ)+((1 : ℝ)-(d : ℝ))) := (Real.rpow_add hM _ _).symm
      _ = _ := by congr 1; ring
  by_cases hnear : M ≤ h
  · have hk2 : k ≤ 2*h := by linarith
    calc
      _ ≤ (G*M^((2 : ℝ)-(d : ℝ)))*k := mul_le_mul_of_nonneg_right global hk
      _ ≤ (G*M^((2 : ℝ)-(d : ℝ)))*(2*h) :=
        mul_le_mul_of_nonneg_left hk2 (by positivity)
      _ ≤ _ := by
        have hz : 0 ≤ 4*C*h*M^((2 : ℝ)-(d : ℝ)) := by positivity
        dsimp [M] at *
        nlinarith only [hz]
  · have hk2 : k ≤ 2*M := by linarith
    calc
      _ ≤ ((2*C)*h*M^((1 : ℝ)-(d : ℝ)))*k := mul_le_mul_of_nonneg_right oneSided hk
      _ ≤ ((2*C)*h*M^((1 : ℝ)-(d : ℝ)))*(2*M) :=
        mul_le_mul_of_nonneg_left hk2 (by positivity)
      _ = 4*C*h*M^((2 : ℝ)-(d : ℝ)) := by rw [← hpow]; ring
      _ ≤ _ := by
        have hz : 0 ≤ 2*G*h*M^((2 : ℝ)-(d : ℝ)) := by positivity
        dsimp [M] at *
        nlinarith only [hz]

/-- Multiplying by target depth preserves a global Green kernel, at the
cost of the starting depth. Both probability estimates are actual kernels. -/
theorem restricted_halfSpace_depth_weighted {d : ℕ} (G C : ℝ)
    (hG : 0 ≤ G) (hC : 0 ≤ C) (green : CriticalSupGreenUpper d G)
    (panis : PanisHalfSpaceTwoPointUpper d C)
    (i : Fin d) (cut : ℤ) (positive : Bool) (D : Set (Vertex d))
    (hD : D ⊆ coordinateHalfSpace i cut positive) (x y : Vertex d)
    (hx : x ∈ D) (hy : y ∈ D) :
    (percolation d (criticalPoint d)).real (connectionToSetEvent D x {y}) *
      (1+coordinateDepth i cut positive y) ≤
      (2*G+4*C)*(1+coordinateDepth i cut positive x)*
        (max 1 (latticeDistance x y))^((2 : ℝ)-(d : ℝ)) := by
  have hglobal : (percolation d (criticalPoint d)).real (connectionToSetEvent D x {y}) ≤
      G*(max 1 (latticeDistance x y))^((2 : ℝ)-(d : ℝ)) := by
    have hs : connectionToSetEvent D x {y} ⊆ connectionEvent x y := by
      rintro ω ⟨_hx,z,hz,_hzD,hpath⟩
      have hzy : z = y := hz
      subst z
      have hle : restrictedGraph ω D ≤ openGraph ω := fun _ _ h => h.1
      exact hpath.mono hle
    exact (measureReal_mono hs).trans (green x y)
  apply weighted_kernel_algebra G C _ _ _ _ hG hC
  · have h := hD hx
    change 0 ≤ coordinateDepth i cut positive x at h
    linarith
  · have h := hD hy
    change 0 ≤ coordinateDepth i cut positive y at h
    linarith
  · exact latticeDistance_nonneg x y
  · linarith [coordinateDepth_le_add_distance i cut positive x y]
  · exact hglobal
  · exact restricted_halfSpace_one_sided C hC panis i cut positive D hD x y hx hy

end NearCritical.Section8
