module
public import NearCritical.Section8BoundaryKernels

/-! Literal nearest-face geometry and the one-sided two-point bound in cubes.
The cited half-space theorem remains explicit; the cube estimate is derived. -/
@[expose] public section
noncomputable section
namespace NearCritical.Section8
open Set MeasureTheory
open scoped Classical

/-- A coordinate face nearest to x gives a containing half-space with depth
exactly the cube radius minus the supremum distance to the origin. -/
theorem cube_nearest_coordinate_halfSpace {d n : ℕ} (hd : 1 ≤ d)
    (x : Vertex d) (hx : x ∈ centeredBox d n) :
    ∃ (i : Fin d) (cut : ℤ) (positive : Bool),
      (centeredBox d n : Set (Vertex d)) ⊆ coordinateHalfSpace i cut positive ∧
      coordinateDepth i cut positive x = (n : ℝ)-latticeDistance 0 x := by
  have hne : (Finset.univ : Finset (Fin d)).Nonempty :=
    ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  obtain ⟨i, _, hmax⟩ := Finset.exists_max_image Finset.univ
    (fun j : Fin d => |(x j : ℝ)|) hne
  have hnorm : |(x i : ℝ)| = latticeDistance 0 x := by
    apply le_antisymm
    · simpa [latticeDistance, vertexReal, Real.dist_eq] using
        dist_le_pi_dist (vertexReal (0 : Vertex d)) (vertexReal x) i
    · apply (dist_pi_le_iff (abs_nonneg (x i : ℝ))).mpr
      intro j
      simpa [vertexReal, Real.dist_eq] using hmax j (Finset.mem_univ j)
  by_cases hsign : 0 ≤ (x i : ℝ)
  · refine ⟨i, (n : ℤ), false, ?_, ?_⟩
    · intro z hz
      change 0 ≤ (n : ℝ)-(z i : ℝ)
      exact sub_nonneg.mpr (by exact_mod_cast (mem_centeredBox.mp hz i).2)
    · simp [coordinateDepth, ← hnorm, abs_of_nonneg hsign]
  · have hsign' : (x i : ℝ) < 0 := lt_of_not_ge hsign
    refine ⟨i, -(n : ℤ), true, ?_, ?_⟩
    · intro z hz
      change 0 ≤ (z i : ℝ)-((-(n : ℤ) : ℤ) : ℝ)
      have hzR : -(n : ℝ) ≤ (z i : ℝ) := by
        exact_mod_cast (mem_centeredBox.mp hz i).1
      push_cast
      linarith
    · simp only [coordinateDepth, ite_true, Int.cast_neg, Int.cast_natCast,
        ← hnorm, abs_of_neg hsign']
      ring

/-- Actual restricted connections in a cube satisfy the source one-sided
boundary estimate, with the true nearest-face depth and one uniform constant.
Every subdomain inherits the estimate, including cube annuli. -/
theorem cube_one_sided_connection_le {d n : ℕ} (hd : 1 ≤ d)
    (C : ℝ) (hC : 0 ≤ C) (panis : PanisHalfSpaceTwoPointUpper d C)
    (D : Set (Vertex d)) (hD : D ⊆ (centeredBox d n : Set (Vertex d)))
    (x y : Vertex d) (hx : x ∈ D) (hy : y ∈ D) :
    (percolation d (criticalPoint d)).real (connectionToSetEvent D x {y}) ≤
      (2*C)*(1+((n : ℝ)-latticeDistance 0 x))*
        (max 1 (latticeDistance x y))^((1 : ℝ)-(d : ℝ)) := by
  obtain ⟨i, cut, positive, hcube, hdepth⟩ :=
    cube_nearest_coordinate_halfSpace hd x (hD hx)
  simpa only [hdepth] using restricted_halfSpace_one_sided C hC panis
    i cut positive D (hD.trans hcube) x y hx hy

end NearCritical.Section8
