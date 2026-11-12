module
public import NearCritical.Section8BoundaryKernels
public import NearCritical.HeartBoundaryCount

/-! Actual integer-scale PxinfC upper bound: the missing outer-prefix factor
is derived from the cited half-space two-point input, not assumed. -/
@[expose] public section
noncomputable section
namespace NearCritical.Section8
open Set MeasureTheory
open scoped Classical

private lemma cube_subset_cube {d R N : ℕ} (hRN : R ≤ N) :
    centeredBox d R ⊆ centeredBox d N := by
  intro z hz
  apply mem_centeredBox.mpr
  intro i
  have hh := mem_centeredBox.mp hz i
  constructor <;> omega

private lemma boundary_cube_prefix {d N R : ℕ} (hd : 1 ≤ d) (hRN : R < N)
    (C : ℝ) (hC : 0 ≤ C) (panis : PanisHalfSpaceTwoPointUpper d C)
    (x v : Vertex d) (hx : x ∈ boundarySites (centeredBox d N))
    (hv : v ∈ centeredBox d R) :
    (percolation d (criticalPoint d)).real
      (connectionToSetEvent (centeredBox d N : Set (Vertex d)) x {v}) ≤
      (2*C)*(max 1 ((N : ℝ)-(R : ℝ)))^((1 : ℝ)-(d : ℝ)) := by
  have hxQ := (Finset.mem_filter.mp hx).1
  have hvQ := cube_subset_cube hRN.le hv
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have ha : (1 : ℝ)-(d : ℝ) ≤ 0 := by linarith
  obtain ⟨i,hi | hi⟩ := centeredBox_boundary_coordinate hx
  · have hxi : (x i : ℝ) = (N : ℝ) := by exact_mod_cast hi
    have hD : (centeredBox d N : Set (Vertex d)) ⊆ coordinateHalfSpace i (N : ℤ) false := by
      intro z hz
      have hb : (z i : ℝ) ≤ N := by exact_mod_cast (mem_centeredBox.mp hz i).2
      change 0 ≤ (N : ℝ)-(z i : ℝ)
      linarith
    have hp := restricted_halfSpace_one_sided C hC panis i N false
      (centeredBox d N : Set (Vertex d)) hD x v hxQ hvQ
    have hvb : (v i : ℝ) ≤ R := by exact_mod_cast (mem_centeredBox.mp hv i).2
    have hc : |(x i : ℝ)-(v i : ℝ)| ≤ latticeDistance x v := by
      simpa only [latticeDistance,vertexReal,Real.dist_eq] using
        dist_le_pi_dist (vertexReal x) (vertexReal v) i
    have hgap : (N : ℝ)-(R : ℝ) ≤ latticeDistance x v := by linarith [(abs_le.mp hc).2]
    have hpow := Real.rpow_le_rpow_of_nonpos
      (lt_of_lt_of_le zero_lt_one (le_max_left 1 ((N : ℝ)-(R : ℝ))))
      (max_le_max le_rfl hgap) ha
    have hp' : (percolation d (criticalPoint d)).real
        (connectionToSetEvent (centeredBox d N : Set (Vertex d)) x {v}) ≤
        (2*C)*(max 1 (latticeDistance x v))^((1 : ℝ)-(d : ℝ)) := by
      simpa [coordinateDepth,hxi] using hp
    exact hp'.trans (mul_le_mul_of_nonneg_left hpow (by positivity))
  · have hxi : (x i : ℝ) = -(N : ℝ) := by exact_mod_cast hi
    have hD : (centeredBox d N : Set (Vertex d)) ⊆ coordinateHalfSpace i (-(N : ℤ)) true := by
      intro z hz
      have hb : -(N : ℝ) ≤ (z i : ℝ) := by exact_mod_cast (mem_centeredBox.mp hz i).1
      simp only [coordinateHalfSpace, coordinateDepth, Set.mem_setOf_eq, ↓reduceIte,
        Int.cast_neg, Int.cast_natCast]
      linarith
    have hp := restricted_halfSpace_one_sided C hC panis i (-(N : ℤ)) true
      (centeredBox d N : Set (Vertex d)) hD x v hxQ hvQ
    have hvb : -(R : ℝ) ≤ (v i : ℝ) := by exact_mod_cast (mem_centeredBox.mp hv i).1
    have hc : |(x i : ℝ)-(v i : ℝ)| ≤ latticeDistance x v := by
      simpa only [latticeDistance,vertexReal,Real.dist_eq] using
        dist_le_pi_dist (vertexReal x) (vertexReal v) i
    have hgap : (N : ℝ)-(R : ℝ) ≤ latticeDistance x v := by linarith [(abs_le.mp hc).1]
    have hpow := Real.rpow_le_rpow_of_nonpos
      (lt_of_lt_of_le zero_lt_one (le_max_left 1 ((N : ℝ)-(R : ℝ))))
      (max_le_max le_rfl hgap) ha
    have hp' : (percolation d (criticalPoint d)).real
        (connectionToSetEvent (centeredBox d N : Set (Vertex d)) x {v}) ≤
        (2*C)*(max 1 (latticeDistance x v))^((1 : ℝ)-(d : ℝ)) := by
      simpa [coordinateDepth,hxi] using hp
    exact hp'.trans (mul_le_mul_of_nonneg_left hpow (by positivity))

/-- Actual full-heart-union membership at any outer cube boundary vertex.
The outer probability factor, inner arm and entry-cardinality bounds are all
derived; only the separately cited Panis and critical arm inputs remain. -/
theorem cube_boundary_heart_probability_le {d N R H : ℕ} (hd : 1 ≤ d)
    (hHR : H < R) (hRN : R < N) (heart : Finset (Vertex d))
    (hheart : heart ⊆ centeredBox d H) (x : Vertex d)
    (hx : x ∈ boundarySites (centeredBox d N)) (C B : ℝ) (hC : 0 ≤ C) (hB : 0 ≤ B)
    (panis : PanisHalfSpaceTwoPointUpper d C)
    (arm : ∀ i : Fin d, HalfSpaceCriticalArmInput i B) :
    (percolation d (criticalPoint d)).real
      {ω | x ∈ heartClusterUnion ω (centeredBox d N) heart} ≤
      (((2*C)*(max 1 ((N : ℝ)-(R : ℝ)))^((1 : ℝ)-(d : ℝ)))*
        (B/((R-H : ℕ) : ℝ)^3))*((2*d*(2*R+1)^(d-1) : ℕ) : ℝ) := by
  have hxR : x ∉ centeredBox d R := by
    intro hxR
    obtain ⟨i,hi | hi⟩ := centeredBox_boundary_coordinate hx
    · have hh := (mem_centeredBox.mp hxR i).2
      omega
    · have hh := (mem_centeredBox.mp hxR i).1
      omega
  apply heartClusterUnion_probability_le_counted_inner_arm (centeredBox d N) heart
    (cube_subset_cube hRN.le) hheart hHR x hxR (by positivity) hB arm
  intro v hv
  exact boundary_cube_prefix hd hRN C hC panis x v hx (Finset.mem_filter.mp hv).1

end NearCritical.Section8
