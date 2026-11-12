module
public import NearCritical.Section8BoundaryKernels
public import NearCritical.HeartBoundaryCount

/-! The actual outer-annulus membership bound with a fixed face depth.
This profile can be used with the depth-weighted connection kernel. -/
@[expose] public section
noncomputable section
namespace NearCritical.Section8
open Set MeasureTheory
open scoped Classical

private lemma cube_mono {d R N : ℕ} (hRN : R ≤ N) :
    centeredBox d R ⊆ centeredBox d N := by
  intro z hz
  apply mem_centeredBox.mpr
  intro i
  have hh := mem_centeredBox.mp hz i
  constructor <;> omega

private lemma distance_from_inner_cube {d L R : ℕ} (x v : Vertex d)
    (hx : x ∉ centeredBox d L) (hv : v ∈ centeredBox d R) :
    (L : ℝ)-(R : ℝ) ≤ latticeDistance x v := by
  have hout : ∃ j : Fin d, ¬ (-(L : ℤ) ≤ x j ∧ x j ≤ (L : ℤ)) := by
    simpa only [mem_centeredBox,not_forall] using hx
  obtain ⟨j,hj⟩ := hout
  have hvc := mem_centeredBox.mp hv j
  have hvlo : -(R : ℝ) ≤ (v j : ℝ) := by exact_mod_cast hvc.1
  have hvhi : (v j : ℝ) ≤ R := by exact_mod_cast hvc.2
  have hc : |(x j : ℝ)-(v j : ℝ)| ≤ latticeDistance x v := by
    simpa only [latticeDistance,vertexReal,Real.dist_eq] using
      dist_le_pi_dist (vertexReal x) (vertexReal v) j
  have hcase : x j < -(L : ℤ) ∨ (L : ℤ) < x j := by omega
  rcases hcase with h | h
  · have hh : (x j : ℝ) < -(L : ℝ) := by exact_mod_cast h
    linarith [(abs_le.mp hc).1]
  · have hh : (L : ℝ) < (x j : ℝ) := by exact_mod_cast h
    linarith [(abs_le.mp hc).2]

/-- Any fixed containing face gives a valid starting-depth profile; the
separating large coordinate need not be the coordinate of that face. -/
theorem cube_outer_heart_probability_le {d N L R H : ℕ} (hd : 1 ≤ d)
    (hHR : H < R) (hRL : R < L) (hLN : L ≤ N)
    (heart : Finset (Vertex d)) (hheart : heart ⊆ centeredBox d H)
    (x : Vertex d) (hxQ : x ∈ centeredBox d N) (hxL : x ∉ centeredBox d L)
    (i : Fin d) (lower : Bool) (C B : ℝ) (hC : 0 ≤ C) (hB : 0 ≤ B)
    (panis : PanisHalfSpaceTwoPointUpper d C)
    (arm : ∀ j : Fin d, HalfSpaceCriticalArmInput j B) :
    (percolation d (criticalPoint d)).real
      {ω | x ∈ heartClusterUnion ω (centeredBox d N) heart} ≤
      (((2*C)*(1+coordinateDepth i (if lower then -(N : ℤ) else (N : ℤ)) lower x)*
        (max 1 ((L : ℝ)-(R : ℝ)))^((1 : ℝ)-(d : ℝ)))*
        (B/((R-H : ℕ) : ℝ)^3))*((2*d*(2*R+1)^(d-1) : ℕ) : ℝ) := by
  let cut : ℤ := if lower then -(N : ℤ) else (N : ℤ)
  have hD : (centeredBox d N : Set (Vertex d)) ⊆ coordinateHalfSpace i cut lower := by
    intro z hz
    have hlo : -(N : ℝ) ≤ (z i : ℝ) := by exact_mod_cast (mem_centeredBox.mp hz i).1
    have hhi : (z i : ℝ) ≤ N := by exact_mod_cast (mem_centeredBox.mp hz i).2
    cases lower <;> simp only [cut,coordinateHalfSpace,Set.mem_setOf_eq,coordinateDepth,
      Bool.false_eq_true,ite_false,ite_true] <;> push_cast <;> linarith
  have hdepth : 0 ≤ coordinateDepth i cut lower x := hD hxQ
  have hxR : x ∉ centeredBox d R := fun hx => hxL (cube_mono hRL.le hx)
  have hRN : R ≤ N := hRL.le.trans hLN
  apply heartClusterUnion_probability_le_counted_inner_arm (centeredBox d N) heart
    (cube_mono hRN) hheart hHR x hxR (by positivity) hB arm
  intro v hv
  have hvR := (Finset.mem_filter.mp hv).1
  have hvQ := cube_mono hRN hvR
  have hp := restricted_halfSpace_one_sided C hC panis i cut lower
    (centeredBox d N : Set (Vertex d)) hD x v hxQ hvQ
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hpow := Real.rpow_le_rpow_of_nonpos
    (lt_of_lt_of_le zero_lt_one (le_max_left 1 ((L : ℝ)-(R : ℝ))))
    (max_le_max le_rfl (distance_from_inner_cube x v hxL hvR))
    (show (1 : ℝ)-(d : ℝ) ≤ 0 by linarith)
  exact hp.trans (mul_le_mul_of_nonneg_left hpow (by positivity))

end NearCritical.Section8
