module
public import NearCritical.Section8LocalAnnulusMass
public import NearCritical.Section8CubeOneSided
public import NearCritical.Section8TwoSidedScale

/-! Corrected actual RD estimate in a positive dominant-face chart, for gap at least two. -/
@[expose] public section
noncomputable section
namespace NearCritical.Section8
open Set MeasureTheory
open scoped Classical

private theorem tenth_scale_power {d n : ℕ} (hd : 1 ≤ d) :
    ((n : ℝ)/10)^((1 : ℝ)-(d : ℝ)) =
      (10 : ℝ)^(d-1)*(n : ℝ)^((1 : ℝ)-(d : ℝ)) := by
  have he : (1 : ℝ)-(d : ℝ) = -((d-1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hd,Nat.cast_one]
    ring
  rw [he,Real.rpow_neg (by positivity : (0 : ℝ) ≤ (n : ℝ)/10),
    Real.rpow_neg (Nat.cast_nonneg n)]
  simp only [Real.rpow_natCast]
  rw [div_pow,inv_div,div_eq_mul_inv]

/-- Actual source-domain connection estimate in one positive face chart.
The local radius is strictly below the gap; first exit retains the annulus prefix. -/
theorem positive_RD_connection_le {d n c r s : ℕ} (hd : 1 ≤ d) (hn : 1 ≤ n)
    (hs : 2 ≤ s) (hrs : r < s) (hsc : s ≤ c) (hcn : 5*c ≤ n)
    (C A B : ℝ) (hC : 0 ≤ C) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (panis : PanisHalfSpaceTwoPointUpper d C)
    (arm : ∀ j : Fin d, HalfSpaceCriticalArmInput j A)
    (second : ∀ j : Fin d, SlabBoundarySecondMomentUpper j B)
    (x w : Vertex d) (i : Fin d)
    (hx : x ∈ heartAnnulus (centeredBox d n) (centeredBox d c))
    (hw : w ∈ heartAnnulus (centeredBox d n) (centeredBox d c))
    (hxouter : 3*(n : ℝ)/4 ≤ latticeDistance 0 x)
    (hface : w i = (c : ℤ)+(r : ℤ))
    (htransverse : ∀ j : Fin d, j ≠ i → |w j| ≤ (c : ℤ)-(s : ℤ)) :
    (percolation d (criticalPoint d)).real
      (connectionToSetEvent (heartAnnulus (centeredBox d n) (centeredBox d c) : Set (Vertex d)) x {w}) ≤
      ((6*(d : ℝ))*(4*C*(A+B)*(9 : ℝ)^(d-1))*(2*C)*(10 : ℝ)^(d-1))*
        (1+((n : ℝ)-latticeDistance 0 x))*(1+(r : ℝ))*
        (n : ℝ)^((1 : ℝ)-(d : ℝ))/(s : ℝ) := by
  let Q := heartAnnulus (centeredBox d n) (centeredBox d c)
  let T := cubeCut Q w (s/2)
  let F := T.filter (fun z => ∃ j : Fin d,
    z j = w j+((s/2 : ℕ) : ℤ) ∨ z j = w j-((s/2 : ℕ) : ℤ))
  let f := fun z => (percolation d (criticalPoint d)).real
    (connectionToSetEvent (T : Set (Vertex d)) w {z})
  let g := fun z => (percolation d (criticalPoint d)).real
    (connectionToSetEvent (Q : Set (Vertex d)) z {x})
  let L := (2*C)*(10 : ℝ)^(d-1)*(1+((n : ℝ)-latticeDistance 0 x))*
    (n : ℝ)^((1 : ℝ)-(d : ℝ))
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hcR : 5*(c : ℝ) ≤ n := by exact_mod_cast hcn
  have htR : ((s/2 : ℕ) : ℝ) ≤ c := by exact_mod_cast (show s/2 ≤ c by omega)
  have hQ : Q ⊆ centeredBox d n := heartAnnulus_subset _ _
  obtain ⟨j,wall,positive,hhalf,hdepth⟩ := cube_nearest_coordinate_halfSpace hd x (hQ hx)
  have hxdepth : 0 ≤ (n : ℝ)-latticeDistance 0 x := by
    have h : 0 ≤ coordinateDepth j wall positive x := hhalf (hQ hx)
    rwa [hdepth] at h
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hwNorm : latticeDistance 0 w ≤ 2*(c : ℝ) := by
    apply (dist_pi_le_iff (by positivity : (0 : ℝ) ≤ 2*(c : ℝ))).mpr
    intro j
    have hb : |w j| ≤ 2*(c : ℤ) := by
      by_cases hj : j = i
      · subst j
        rw [hface,abs_of_nonneg (by omega)]
        omega
      · have hh := htransverse j hj
        omega
    simpa [vertexReal,Real.dist_eq] using (show |(w j : ℝ)| ≤ 2*(c : ℝ) by exact_mod_cast hb)
  have hlocalNorm (z : Vertex d) (hz : z ∈ T) : latticeDistance 0 z ≤ 3*(c : ℝ) := by
    have hdist := cubeCut_distance_le Q w z hz
    have htri := latticeDistance_triangle 0 w z
    linarith
  have hxT : x ∉ T := by
    intro hxt
    have hh := hlocalNorm x hxt
    linarith
  have hsuffix (z : Vertex d) (hz : z ∈ F) : g z ≤ L := by
    have hzT := (Finset.mem_filter.mp hz).1
    have hzQ := (Finset.mem_filter.mp hzT).1
    have hnorm := hlocalNorm z hzT
    have htri := latticeDistance_triangle 0 z x
    rw [latticeDistance_comm z x] at htri
    have hsep : (n : ℝ)/10 ≤ max 1 (latticeDistance x z) := by
      have hh : (n : ℝ)/10 ≤ latticeDistance x z := by linarith
      exact hh.trans (le_max_right _ _)
    have hp := cube_one_sided_connection_le hd C hC panis (Q : Set (Vertex d))
      (fun v hv => hQ hv) x z hx hzQ
    rw [connectionToSetEvent_singleton_symm (Q : Set (Vertex d)) x z] at hp
    have hk := Real.rpow_le_rpow_of_nonpos (by positivity : (0 : ℝ) < (n : ℝ)/10)
      hsep (by linarith : (1 : ℝ)-(d : ℝ) ≤ 0)
    calc
      g z ≤ (2*C)*(1+((n : ℝ)-latticeDistance 0 x))*
          (max 1 (latticeDistance x z))^((1 : ℝ)-(d : ℝ)) := hp
      _ ≤ (2*C)*(1+((n : ℝ)-latticeDistance 0 x))*
          ((n : ℝ)/10)^((1 : ℝ)-(d : ℝ)) :=
        mul_le_mul_of_nonneg_left hk (by positivity)
      _ = L := by rw [tenth_scale_power hd]; dsimp [L]; ring
  have hprefix := local_annulus_face_mass_le_gap hd hs C A B hC hA hB panis arm second
    (centeredBox d n) w i hw hsc hface htransverse
  rw [connectionToSetEvent_singleton_symm (Q : Set (Vertex d)) x w]
  calc
    _ ≤ ∑ z ∈ F, f z*g z := finite_connection_cube_exit_bk (criticalPoint d) Q w x hw hxT
    _ ≤ ∑ z ∈ F, f z*L := Finset.sum_le_sum (fun z hz =>
      mul_le_mul_of_nonneg_left (hsuffix z hz) measureReal_nonneg)
    _ = (∑ z ∈ F, f z)*L := by rw [Finset.sum_mul]
    _ ≤ ((6*(d : ℝ))*(4*C*(A+B)*(9 : ℝ)^(d-1))*(1+(r : ℝ))/(s : ℝ))*L :=
      mul_le_mul_of_nonneg_right hprefix hL
    _ = _ := by dsimp [L]; ring

end NearCritical.Section8
