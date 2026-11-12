module
public import NearCritical.Section8CubeOneSided
public import NearCritical.Section8HeartAnnulus

/-! Direct outer-wall estimate for the small-gap part of RD. -/
@[expose] public section
noncomputable section
namespace NearCritical.Section8
open Set MeasureTheory
open scoped Classical

/-- Points within twice the inner radius have a direct outer-wall estimate.
For source RD gap one, the inner depth is zero and the RD factor is exactly one.
The actual annulus remains the connection domain. -/
theorem annulus_inner_connection_le {d n c : ℕ} (hd : 1 ≤ d) (hn : 1 ≤ n)
    (hcn : 5*c ≤ n) (C : ℝ) (hC : 0 ≤ C)
    (panis : PanisHalfSpaceTwoPointUpper d C) (x w : Vertex d)
    (hx : x ∈ heartAnnulus (centeredBox d n) (centeredBox d c))
    (hw : w ∈ heartAnnulus (centeredBox d n) (centeredBox d c))
    (hxouter : 3*(n : ℝ)/4 ≤ latticeDistance 0 x)
    (hwinner : latticeDistance 0 w ≤ 2*(c : ℝ)) :
    (percolation d (criticalPoint d)).real
      (connectionToSetEvent
        (heartAnnulus (centeredBox d n) (centeredBox d c) : Set (Vertex d)) x {w}) ≤
      ((2*C)*(10 : ℝ)^(d-1))*(1+((n : ℝ)-latticeDistance 0 x))*
        (n : ℝ)^((1 : ℝ)-(d : ℝ)) := by
  let Q := heartAnnulus (centeredBox d n) (centeredBox d c)
  have hQ : Q ⊆ centeredBox d n := heartAnnulus_subset _ _
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hcR : 5*(c : ℝ) ≤ n := by exact_mod_cast hcn
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  obtain ⟨i,wall,positive,hhalf,hdepth⟩ := cube_nearest_coordinate_halfSpace hd x (hQ hx)
  have hxdepth : 0 ≤ (n : ℝ)-latticeDistance 0 x := by
    have hh : 0 ≤ coordinateDepth i wall positive x := hhalf (hQ hx)
    rwa [hdepth] at hh
  have htri := latticeDistance_triangle 0 w x
  rw [latticeDistance_comm w x] at htri
  have hsep : (n : ℝ)/10 ≤ max 1 (latticeDistance x w) := by
    apply le_trans (b := latticeDistance x w) _ (le_max_right _ _)
    linarith
  have hp := cube_one_sided_connection_le hd C hC panis (Q : Set (Vertex d))
    (fun v hv => hQ hv) x w hx hw
  have hk := Real.rpow_le_rpow_of_nonpos (by positivity : (0 : ℝ) < (n : ℝ)/10)
    hsep (by linarith : (1 : ℝ)-(d : ℝ) ≤ 0)
  have hpower : ((n : ℝ)/10)^((1 : ℝ)-(d : ℝ)) =
      (10 : ℝ)^(d-1)*(n : ℝ)^((1 : ℝ)-(d : ℝ)) := by
    have he : (1 : ℝ)-(d : ℝ) = -((d-1 : ℕ) : ℝ) := by
      rw [Nat.cast_sub hd,Nat.cast_one]
      ring
    rw [he,Real.rpow_neg (by positivity : (0 : ℝ) ≤ (n : ℝ)/10),
      Real.rpow_neg (Nat.cast_nonneg n)]
    simp only [Real.rpow_natCast]
    rw [div_pow,inv_div,div_eq_mul_inv]
  calc
    _ ≤ (2*C)*(1+((n : ℝ)-latticeDistance 0 x))*
        (max 1 (latticeDistance x w))^((1 : ℝ)-(d : ℝ)) := hp
    _ ≤ (2*C)*(1+((n : ℝ)-latticeDistance 0 x))*
        ((n : ℝ)/10)^((1 : ℝ)-(d : ℝ)) :=
      mul_le_mul_of_nonneg_left hk (by positivity)
    _ = _ := by rw [hpower]; ring

end NearCritical.Section8
