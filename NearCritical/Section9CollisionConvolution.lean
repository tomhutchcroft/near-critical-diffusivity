module
public import NearCritical.Section9CoalescenceBubble
public import NearCritical.Section8FourthConvolution

/-! Finite four-arm collision contraction for Section 9. -/
@[expose] public section
namespace NearCritical
open MeasureTheory

/-- Contracting the common collision vertex in two actual critical bubbles
produces the eighth-order kernel. All three finite cutoffs are arbitrary. -/
theorem section9_finite_collision_convolution_le {d : ℕ} (hd : 9 ≤ d) {G : ℝ}
    (hG : 0 ≤ G) (green : CriticalSupGreenUpper d G)
    (L R W : Finset (Vertex d)) (x y : Vertex d) :
    ∑ w ∈ W,
      (∑ u ∈ L, twoPoint d (criticalPoint d) x u * twoPoint d (criticalPoint d) w u) *
      (∑ v ∈ R, twoPoint d (criticalPoint d) y v * twoPoint d (criticalPoint d) w v) ≤
      G^4 * ((4 : ℝ)^((d : ℝ)-2)*(2+19*(2*(d : ℝ)*3^(d-1))))^2 *
        ((4 : ℝ)^((d : ℝ)-4)*(162+163*(2*(d : ℝ)*3^(d-1)))) *
        (max 1 (latticeDistance x y))^((8 : ℝ)-(d : ℝ)) := by
  let B : ℝ := (4 : ℝ)^((d : ℝ)-2)*(2+19*(2*(d : ℝ)*3^(d-1)))
  let C : ℝ := (4 : ℝ)^((d : ℝ)-4)*(162+163*(2*(d : ℝ)*3^(d-1)))
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hpoint (w : Vertex d) :
      (∑ u ∈ L, twoPoint d (criticalPoint d) x u * twoPoint d (criticalPoint d) w u) *
      (∑ v ∈ R, twoPoint d (criticalPoint d) y v * twoPoint d (criticalPoint d) w v) ≤
      (G^4*B^2) * ((max 1 (latticeDistance x w))^((4 : ℝ)-(d : ℝ)) *
        (max 1 (latticeDistance y w))^((4 : ℝ)-(d : ℝ))) := by
    calc
      _ ≤ (G^2*(B*(max 1 (latticeDistance x w))^((4 : ℝ)-(d : ℝ)))) *
          (G^2*(B*(max 1 (latticeDistance y w))^((4 : ℝ)-(d : ℝ)))) :=
        mul_le_mul (section9_finite_bubble_le (by omega) hG green L x w)
          (section9_finite_bubble_le (by omega) hG green R y w)
          (Finset.sum_nonneg fun _ _ => mul_nonneg measureReal_nonneg measureReal_nonneg)
          (by positivity)
      _ = _ := by ring
  calc
    _ ≤ ∑ w ∈ W, (G^4*B^2) *
        ((max 1 (latticeDistance x w))^((4 : ℝ)-(d : ℝ)) *
         (max 1 (latticeDistance y w))^((4 : ℝ)-(d : ℝ))) :=
      Finset.sum_le_sum fun w _ => hpoint w
    _ = (G^4*B^2) * (∑ w ∈ W,
        (max 1 (latticeDistance x w))^((4 : ℝ)-(d : ℝ)) *
        (max 1 (latticeDistance y w))^((4 : ℝ)-(d : ℝ))) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ (G^4*B^2) * (C*(max 1 (latticeDistance x y))^((8 : ℝ)-(d : ℝ))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa only [Nat.cast_one] using
        Section8.truncated_fourth_fourth_convolution_le hd 1 (by decide) W x y
    _ = _ := by dsimp [B,C]; ring

end NearCritical
