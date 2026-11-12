module
public import NearCritical.Section9CoalescenceBubble
public import NearCritical.Section9RestrictedTripodProbability
public import NearCritical.Section9PivotalMeanUpper

/-! Actual finite tripod error with a potentially microscopic near-root pair.
The shifted root needs only n/8 separation from the distant target. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory
open scoped Classical BigOperators

/-- The actual finite three-arm diagram has macroscopic n^(2-d) decay and
retains the clipped near-pair kernel of order 4-d. No infinite bubble or
multipoint tree-graph estimate is an input. -/
theorem section8_extension_finite_tripod_error_le {d : ℕ} (hd : 5 ≤ d) {G : ℝ}
    (hG : 0 ≤ G) (green : CriticalSupGreenUpper d G)
    (U : Finset (Vertex d)) (a y z : Vertex d) (n : ℝ) (hn : 1 ≤ n)
    (haz : n/8 ≤ latticeDistance a z) (hyz : n/4 ≤ latticeDistance y z)
    (hay : max 1 (latticeDistance a y) ≤ 2*n) :
    let Cb := (4 : ℝ)^((d : ℝ)-2)*(2+19*(2*(d : ℝ)*3^(d-1)))
    ∑ u ∈ U, twoPoint d (criticalPoint d) a u * twoPoint d (criticalPoint d) y u *
      twoPoint d (criticalPoint d) z u ≤
      (G^3*Cb*(16 : ℝ)^((d : ℝ)-2)*(1+(8 : ℝ)^((d : ℝ)-4))) *
        n^((2 : ℝ)-(d : ℝ))*(max 1 (latticeDistance a y))^((4 : ℝ)-(d : ℝ)) := by
  intro Cb
  let P := twoPoint d (criticalPoint d)
  let k : ℝ := max 1 (latticeDistance a y)
  let B : ℝ := G^2*Cb
  let H : ℝ := G*(n/16)^((2 : ℝ)-(d : ℝ))
  have hn0 : 0 < n := zero_lt_one.trans_le hn
  have hk1 : 1 ≤ k := le_max_left _ _
  have hk0 : 0 < k := zero_lt_one.trans_le hk1
  have hdR : (5 : ℝ) ≤ d := by exact_mod_cast hd
  have hCb : 0 ≤ Cb := by dsimp [Cb]; positivity
  have hB : 0 ≤ B := mul_nonneg (sq_nonneg G) hCb
  have hH : 0 ≤ H := mul_nonneg hG (Real.rpow_nonneg (by positivity) _)
  have hfar (v u : Vertex d) (h : n/16 ≤ latticeDistance v u) : P v u ≤ H :=
    (green v u).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos (by positivity)
        (h.trans (le_max_right _ _)) (by linarith)) hG)
  have hBubbleAY : ∑ u ∈ U, P a u*P y u ≤ B*k^((4 : ℝ)-(d : ℝ)) := by
    simpa only [P,B,Cb,k,mul_assoc] using section9_finite_bubble_le hd hG green U a y
  have hKernelYZ : (max 1 (latticeDistance y z))^((4 : ℝ)-(d : ℝ)) ≤
      (8 : ℝ)^((d : ℝ)-4)*k^((4 : ℝ)-(d : ℝ)) := by
    have hbase : k/8 ≤ max 1 (latticeDistance y z) :=
      (show k/8 ≤ n/4 by dsimp only [k]; linarith).trans
        (hyz.trans (le_max_right _ _))
    calc
      _ ≤ (k/8)^((4 : ℝ)-(d : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) hbase (by linarith)
      _ = _ := by
        rw [Real.div_rpow hk0.le (by norm_num : (0 : ℝ) ≤ 8),div_eq_mul_inv,
          ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 8)]
        have he : -((4 : ℝ)-(d : ℝ)) = (d : ℝ)-4 := by ring
        rw [he]
        ring
  have hBubbleYZ : ∑ u ∈ U, P y u*P z u ≤
      B*((8 : ℝ)^((d : ℝ)-4)*k^((4 : ℝ)-(d : ℝ))) := by
    have hb : ∑ u ∈ U, P y u*P z u ≤ B*(max 1 (latticeDistance y z))^((4 : ℝ)-(d : ℝ)) := by
      simpa only [P,B,Cb,mul_assoc] using section9_finite_bubble_le hd hG green U y z
    exact hb.trans (mul_le_mul_of_nonneg_left hKernelYZ hB)
  calc
    _ ≤ ∑ u ∈ U, H*(P a u*P y u+P y u*P z u) := by
      apply Finset.sum_le_sum
      intro u _
      have ha0 : 0 ≤ P a u := twoPoint_nonneg (criticalPoint d) a u
      have hy0 : 0 ≤ P y u := twoPoint_nonneg (criticalPoint d) y u
      have hz0 : 0 ≤ P z u := twoPoint_nonneg (criticalPoint d) z u
      by_cases hzu : n/16 ≤ latticeDistance z u
      · have hm := mul_le_mul_of_nonneg_left (hfar z u hzu) (mul_nonneg ha0 hy0)
        have hp := mul_nonneg hH (mul_nonneg hy0 hz0)
        nlinarith only [hm,hp]
      · have hau : n/16 ≤ latticeDistance a u := by
          have ht := latticeDistance_triangle a u z
          rw [latticeDistance_comm u z] at ht
          linarith
        have hm := mul_le_mul_of_nonneg_right (hfar a u hau) (mul_nonneg hy0 hz0)
        have hp := mul_nonneg hH (mul_nonneg ha0 hy0)
        nlinarith only [hm,hp]
    _ = H*((∑ u ∈ U, P a u*P y u)+(∑ u ∈ U, P y u*P z u)) := by
      rw [← Finset.mul_sum,Finset.sum_add_distrib]
    _ ≤ H*(B*k^((4 : ℝ)-(d : ℝ))+
        B*((8 : ℝ)^((d : ℝ)-4)*k^((4 : ℝ)-(d : ℝ)))) :=
      mul_le_mul_of_nonneg_left (add_le_add hBubbleAY hBubbleYZ) hH
    _ = _ := by
      dsimp only [H,B,k]
      rw [Real.div_rpow hn0.le (by norm_num : (0 : ℝ) ≤ 16),div_eq_mul_inv,
        ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 16)]
      have he : -((2 : ℝ)-(d : ℝ)) = (d : ℝ)-2 := by ring
      rw [he]
      ring

/-- The finite diagram bound controls the actual restricted two-connection
probability by proved finite BK, including coincident near roots and zero legs. -/
theorem section8_extension_restricted_joint_error_le {d : ℕ} (hd : 5 ≤ d) {G : ℝ}
    (hG : 0 ≤ G) (green : CriticalSupGreenUpper d G)
    (U : Finset (Vertex d)) (a y z : Vertex d) (n : ℝ) (hn : 1 ≤ n)
    (haz : n/8 ≤ latticeDistance a z) (hyz : n/4 ≤ latticeDistance y z)
    (hay : max 1 (latticeDistance a y) ≤ 2*n) :
    let Cb := (4 : ℝ)^((d : ℝ)-2)*(2+19*(2*(d : ℝ)*3^(d-1)))
    (percolation d (criticalPoint d)).real
      (connectionToSetEvent (U : Set (Vertex d)) a {y} ∩
       connectionToSetEvent (U : Set (Vertex d)) a {z}) ≤
      (G^3*Cb*(16 : ℝ)^((d : ℝ)-2)*(1+(8 : ℝ)^((d : ℝ)-4))) *
        n^((2 : ℝ)-(d : ℝ))*(max 1 (latticeDistance a y))^((4 : ℝ)-(d : ℝ)) := by
  intro Cb
  let P := fun v w => (percolation d (criticalPoint d)).real
    (connectionToSetEvent (U : Set (Vertex d)) v {w})
  have hP (v w : Vertex d) : P v w ≤ twoPoint d (criticalPoint d) v w := by
    simpa only [P,Finset.coe_singleton,Finset.sum_singleton] using
      connectionToSet_probability_le_twoPoint_sum (criticalPoint d) (U : Set (Vertex d)) v {w}
  have hP0 (v w : Vertex d) : 0 ≤ P v w := measureReal_nonneg
  have hPy (u : Vertex d) : P u y ≤ twoPoint d (criticalPoint d) y u := by
    rw [twoPoint_symm (criticalPoint d) y u]
    exact hP u y
  calc
    _ ≤ ∑ u ∈ U, P a u*(P u y*P z u) := by
      simpa only [P,Finset.coe_singleton,Finset.sum_singleton] using
        restricted_joint_connection_probability_le (criticalPoint d) U {z} a y
    _ ≤ ∑ u ∈ U, twoPoint d (criticalPoint d) a u * twoPoint d (criticalPoint d) y u *
        twoPoint d (criticalPoint d) z u := by
      apply Finset.sum_le_sum
      intro u _
      rw [mul_assoc]
      exact mul_le_mul (hP a u)
        (mul_le_mul (hPy u) (hP z u) (hP0 z u) (twoPoint_nonneg _ _ _))
        (mul_nonneg (hP0 u y) (hP0 z u)) (twoPoint_nonneg _ _ _)
    _ ≤ _ := section8_extension_finite_tripod_error_le hd hG green U a y z n hn haz hyz hay

end NearCritical
