module

public import NearCritical.Section9CoalescenceBubble
public import NearCritical.CriticalTriangle
public import NearCritical.Section9RestrictedTripodProbability
public import NearCritical.Section9PivotalMeanUpper
public import NearCritical.Section9CrossSeparated

@[expose] public section
namespace NearCritical
open MeasureTheory
open scoped Classical

/-- A separated finite tripod has the required power decay using only
the finite bubble estimate. No infinite spatial bubble is needed. -/
theorem section9_finite_tripod_decay {d : ℕ} (hd : 5 ≤ d) {G : ℝ}
    (hG : 0 ≤ G) (green : CriticalSupGreenUpper d G)
    (U : Finset (Vertex d)) (a b z : Vertex d) {r : ℝ} (hr : 0 < r)
    (hab : r ≤ latticeDistance a b) (haz : r ≤ latticeDistance a z)
    (hbz : r ≤ latticeDistance b z) :
    let C := G^2 * ((4 : ℝ)^((d : ℝ)-2)*(2+19*(2*(d : ℝ)*3^(d-1))))
    ∑ u ∈ U, twoPoint d (criticalPoint d) a u * twoPoint d (criticalPoint d) b u *
      twoPoint d (criticalPoint d) z u ≤
      (2 * G * C * (2 : ℝ)^((d : ℝ)-2)) * r ^ (6 - 2 * (d : ℝ)) := by
  intro C
  let P := twoPoint d (criticalPoint d)
  let H := G * (r/2)^((2 : ℝ)-(d : ℝ))
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hd' : (5 : ℝ) ≤ d := by exact_mod_cast hd
  have hfar (v u : Vertex d) (h : r/2 ≤ latticeDistance v u) : P v u ≤ H :=
    (green v u).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos (by positivity) (h.trans (le_max_right _ _)) (by linarith)) hG)
  have hBubble (v w : Vertex d) (h : r ≤ latticeDistance v w) :
      ∑ u ∈ U, P v u * P w u ≤ C * r^((4 : ℝ)-(d : ℝ)) := by
    have hC : 0 ≤ C := by dsimp [C]; positivity
    refine (section9_finite_bubble_le hd hG green U v w).trans ?_
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos hr (h.trans (le_max_right _ _)) (by linarith)) hC
  calc
    _ ≤ ∑ u ∈ U, H * (P a u * P z u + P b u * P z u) := by
      apply Finset.sum_le_sum
      intro u _
      have ha0 := twoPoint_nonneg (criticalPoint d) a u
      have hb0 := twoPoint_nonneg (criticalPoint d) b u
      have hz0 := twoPoint_nonneg (criticalPoint d) z u
      by_cases ha : r/2 ≤ latticeDistance a u
      · have hm := mul_le_mul_of_nonneg_right (hfar a u ha) (mul_nonneg hb0 hz0)
        nlinarith [mul_nonneg hH (mul_nonneg ha0 hz0)]
      · have hbu : r/2 ≤ latticeDistance b u := by
          have ht := latticeDistance_triangle a u b
          rw [latticeDistance_comm u b] at ht
          linarith
        have hm := mul_le_mul_of_nonneg_right (hfar b u hbu) (mul_nonneg ha0 hz0)
        nlinarith [mul_nonneg hH (mul_nonneg hb0 hz0)]
    _ = H * ((∑ u ∈ U, P a u * P z u) + ∑ u ∈ U, P b u * P z u) := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib]
    _ ≤ H * (C * r^((4 : ℝ)-(d : ℝ)) + C * r^((4 : ℝ)-(d : ℝ))) :=
      mul_le_mul_of_nonneg_left (add_le_add (hBubble a z haz) (hBubble b z hbz)) hH
    _ = _ := by
      dsimp [H]
      rw [Real.div_rpow hr.le (by norm_num), div_eq_mul_inv,
        ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
      have he : -((2 : ℝ) - (d : ℝ)) = (d : ℝ) - 2 := by ring
      rw [he]
      have hp : r ^ ((2 : ℝ)-(d : ℝ)) * r ^ ((4 : ℝ)-(d : ℝ)) =
          r ^ (6 - 2 * (d : ℝ)) := by
        rw [← Real.rpow_add hr]
        congr 1
        ring
      rw [← hp]
      ring

/-- Restricted BK and finite bubble decay bound the actual joint
connection using only the critical two-point upper bound. -/
theorem section9_restricted_tripod_decay {d : ℕ} (hd : 5 ≤ d) {G : ℝ}
    (hG : 0 ≤ G) (green : CriticalSupGreenUpper d G)
    (U : Finset (Vertex d)) (a b z : Vertex d) {r : ℝ} (hr : 0 < r)
    (hab : r ≤ latticeDistance a b) (haz : r ≤ latticeDistance a z)
    (hbz : r ≤ latticeDistance b z) :
    let C := G^2 * ((4 : ℝ)^((d : ℝ)-2)*(2+19*(2*(d : ℝ)*3^(d-1))))
    (percolation d (criticalPoint d)).real
      (connectionToSetEvent (U : Set (Vertex d)) a {b} ∩
        connectionToSetEvent (U : Set (Vertex d)) a {z}) ≤
      (2 * G * C * (2 : ℝ)^((d : ℝ)-2)) * r ^ (6 - 2 * (d : ℝ)) := by
  intro C
  let P := fun v w => (percolation d (criticalPoint d)).real
    (connectionToSetEvent (U : Set (Vertex d)) v {w})
  have hP (v w : Vertex d) : P v w ≤ twoPoint d (criticalPoint d) v w := by
    simpa only [P, Finset.coe_singleton, Finset.sum_singleton] using
      connectionToSet_probability_le_twoPoint_sum (criticalPoint d) (U : Set (Vertex d)) v {w}
  have hP0 (v w : Vertex d) : 0 ≤ P v w := measureReal_nonneg
  have hP' (u : Vertex d) : P u b ≤ twoPoint d (criticalPoint d) b u := by
    rw [twoPoint_symm (criticalPoint d) b u]
    exact hP u b
  calc
    _ ≤ ∑ u ∈ U, P a u * (P u b * P z u) := by
      simpa only [P, Finset.coe_singleton, Finset.sum_singleton] using
        restricted_joint_connection_probability_le (criticalPoint d) U {z} a b
    _ ≤ ∑ u ∈ U, twoPoint d (criticalPoint d) a u * twoPoint d (criticalPoint d) b u *
        twoPoint d (criticalPoint d) z u := by
      apply Finset.sum_le_sum
      intro u _
      rw [mul_assoc]
      exact mul_le_mul (hP a u)
        (mul_le_mul (hP' u) (hP z u) (hP0 z u) (twoPoint_nonneg _ _ _))
        (mul_nonneg (hP0 u b) (hP0 z u)) (twoPoint_nonneg _ _ _)
    _ ≤ _ := section9_finite_tripod_decay hd hG green U a b z hr hab haz hbz

/-- The Case 2 joint arm to a finite family of third-cube targets,
derived from finite BK and the source two-point asymptotics. -/
theorem section9_cross_finite_joint_arm_le {d : ℕ} (hd : 5 ≤ d)
    (asymptotics : TwoPointAsymptotics d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (i : Fin d) (n : ℕ), 0 < n →
      ∀ (U B : Finset (Vertex d)) (a b : Vertex d),
      a ∈ section9FiniteMiddle i n → b ∈ section9FiniteEndCube i n 0 →
      B ⊆ section9FiniteEndCube i n (2*(n:ℝ)) →
      (percolation d (criticalPoint d)).real
        (connectionToSetEvent (U : Set (Vertex d)) a {b} ∩ connectionToSetEvent (U : Set (Vertex d)) a (B : Set (Vertex d))) ≤
          (B.card : ℝ) * (C * ((n:ℝ)/8) ^ (6 - 2 * (d : ℝ))) := by
  have hd2 : 2 ≤ d := (by decide : 2 ≤ 5).trans hd
  obtain ⟨G, hG, green⟩ := criticalSupGreenUpper_of_asymptotics hd2 asymptotics
  let C := 2 * G * (G^2 * ((4 : ℝ)^((d : ℝ)-2)*(2+19*(2*(d : ℝ)*3^(d-1))))) *
    (2 : ℝ)^((d : ℝ)-2)
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro i n hn U B a b ha hb hB
  let E := fun z => connectionToSetEvent (U : Set (Vertex d)) a {b} ∩ connectionToSetEvent (U : Set (Vertex d)) a {z}
  have hsub : connectionToSetEvent (U : Set (Vertex d)) a {b} ∩ connectionToSetEvent (U : Set (Vertex d)) a (B : Set (Vertex d)) ⊆
      ⋃ z ∈ B, E z := by
    rintro ω ⟨hab, ⟨haD, z, hz, hzD, haz⟩⟩
    exact Set.mem_iUnion.mpr ⟨z, Set.mem_iUnion.mpr ⟨hz, hab, ⟨haD, z, rfl, hzD, haz⟩⟩⟩
  refine (measureReal_mono hsub (measure_ne_top _ _)).trans ((measureReal_biUnion_finset_le B E).trans ?_)
  calc
    _ ≤ ∑ _z ∈ B, C * ((n:ℝ)/8) ^ (6 - 2 * (d : ℝ)) := by
      apply Finset.sum_le_sum
      intro z hz
      obtain ⟨hab, hbz, haz⟩ := section9_cross_terminal_separations i n ha hb (hB hz)
      exact section9_restricted_tripod_decay hd hG.le green U a b z
        (div_pos (by exact_mod_cast hn) (by norm_num)) hab haz hbz
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]

end NearCritical
