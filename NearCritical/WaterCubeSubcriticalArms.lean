module
public import NearCritical.WaterCubeOrdinaryArms

/-! Subcritical ordinary-arm input and actual finite-face exponential bounds
needed at the middle layer in source lem.aa_bound. The literature input retains
its literal pc/2<=p<=pc parameter range; extension to smaller p is proved. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory

/-- Named STANDARD source eq.onearm_sub (Hutchcroft2023, CHS23), rescaled to
ordinary supmetric radius n/2. It is NOT a finite-face estimate. -/
def OrdinaryArmSubcriticalInput (d : ℕ) (C b : ℝ) : Prop :=
  ∀ (p : unitInterval) (x : Vertex d) (n : ℕ), 1 ≤ n →
    (criticalPoint d : ℝ)/2 ≤ (p : ℝ) → p ≤ criticalPoint d →
    (percolation d p).real (extrinsicRadiusArmEvent x ((n : ℝ)/2)) ≤
      C/(n : ℝ)^2 * Real.exp (-b * Real.sqrt ((criticalPoint d : ℝ)-(p : ℝ)) * n)

/-- Actual monotone clamping extends the cited parameter range, losing at most
factor two in the exponential rate. -/
theorem ordinaryArm_subcritical_all_parameters {d : ℕ} {C b : ℝ}
    (hC : 0 ≤ C) (hb : 0 ≤ b) (ordinary : OrdinaryArmSubcriticalInput d C b)
    (p : unitInterval) (hp : p ≤ criticalPoint d) (x : Vertex d) (n : ℕ) (hn : 1 ≤ n) :
    (percolation d p).real (extrinsicRadiusArmEvent x ((n : ℝ)/2)) ≤
      C/(n : ℝ)^2 * Real.exp (-(b/2) * Real.sqrt ((criticalPoint d : ℝ)-(p : ℝ)) * n) := by
  let pHalf : unitInterval := ⟨(criticalPoint d : ℝ)/2, by
    constructor
    · exact div_nonneg (criticalPoint d).2.1 (by norm_num)
    · linarith [(criticalPoint d).2.2]⟩
  have hHalfLE : pHalf ≤ criticalPoint d := by
    change (criticalPoint d : ℝ)/2 ≤ (criticalPoint d : ℝ)
    linarith [(criticalPoint d).2.1]
  let q := max p pHalf
  have hpq : p ≤ q := le_max_left _ _
  have hqLower : (criticalPoint d : ℝ)/2 ≤ (q : ℝ) :=
    show (pHalf : ℝ) ≤ (q : ℝ) from le_max_right _ _
  have hqpc : q ≤ criticalPoint d := max_le hp hHalfLE
  have hgap : Real.sqrt ((criticalPoint d : ℝ)-(p : ℝ)) ≤
      2 * Real.sqrt ((criticalPoint d : ℝ)-(q : ℝ)) := by
    by_cases hcase : pHalf ≤ p
    · dsimp only [q]
      rw [max_eq_left hcase]
      linarith [Real.sqrt_nonneg ((criticalPoint d : ℝ)-(p : ℝ))]
    · have hq : q = pHalf := max_eq_right (le_of_not_ge hcase)
      rw [hq]
      apply Real.sqrt_le_iff.mpr
      refine ⟨by positivity, ?_⟩
      rw [mul_pow, Real.sq_sqrt (sub_nonneg.mpr hHalfLE)]
      dsimp [pHalf]
      linarith [p.2.1, (criticalPoint d).2.1]
  calc
    _ ≤ (percolation d q).real (extrinsicRadiusArmEvent x ((n : ℝ)/2)) :=
      percolation_increasing_event_real_mono (measurableSet_extrinsicRadiusArmEvent _ _)
        (extrinsicRadiusArmEvent_increasing _ _) hpq
    _ ≤ _ := ordinary q x n hn hqLower hqpc
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (div_nonneg hC (sq_nonneg _))
      apply Real.exp_le_exp.mpr
      have h := mul_le_mul_of_nonneg_left hgap (mul_nonneg hb (Nat.cast_nonneg n))
      nlinarith

/-- Actual finite-face subcritical bound with a padded depth. This includes
zero-depth connections and all p<=pc, and so applies at every midpoint bond. -/
theorem waterCube_face_subcritical_padded {d : ℕ} {C b : ℝ}
    (hC : 0 ≤ C) (hb : 0 ≤ b) (ordinary : OrdinaryArmSubcriticalInput d C b)
    (p : unitInterval) (hp : p ≤ criticalPoint d) (i : Fin d) (r R : ℕ)
    (upper : Bool) (x : DomainVertex (waterCube d i r R)) :
    (percolation d p).real (waterCubeFaceConnectionEvent i r R upper x) ≤
      (4*C + Real.exp (b/4))/(waterCubeTargetDepth i r upper x.val + 1 : ℝ)^2 *
        Real.exp (-(b/4) * Real.sqrt ((criticalPoint d : ℝ)-(p : ℝ)) *
          (waterCubeTargetDepth i r upper x.val + 1 : ℝ)) := by
  let m := waterCubeTargetDepth i r upper x.val
  let t := Real.sqrt ((criticalPoint d : ℝ)-(p : ℝ))
  have ht : 0 ≤ t := Real.sqrt_nonneg _
  have ht1 : t ≤ 1 := by
    apply Real.sqrt_le_one.mpr
    linarith [p.2.1, (criticalPoint d).2.2]
  by_cases hm : m = 0
  · have hunit : 1 ≤ (4*C + Real.exp (b/4)) * Real.exp (-(b/4)*t) := by
      calc
        1 ≤ Real.exp (b/4 + (-(b/4)*t)) := by
          apply Real.one_le_exp_iff.mpr
          nlinarith
        _ = Real.exp (b/4) * Real.exp (-(b/4)*t) := Real.exp_add _ _
        _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (Real.exp_nonneg _)
    have hprob : (percolation d p).real (waterCubeFaceConnectionEvent i r R upper x) ≤ 1 := measureReal_le_one
    simpa only [← show m = waterCubeTargetDepth i r upper x.val from rfl, hm,
      Nat.cast_zero, zero_add, one_pow, div_one, mul_one] using hprob.trans hunit
  · have hmone : (1 : ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
    have hmpos : (0 : ℝ) < m := by linarith
    have hArm := ordinaryArm_subcritical_all_parameters hC hb ordinary p hp x.val m (by omega)
    have hface : (percolation d p).real (waterCubeFaceConnectionEvent i r R upper x) ≤
        C/(m : ℝ)^2 * Real.exp (-(b/2)*t*m) := by
      apply (measureReal_mono (waterCube_face_subset_extrinsicArm i r R upper x
        (show (m : ℝ)/2 < waterCubeTargetDepth i r upper x.val by change (m : ℝ)/2 < m; linarith))).trans hArm
    have hcoef : C/(m : ℝ)^2 ≤ (4*C+Real.exp (b/4))/(m+1:ℝ)^2 := by
      apply (div_le_div_iff₀ (sq_pos_of_pos hmpos) (by positivity)).mpr
      have hs : (m+1:ℝ)^2 ≤ 4*(m:ℝ)^2 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left hs hC,
        mul_nonneg (Real.exp_nonneg (b/4)) (sq_nonneg (m:ℝ))]
    have hexp : Real.exp (-(b/2)*t*m) ≤ Real.exp (-(b/4)*t*(m+1:ℝ)) := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_nonneg (mul_nonneg hb ht) (show 0 ≤ (m:ℝ)-1 by linarith)]
    exact hface.trans (mul_le_mul hcoef hexp (Real.exp_nonneg _) (by positivity))

end NearCritical
