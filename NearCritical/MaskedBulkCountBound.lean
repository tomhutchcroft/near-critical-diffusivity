module

public import NearCritical.BulkSupercriticalBound

@[expose] public section
namespace NearCritical
open Finset MeasureTheory
open scoped Classical

/-- A uniform bound on the actual masked two-arm probabilities transfers to
the normalized auxiliary energy by counting only the bulk bonds. -/
theorem waterCube_annealedBulkB_le_of_uniform_twoArm
    (d : ℕ) (i : Fin d) (r R : ℕ) (δ : ℝ) (p s : unitInterval)
    (K : ℝ) (hK : 0 ≤ K)
    (hArm : ∀ e ∈ bulkBondMask (waterCube d i r R) i (2*(r:ℝ)+1) δ,
      (bulkPercolation (waterCube d i r R) i (2*(r:ℝ)+1) δ p s).real
        {ω | sourceTwoArm (waterCube d i r R) i ω e} ≤ K / (2*(r:ℝ)+1)^4) :
    annealedMaskedB (waterCube d i r R) i
      (bulkBondMask (waterCube d i r R) i (2*(r:ℝ)+1) δ) (p : ℝ) (s : ℝ) ≤
      (d : ℝ) * K / (2*(r:ℝ)+1)^2 := by
  let U := waterCube d i r R
  let height : ℝ := 2*(r:ℝ)+1
  let M := bulkBondMask U i height δ
  have hheight : 0 < height := by dsimp [height]; positivity
  have hvol : 0 < (U.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr (waterCube_nonempty d i r R)
  obtain ⟨l, hl⟩ := negativeFace_nonempty (waterCube_nonempty d i r R) i
  obtain ⟨h, hh⟩ := positiveFace_nonempty (waterCube_nonempty d i r R) i
  have hb := annealedBulkB_le_sourceTwoArm_probabilities U i height δ hl hh p s
  rw [waterCube_face_height d i r R hl hh] at hb
  have hsum : (∑ e ∈ M, (bulkPercolation U i height δ p s).real
      {ω | sourceTwoArm U i ω e}) ≤ (M.card : ℝ) * (K / height^4) := by
    calc
      _ ≤ ∑ _e ∈ M, (K / height^4) := by
        apply sum_le_sum
        intro e he
        exact hArm e he
      _ = _ := by simp
  have hm : (M.card : ℝ) ≤ (d : ℝ) * (U.card : ℝ) := by
    exact_mod_cast card_issuedBondMask_le U M
  have hsum' := hsum.trans (mul_le_mul_of_nonneg_right hm (div_nonneg hK (pow_nonneg hheight.le 4)))
  calc
    _ ≤ height^2 / (U.card : ℝ) * (∑ e ∈ M, (bulkPercolation U i height δ p s).real
        {ω | sourceTwoArm U i ω e}) := hb
    _ ≤ height^2 / (U.card : ℝ) * (((d : ℝ) * (U.card : ℝ)) * (K / height^4)) :=
      mul_le_mul_of_nonneg_left hsum' (div_nonneg (sq_nonneg _) hvol.le)
    _ = _ := by
      change height^2 / (U.card : ℝ) * (((d : ℝ) * (U.card : ℝ)) * (K / height^4)) =
        (d : ℝ) * K / height^2
      field_simp [ne_of_gt hheight, ne_of_gt hvol]

end NearCritical
