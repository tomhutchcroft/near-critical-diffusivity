module
public import NearCritical.BulkSupercriticalBound
public import NearCritical.WaterCubeOrdinaryArms

/-! Actual STANDARD ordinary-window specialization at the bulk radius, then
NEW no-log b-delta deduction with the previous scale-specific arm premise
DISCHARGED. No subcritical inhomogeneous exponential gain is claimed. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory

/-- Uniform rescaling of the named standard ordinary-arm window estimate.
The integer scale is floor(delta*h); small scales use probability<=1. -/
theorem ordinaryArm_window_at_bulk_radius {d : ℕ} {C δ h : ℝ}
    (hC : 1 ≤ C) (ordinary : OrdinaryArmWindowInput d C)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hh : 0 < h)
    (p : unitInterval) (hp : (p:ℝ) ≤ (criticalPoint d:ℝ)+1/h^2)
    (x : Vertex d) :
    (percolation d p).real (extrinsicRadiusArmEvent x (δ*h/2)) ≤ (4*C/δ^2)/h^2 := by
  have hC0 : 0 ≤ C := by linarith
  have hδh : 0 ≤ δ*h := mul_nonneg hδ.le hh.le
  by_cases hlarge : 2 ≤ δ*h
  · let n := ⌊δ*h⌋₊
    have hn1 : 1 ≤ n := by
      apply Nat.le_floor
      norm_num
      linarith
    have hnpos : (0:ℝ) < n := by exact_mod_cast (show 0<n by omega)
    have hnf : (n:ℝ) ≤ δ*h := Nat.floor_le hδh
    have hnf' : δ*h < (n:ℝ)+1 := Nat.lt_floor_add_one _
    have hnlo : δ*h/2 ≤ (n:ℝ) := by linarith
    have hnh : (n:ℝ) ≤ h := hnf.trans (by nlinarith)
    have hwin : (p:ℝ) ≤ (criticalPoint d:ℝ)+((n:ℝ)^2)⁻¹ := by
      have hinv : (h^2)⁻¹ ≤ ((n:ℝ)^2)⁻¹ := by
        simpa only [one_div] using one_div_le_one_div_of_le (sq_pos_of_pos hnpos)
          (show (n:ℝ)^2 ≤ h^2 by nlinarith)
      rw [one_div] at hp
      linarith
    have hinc : extrinsicRadiusArmEvent x (δ*h/2) ⊆ extrinsicRadiusArmEvent x ((n:ℝ)/2) := by
      rintro ω ⟨y,hy,hpath⟩
      exact ⟨y,(show (n:ℝ)/2 ≤ δ*h/2 by linarith).trans_lt hy,hpath⟩
    apply ((measureReal_mono hinc).trans (ordinary p x n hn1 hwin)).trans
    rw [div_div]
    apply (div_le_div_iff₀ (sq_pos_of_pos hnpos) (mul_pos (sq_pos_of_pos hδ) (sq_pos_of_pos hh))).mpr
    have hs : δ^2*h^2 ≤ 4*(n:ℝ)^2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hs hC0]
  · have hprob : (percolation d p).real (extrinsicRadiusArmEvent x (δ*h/2)) ≤ 1 := measureReal_le_one
    apply hprob.trans
    rw [div_div]
    apply (le_div_iff₀ (mul_pos (sq_pos_of_pos hδ) (sq_pos_of_pos hh))).mpr
    have hs : (δ*h)^2 ≤ 4 := by nlinarith
    nlinarith

/-- NEW supercritical no-log source b-delta bound from ONLY the named
STANDARD ordinary-window input. Actual domination, BK, geometry and counting
are already proved; no scale-specific arm probability is a hypothesis. -/
theorem waterCube_bulkB_window_of_standard_ordinary {d : ℕ} (i : Fin d)
    {C δ : ℝ} (hC : 1 ≤ C) (ordinary : OrdinaryArmWindowInput d C)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (r R : ℕ) (p s : unitInterval)
    (hp : (p:ℝ) ≤ (criticalPoint d:ℝ)+1/(2*(r:ℝ)+1)^2)
    (hs : (s:ℝ) ≤ (criticalPoint d:ℝ)+1/(2*(r:ℝ)+1)^2) :
    annealedMaskedB (waterCube d i r R) i
      (bulkBondMask (waterCube d i r R) i (2*(r:ℝ)+1) δ) (p:ℝ) (s:ℝ) ≤
        (d:ℝ)*(4*C/δ^2)^2/(2*(r:ℝ)+1)^2 := by
  let P0 := max p s
  have hwin : (P0:ℝ) ≤ (criticalPoint d:ℝ)+1/(2*(r:ℝ)+1)^2 := by
    change max (p:ℝ) (s:ℝ) ≤ _
    exact max_le hp hs
  have hcoef : 0 ≤ 4*C/δ^2 := div_nonneg (by linarith) (sq_nonneg δ)
  exact waterCube_annealedBulkB_supercritical_bound d i r R δ p s P0
    (show (p:ℝ) ≤ (P0:ℝ) from le_max_left _ _) (show (s:ℝ) ≤ (P0:ℝ) from le_max_right _ _)
    (4*C/δ^2) hcoef
    (fun x => ordinaryArm_window_at_bulk_radius hC ordinary hδ hδ1 (by positivity) P0 hwin x)

/-- The literal source integral enjoys the SAME actual-law no-log estimate. -/
theorem waterCube_sourceBulkB_window_of_standard_ordinary {d : ℕ} (i : Fin d)
    {C δ : ℝ} (hC : 1 ≤ C) (ordinary : OrdinaryArmWindowInput d C)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (r R : ℕ) (p s : unitInterval)
    (hp : (p:ℝ) ≤ (criticalPoint d:ℝ)+1/(2*(r:ℝ)+1)^2)
    (hs : (s:ℝ) ≤ (criticalPoint d:ℝ)+1/(2*(r:ℝ)+1)^2) :
    (∫ ω, sourceMaskedQuenchedB (waterCube d i r R) i
      (bulkBondMask (waterCube d i r R) i (2*(r:ℝ)+1) δ) ω
      ∂bulkPercolation (waterCube d i r R) i (2*(r:ℝ)+1) δ p s) ≤
        (d:ℝ)*(4*C/δ^2)^2/(2*(r:ℝ)+1)^2 := by
  rw [← annealedBulkB_eq_sourceIntegral]
  exact waterCube_bulkB_window_of_standard_ordinary i hC ordinary hδ hδ1 r R p s hp hs

end NearCritical
