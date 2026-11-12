module

public import NearCritical.SplitCrossMoatMass
public import NearCritical.SplitCrossMoatDeletion
public import NearCritical.Section8BoundaryKernels
public import NearCritical.ThreePointTreeGraphDerivation

/-! Bounds on the BK deletion loss for interior and face-terminal edges.
The endpoint separation supplies one macroscopic decay factor, leaving
the small Green mass of the removed vertices at either endpoint. -/
@[expose] public section
noncomputable section

namespace NearCritical.SplitCrossDirect

open MeasureTheory
open scoped Classical

def moatDeletionLoss {d : ℕ} (p : unitInterval) (T F : Finset (Vertex d))
    (x y : Vertex d) : ℝ :=
  ∑ z ∈ F ∩ T,
    (percolation d p).real (connectionToSetEvent (T : Set (Vertex d)) x {z}) *
      (percolation d p).real (connectionToSetEvent (T : Set (Vertex d)) z {y})

private theorem restricted_connection_le_moatGreen {d : ℕ} {G : ℝ}
    (green : CriticalSupGreenUpper d G) (T : Set (Vertex d)) (x y : Vertex d) :
    (percolation d (criticalPoint d)).real (connectionToSetEvent T x {y}) ≤
      G * moatGreen x y :=
  (measureReal_mono (connectionToSetEvent_singleton_subset T x y) (measure_ne_top _ _)).trans
    (green x y)

private theorem moatGreen_comm {d : ℕ} (x y : Vertex d) : moatGreen x y = moatGreen y x := by
  unfold moatGreen
  rw [latticeDistance_comm]

theorem interior_moatDeletionLoss_le {d : ℕ} (hd : 2 ≤ d)
    {G : ℝ} (hG : 0 ≤ G) (green : CriticalSupGreenUpper d G)
    (T F : Finset (Vertex d)) (x y : Vertex d) {s : ℝ} (hs : 0 < s)
    (hxy : 2 * s ≤ latticeDistance x y) :
    moatDeletionLoss (criticalPoint d) T F x y ≤
      (G^2 * s ^ ((2 : ℝ) - (d : ℝ))) *
        ((∑ z ∈ F, moatGreen x z) + (∑ z ∈ F, moatGreen y z)) := by
  let K := s ^ ((2 : ℝ) - (d : ℝ))
  have hK : 0 ≤ K := Real.rpow_nonneg hs.le _
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hfar {a b : Vertex d} (hab : s ≤ latticeDistance a b) : moatGreen a b ≤ K :=
    Real.rpow_le_rpow_of_nonpos hs (hab.trans (le_max_right _ _)) (by linarith)
  unfold moatDeletionLoss
  calc
    _ ≤ ∑ z ∈ F ∩ T, (G^2 * K) * (moatGreen x z + moatGreen y z) := by
      apply Finset.sum_le_sum
      intro z _
      have hsep := latticeDistance_triangle x z y
      have hprod : moatGreen x z * moatGreen y z ≤ K * (moatGreen x z + moatGreen y z) := by
        by_cases hx : s ≤ latticeDistance x z
        · exact (mul_le_mul_of_nonneg_right (hfar hx) (moatGreen_nonneg y z)).trans
            (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (moatGreen_nonneg x z)) hK)
        · have hy : s ≤ latticeDistance y z := by
            rw [latticeDistance_comm y z]
            linarith
          calc
            _ ≤ moatGreen x z * K := mul_le_mul_of_nonneg_left (hfar hy) (moatGreen_nonneg x z)
            _ = K * moatGreen x z := mul_comm _ _
            _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (moatGreen_nonneg y z)) hK
      calc
        _ ≤ (G * moatGreen x z) * (G * moatGreen z y) :=
          mul_le_mul (restricted_connection_le_moatGreen green _ x z)
            (restricted_connection_le_moatGreen green _ z y) measureReal_nonneg
            (mul_nonneg hG (moatGreen_nonneg x z))
        _ = G^2 * (moatGreen x z * moatGreen y z) := by rw [moatGreen_comm z y]; ring
        _ ≤ _ := by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hprod (sq_nonneg G)
    _ ≤ ∑ z ∈ F, (G^2 * K) * (moatGreen x z + moatGreen y z) :=
      Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_left
        (fun z _ _ => mul_nonneg (mul_nonneg (sq_nonneg G) hK)
          (add_nonneg (moatGreen_nonneg x z) (moatGreen_nonneg y z)))
    _ = _ := by rw [← Finset.mul_sum, Finset.sum_add_distrib]

/-- A face endpoint has zero half-space depth. If every removed vertex is
far from that face endpoint, its arm supplies the full boundary decay. -/
theorem face_moatDeletionLoss_le {d : ℕ} (hd : 1 ≤ d)
    {G C : ℝ} (hG : 0 ≤ G) (green : CriticalSupGreenUpper d G)
    (hC : 0 ≤ C) (panis : Section8.PanisHalfSpaceTwoPointUpper d C)
    (T F : Finset (Vertex d)) (x y : Vertex d) (i : Fin d) (cut : ℤ) (positive : Bool)
    (hT : (T : Set (Vertex d)) ⊆ Section8.coordinateHalfSpace i cut positive)
    (hy : y ∈ T) (hdepth : Section8.coordinateDepth i cut positive y = 0)
    {s : ℝ} (hs : 0 < s) (hsep : ∀ z ∈ F ∩ T, s ≤ latticeDistance y z) :
    moatDeletionLoss (criticalPoint d) T F x y ≤
      ((2*C)*G * s ^ ((1 : ℝ) - (d : ℝ))) * ∑ z ∈ F, moatGreen x z := by
  let K := s ^ ((1 : ℝ) - (d : ℝ))
  have hK : 0 ≤ K := Real.rpow_nonneg hs.le _
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hcoef : 0 ≤ (2*C)*G*K := by positivity
  unfold moatDeletionLoss
  calc
    _ ≤ ∑ z ∈ F ∩ T, ((2*C)*G*K) * moatGreen x z := by
      apply Finset.sum_le_sum
      intro z hz
      have hzT := (Finset.mem_inter.mp hz).2
      have hbound := Section8.restricted_halfSpace_one_sided C hC panis i cut positive
        (T : Set (Vertex d)) hT y z hy hzT
      rw [hdepth, add_zero, mul_one] at hbound
      have hpow : (max 1 (latticeDistance y z)) ^ ((1 : ℝ) - (d : ℝ)) ≤ K :=
        Real.rpow_le_rpow_of_nonpos hs ((hsep z hz).trans (le_max_right _ _)) (by linarith)
      have hb : (percolation d (criticalPoint d)).real
          (connectionToSetEvent (T : Set (Vertex d)) z {y}) ≤ (2*C)*K := by
        rw [connectionToSetEvent_singleton_symm _ z y]
        exact hbound.trans (mul_le_mul_of_nonneg_left hpow (by positivity))
      calc
        _ ≤ (G * moatGreen x z) * ((2*C)*K) :=
          mul_le_mul (restricted_connection_le_moatGreen green _ x z) hb
            measureReal_nonneg (mul_nonneg hG (moatGreen_nonneg x z))
        _ = _ := by ring
    _ ≤ ∑ z ∈ F, ((2*C)*G*K) * moatGreen x z :=
      Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_left
        (fun z _ _ => mul_nonneg hcoef (moatGreen_nonneg x z))
    _ = _ := by rw [← Finset.mul_sum]

end NearCritical.SplitCrossDirect
