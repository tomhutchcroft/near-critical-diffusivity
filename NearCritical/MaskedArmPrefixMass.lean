module

public import NearCritical.SlabPlaneBounds
public import NearCritical.SlabPioneerShift
public import NearCritical.BulkSupercriticalBound

@[expose] public section
namespace NearCritical
open Set MeasureTheory
open scoped Classical ENNReal

/-- The physical lower-cut sum is bounded by the normalized homogeneous
pioneer mass. This uses domination of the bulk law when q ≤ p. -/
theorem maskedWaterCube_lower_cut_real_le {d : ℕ} (i : Fin d)
    (r R : ℕ) (δ : ℝ) (p q : unitInterval) (hqp : q ≤ p)
    (x : Vertex d) (m : ℤ) {B : ℝ} (hB : 0 ≤ B)
    (hmass : slabPioneerMass p i 0 m (x i+(r : ℤ)) m ≤ ENNReal.ofReal B) :
    let U := waterCube d i r R
    (∑ y ∈ U.filter (fun y => y i+(r : ℤ)=m),
      (bulkPercolation U i (2*(r : ℝ)+1) δ p q).real
        (connectionToSetEvent ((U : Set (Vertex d)) ∩
          finiteHeightSlab i (-(r : ℤ)) (m-r)) x {y})) ≤ B := by
  dsimp only
  let U := waterCube d i r R
  let W := U.filter (fun y => y i+(r : ℤ)=m)
  let T := finiteHeightSlab i (-(r : ℤ)) (m-r)
  let A := fun y : Vertex d => connectionToSetEvent ((U : Set (Vertex d)) ∩ T) x {y}
  change (∑ y ∈ W, (bulkPercolation U i (2*(r : ℝ)+1) δ p q).real (A y)) ≤ B
  refine le_trans (Finset.sum_le_sum (fun y _ => ?_))
    (show (∑ y ∈ W, (percolation d p).real (A y)) ≤ B from ?_)
  · rw [bulkPercolation_eq_masked]
    exact maskedPercolation_event_real_le_homogeneous _ p q p le_rfl hqp
      (measurableSet_connectionToSetEvent _ _ _) (connectionToSetEvent_increasing _ _ _)
  · apply (ENNReal.ofReal_le_ofReal_iff hB).mp
    rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => measureReal_nonneg)]
    have hshift : slabPioneerMass p i (-(r : ℤ)) (m-r) (x i) (m-r) =
        slabPioneerMass p i 0 m (x i+(r : ℤ)) m := by
      simpa only [zero_add, sub_eq_add_neg, add_neg_cancel_right] using
        slabPioneerMass_shift p i 0 m (x i+(r : ℤ)) m (-(r : ℤ))
    refine le_trans ?_ (hshift.le.trans hmass)
    rw [← slab_plane_mass_eq_canonical p i _ _ x (m-r)]
    refine le_trans (Finset.sum_le_sum (fun y hy => ?_)) (ENNReal.sum_le_tsum W)
    have hy' : y i = m-r := by
      have h := (Finset.mem_filter.mp hy).2
      omega
    rw [if_pos hy', ofReal_measureReal]
    exact measure_mono (connectionToSetEvent_mono (fun _ hz => hz.2) (Subset.refl _) x)

end NearCritical
