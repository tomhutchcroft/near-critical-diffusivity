module

public import NearCritical.MaskedArmPhysicalCut

@[expose] public section
namespace NearCritical
open Set MeasureTheory
open scoped Classical ENNReal

/-- An explicit real envelope for the full pioneer mass bounds the actual
finite real cut sum used in the masked-arm product estimate. -/
theorem maskedWaterCube_upper_cut_real_le {d : ℕ} (i : Fin d)
    (r R : ℕ) (δ : ℝ) (p q : unitInterval) (x : Vertex d)
    {B : ℝ} (hB : 0 ≤ B) :
    let U := waterCube d i r R
    let m : ℤ := ⌊δ*(2*(r : ℝ)+1)/2⌋
    let n : ℤ := (2*r+1 : ℤ)-m-1
    twoPhaseSlabPioneerMass i p q m n (x i+(r : ℤ)) n ≤ ENNReal.ofReal B →
    (∑ y ∈ U.filter (fun y => y i+(r : ℤ)=n),
      (bulkPercolation U i (2*(r : ℝ)+1) δ p q).real
        (connectionToSetEvent ((U : Set (Vertex d)) ∩
          finiteHeightSlab i (-(r : ℤ)) (n-r)) x {y})) ≤ B := by
  dsimp only
  intro hmass
  apply (ENNReal.ofReal_le_ofReal_iff hB).mp
  rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => measureReal_nonneg)]
  letI : IsProbabilityMeasure
      (bulkPercolation (waterCube d i r R) i (2*(r : ℝ)+1) δ p q) := by
    change IsProbabilityMeasure (percolationProfile d _)
    infer_instance
  refine le_trans (le_of_eq ?_) ((maskedWaterCube_upper_cut_mass_le i r R δ p q x).trans hmass)
  apply Finset.sum_congr rfl
  intro y _
  exact ofReal_measureReal

end NearCritical
