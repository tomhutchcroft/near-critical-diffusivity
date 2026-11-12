module

public import NearCritical.MaskedWaterCubeSuffix

@[expose] public section
namespace NearCritical
open Set MeasureTheory

/-- At a fixed physical cut, the suffix estimate is independent of the
transverse location of the cut vertex. -/
theorem maskedWaterCube_suffix_at_cut {d : ℕ} {Co : ℝ}
    (ordinary : OrdinaryArmWindowInput d Co) (p q : unitInterval) (hqp : q ≤ p)
    (i : Fin d) (r R : ℕ) (δ : ℝ) (S : Set (Vertex d))
    (v : Vertex d) (hv : v ∈ waterCube d i r R)
    (n : ℤ) (hn : n < 2*(r : ℤ)+1) (hvn : v i+(r : ℤ) = n)
    (hp : (p : ℝ) ≤ (criticalPoint d : ℝ)+(((2*r+1 : ℕ) : ℝ)^2)⁻¹) :
    (bulkPercolation (waterCube d i r R) i (2*(r : ℝ)+1) δ p q).real
      (connectionToSetEvent S v (Subtype.val '' positiveFace (waterCube d i r R) i)) ≤
      Co/((2*(r : ℝ)+1-(n : ℝ))^2) := by
  have h := maskedWaterCube_suffix_probability_le_ordinary ordinary p q hqp i r R δ S v hv hp
  have hdepth : ((waterCubeTargetDepth i r true v : ℕ) : ℤ) =
      2*(r : ℤ)+1-n := by
    simp only [waterCubeTargetDepth, waterCubeOppositeDepth, Bool.not_true,
      Bool.false_eq_true, ite_false]
    rw [Int.toNat_of_nonneg (by omega)]
    omega
  have hdepthR : (waterCubeTargetDepth i r true v : ℝ) =
      2*(r : ℝ)+1-(n : ℝ) := by exact_mod_cast hdepth
  simpa only [hdepthR] using h

end NearCritical
