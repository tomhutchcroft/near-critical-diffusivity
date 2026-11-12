module

public import NearCritical.HalfSpaceInteriorArmBounds

/-! Literal two-branch prop.onearm_half_plus, with all NEW deductions proved.
The cited L1/L2/finite DM and classical nontriviality of pc remain explicit. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Set MeasureTheory

/-- Source prop.onearm_half_plus: the SAME positive constants are fixed before
all parameters and scales, for the actual full-half-space arm event. All new
arm/cluster conclusions have been discharged; only named standard inputs remain. -/
theorem halfSpace_onearm_extension_of_standard_inputs {d : ℕ} (i : Fin d)
    {E A B b : ℝ} (hE : 0 < E) (hA : 0 < A) (hB : 0 < B) (hb : 0 < b)
    (hpc : 0 < (criticalPoint d : ℝ)) (hpc1 : (criticalPoint d : ℝ) < 1)
    (criticalArm : HalfSpaceCriticalArmInput i A)
    (pioneers : HalfSpacePioneerExponentialInput i B b)
    (entropic : FiniteHalfSpaceEntropicInput i E) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (p : unitInterval) (k n : ℕ), 1 ≤ n → 2 * k ≤ n →
      ((criticalPoint d : ℝ) < (p : ℝ) →
        (p : ℝ) ≤ (criticalPoint d : ℝ) + ((n : ℝ) ^ 2)⁻¹ →
        (percolation d p).real (halfSpaceArmEvent i k n) ≤ C * ((k + 1 : ℝ) / (n : ℝ) ^ 3)) ∧
      (p ≤ criticalPoint d →
        (percolation d p).real (halfSpaceArmEvent i k n) ≤ C * ((k + 1 : ℝ) / (n : ℝ) ^ 3) *
          Real.exp (-c * Real.sqrt ((criticalPoint d : ℝ) - (p : ℝ)) * (n : ℝ))) := by
  obtain ⟨K, hK, hsuper⟩ := halfSpace_entropic_transfer_of_standard_inputs i hE hA hB hb
    hpc hpc1 criticalArm pioneers entropic
  let C := max K (halfSpaceInteriorArmConstant d A B b)
  refine ⟨C, b / 12, lt_of_lt_of_le hK (le_max_left _ _), by positivity, ?_⟩
  intro p k n hn hk
  constructor
  · intro hp hwindow
    exact (hsuper p k n hn hk hp hwindow).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  · intro hp
    have hsub : (percolation d p).real (halfSpaceArmEvent i k n) ≤
        halfSpaceInteriorArmConstant d A B b * (k + 1 : ℝ) / (n : ℝ) ^ 3 *
          Real.exp (-(b / 12) * Real.sqrt ((criticalPoint d : ℝ) - (p : ℝ)) * (n : ℝ)) := by
      simpa only [halfSpaceArmEvent, halfSpaceArmDomain, halfSpaceArmTarget] using
        halfSpace_interior_subcritical_real i hA hB hb hpc criticalArm pioneers p hp
          (halfSpaceArmBase i k) k n (by simp [halfSpaceArmBase]) hn hk
    calc
      _ ≤ _ := hsub
      _ = halfSpaceInteriorArmConstant d A B b * ((k + 1 : ℝ) / (n : ℝ) ^ 3) *
          Real.exp (-(b / 12) * Real.sqrt ((criticalPoint d : ℝ) - (p : ℝ)) * (n : ℝ)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)) (Real.exp_nonneg _)

end NearCritical
