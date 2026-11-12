module

public import NearCritical.Section9CoalescenceCaseOneConditional
public import NearCritical.Section9CoalescenceRegularKernel
public import NearCritical.Section9CoalescenceCaseThree

@[expose] public section
namespace NearCritical

/-- Collect the Case 1 factors, leaving only the root-pair bubble kernel
and the separated-arm power. -/
theorem section9_case_one_scale_factors {d : ℕ} {n C M M₀ q q₀ N K : ℝ}
    (hn : 0 < n) (hC : 0 ≤ C) (hM : 0 ≤ M) (hq : 0 ≤ q)
    (hN : 0 ≤ N) (hK : 0 ≤ K)
    (hMass : M ≤ M₀ * n ^ (2 : ℝ)) (hOpen : q ≤ q₀ * n ^ (-2 : ℝ)) :
    (N * (C * (n/8)^((2:ℝ)-(d:ℝ)))) * (M * K) * q ≤
      N * ((M₀ * q₀) * (C / 8^((2:ℝ)-(d:ℝ)))) * n^((2:ℝ)-(d:ℝ)) * K := by
  have hMq := section9_single_opening_mass_le hn hM hq hMass hOpen
  calc
    _ = (M * q) * (N * (C * (n/8)^((2:ℝ)-(d:ℝ))) * K) := by ring
    _ ≤ (M₀ * q₀) * (N * (C * (n/8)^((2:ℝ)-(d:ℝ))) * K) :=
      mul_le_mul_of_nonneg_right hMq (by positivity)
    _ = _ := by
      rw [Real.div_rpow hn.le (by norm_num : (0 : ℝ) ≤ 8)]
      ring

end NearCritical
