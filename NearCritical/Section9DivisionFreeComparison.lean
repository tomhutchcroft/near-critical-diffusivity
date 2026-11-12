module
public import NearCritical.Section9AvoidanceComparison
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Division-free energy comparison and finite cluster-fiber averaging. -/
@[expose] public section
noncomputable section
namespace NearCritical
open scoped BigOperators

/-- Unlike a quotient bound, this inequality retains information when energy
is zero. The mass m and probability scale a may both vanish. -/
theorem section9_mass_energy_comparison {ι : Type*} (J : Finset ι)
    (w q : ι → ℝ) (m a T : ℝ) (hm : 0 ≤ m) (ha : 0 ≤ a)
    (hq : ∀ j ∈ J, 0 ≤ q j ∧ q j ≤ a*m)
    (hweighted : m*T ≤ ∑ j ∈ J, w j*q j) :
    m*(max T 0)^2 ≤ a*(∑ j ∈ J, (w j)^2)*(∑ j ∈ J, q j) := by
  have hD : 0 ≤ ∑ j ∈ J, (w j)^2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hQ : 0 ≤ ∑ j ∈ J, q j := Finset.sum_nonneg fun j hj => (hq j hj).1
  by_cases hm0 : m = 0
  · simp only [hm0,zero_mul]
    exact mul_nonneg (mul_nonneg ha hD) hQ
  have hmpos : 0 < m := lt_of_le_of_ne hm (Ne.symm hm0)
  by_cases hT : T ≤ 0
  · simp only [max_eq_right hT,zero_pow (by decide : (2 : ℕ) ≠ 0),mul_zero]
    exact mul_nonneg (mul_nonneg ha hD) hQ
  have hTpos : 0 < T := lt_of_not_ge hT
  rw [max_eq_left hTpos.le]
  have hq2 : (∑ j ∈ J, (q j)^2) ≤ (a*m)*(∑ j ∈ J, q j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    simpa only [pow_two] using mul_le_mul_of_nonneg_right (hq j hj).2 (hq j hj).1
  have hcs := (Finset.sum_mul_sq_le_sq_mul_sq J w q).trans
    (mul_le_mul_of_nonneg_left hq2 hD)
  have hlo : (m*T)^2 ≤ (∑ j ∈ J, w j*q j)^2 := by
    simpa only [pow_two] using mul_self_le_mul_self (mul_nonneg hm hTpos.le) hweighted
  have hcombined := hlo.trans hcs
  apply (mul_le_mul_iff_right₀ hmpos).mp
  nlinarith only [hcombined]

/-- Finite averaging of cross-multiplied fiber estimates. No inverse energy,
positive fiber weight, or positive energy is required. -/
theorem section9_finite_weighted_energy_averaging {ι : Type*} (S : Finset ι)
    (m X Y P : ι → ℝ) (ell : ℝ) (hell : 0 ≤ ell)
    (hm : ∀ c ∈ S, 0 ≤ m c) (hY : ∀ c ∈ S, 0 ≤ Y c)
    (hP : ∀ c ∈ S, 0 ≤ P c)
    (hpoint : ∀ c ∈ S, ell*m c*(X c)^2 ≤ Y c*P c) :
    ell*(∑ c ∈ S, m c*X c)^2 ≤
      (∑ c ∈ S, m c*Y c)*(∑ c ∈ S, P c) := by
  have hMY : 0 ≤ ∑ c ∈ S, m c*Y c :=
    Finset.sum_nonneg fun c hc => mul_nonneg (hm c hc) (hY c hc)
  have hPS : 0 ≤ ∑ c ∈ S, P c := Finset.sum_nonneg hP
  by_cases hell0 : ell = 0
  · simp only [hell0,zero_mul]
    exact mul_nonneg hMY hPS
  have hellpos : 0 < ell := lt_of_le_of_ne hell (Ne.symm hell0)
  have hsq (c : ι) (hc : c ∈ S) :
      (ell*m c*X c)^2 ≤ (ell*m c*Y c)*P c := by
    have hh := mul_le_mul_of_nonneg_left (hpoint c hc) (mul_nonneg hell (hm c hc))
    nlinarith only [hh]
  have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul S
    (fun c hc => mul_nonneg (mul_nonneg hell (hm c hc)) (hY c hc)) hP hsq
  have hsumX : (∑ c ∈ S, ell*m c*X c) = ell*(∑ c ∈ S, m c*X c) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro c _
    ring
  have hsumY : (∑ c ∈ S, ell*m c*Y c) = ell*(∑ c ∈ S, m c*Y c) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro c _
    ring
  rw [hsumX,hsumY] at hcs
  apply (mul_le_mul_iff_right₀ hellpos).mp
  nlinarith only [hcs]

end NearCritical
