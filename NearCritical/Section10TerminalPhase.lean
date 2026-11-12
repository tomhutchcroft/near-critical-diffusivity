module

public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.Tactic

/-! Section10 shared terminal-exit distinction. Scalar facts only: identical
exit indicators need not contract, and one bounded terminal factor costs a
constant. -/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open scoped Classical BigOperators
variable {X : Type*} [Fintype X]

/-- Two identical normalized exit indicators have mean inverse success
probability, rather than the interior-step two-thirds contraction. -/
theorem coincident_exit_product_mean (μ : X → ℝ) (A : Set X)
    (hs : (∑ x, if x ∈ A then μ x else 0) ≠ 0) :
    (∑ x, μ x*(if x ∈ A then (∑ y, if y ∈ A then μ y else 0)⁻¹ else 0)^2) =
      (∑ y, if y ∈ A then μ y else 0)⁻¹ := by
  let s := ∑ y, if y ∈ A then μ y else 0
  have hs' : s ≠ 0 := hs
  change (∑ x, μ x*(if x ∈ A then s⁻¹ else 0)^2) = s⁻¹
  calc
    _ = (∑ x, if x ∈ A then μ x else 0)*(s⁻¹)^2 := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : x ∈ A <;> simp [hx]
    _ = s⁻¹ := by
      change s*(s⁻¹)^2 = s⁻¹
      field_simp [hs'] <;> ring

/-- An exit event of probability at most one gives a direct obstruction to
extending the interior coin-based contraction verbatim to coincident exits. -/
theorem coincident_exit_not_two_thirds_contraction (μ : X → ℝ) (A : Set X)
    (hs : 0 < ∑ x, if x ∈ A then μ x else 0)
    (hs1 : (∑ x, if x ∈ A then μ x else 0) ≤ 1) :
    (2/3:ℝ) < ∑ x, μ x*(if x ∈ A then (∑ y, if y ∈ A then μ y else 0)⁻¹ else 0)^2 := by
  rw [coincident_exit_product_mean μ A hs.ne']
  have hge : (1:ℝ) ≤ (∑ x, if x ∈ A then μ x else 0)⁻¹ := by
    rw [inv_eq_one_div]
    exact (le_div_iff₀ hs).mpr (by simpa using hs1)
  linarith

/-- The corrected scalar phase budget tolerates ONE terminal rho² factor:
for epsilon<=1/4, rho² times every finite two-thirds tail sum is below4.
Actual phase-tail domination and terminal indexing remain to prove. -/
theorem finite_phase_terminal_factor_le_four {ε : ℝ} (hε : 0 ≤ ε) (hsmall : ε ≤ 1/4)
    (n : ℕ) :
    (1+ε/2)^2*(∑ j ∈ Finset.range n, (2/3:ℝ)^j) ≤ 4 := by
  have hρ0 : 0 ≤ 1+ε/2 := by linarith
  have hρ : 1+ε/2 ≤ (9/8:ℝ) := by linarith
  have hρsq : (1+ε/2)^2 ≤ (9/8:ℝ)^2 :=
    (sq_le_sq₀ hρ0 (by norm_num)).mpr hρ
  have hsum0 : 0 ≤ ∑ j ∈ Finset.range n, (2/3:ℝ)^j :=
    Finset.sum_nonneg (fun j _ => pow_nonneg (by norm_num) j)
  have hsum : (∑ j ∈ Finset.range n, (2/3:ℝ)^j) ≤ 3 := by
    have hg := geom_sum_mul_neg (2/3:ℝ) n
    have hp := pow_nonneg (by norm_num : (0:ℝ) ≤ 2/3) n
    nlinarith
  have h := mul_le_mul hρsq hsum hsum0 (by norm_num : (0:ℝ) ≤ (9/8:ℝ)^2)
  exact h.trans (by norm_num)

end NearCritical.Section10
