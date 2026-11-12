module

public import NearCritical.Section10EITMoments
public import Mathlib.Analysis.SpecificLimits.Normed

/-! Uniform geometric constants for Section10 prop.nw.main. The repaired
criterion Lambda*q<1 suffices; the source's stronger half-criterion is unused. -/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open scoped BigOperators

theorem finite_geometric_sum_le_inverse {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) (H : ℕ) :
    (∑ k ∈ Finset.range H, r^k) ≤ (1-r)⁻¹ := by
  have hs := hasSum_geometric_of_lt_one hr hr1
  have h := hs.summable.sum_le_tsum (Finset.range H) (fun k _ => pow_nonneg hr k)
  simpa only [hs.tsum_eq] using h

theorem finite_linear_geometric_sum_le {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) (H : ℕ) :
    (∑ k ∈ Finset.range H, ((k:ℝ)+2)*r^k) ≤ 2/(1-r)^2 := by
  have hn : ‖r‖ < 1 := by simpa only [Real.norm_eq_abs,abs_of_nonneg hr] using hr1
  have hs : HasSum (fun k : ℕ => ((k:ℝ)+2)*r^k)
      (r/(1-r)^2+2*(1-r)⁻¹) := by
    simpa only [← add_mul] using
      (hasSum_coe_mul_geometric_of_norm_lt_one hn).add
        ((hasSum_geometric_of_lt_one hr hr1).mul_left 2)
  have hb := hs.summable.sum_le_tsum (Finset.range H) (fun k _ => by positivity)
  rw [hs.tsum_eq] at hb
  have hd : 1-r ≠ 0 := ne_of_gt (sub_pos.mpr hr1)
  have heq : r/(1-r)^2+2*(1-r)⁻¹ = (2-r)/(1-r)^2 := by
    field_simp [hd]
    <;> ring
  calc
    _ ≤ r/(1-r)^2+2*(1-r)⁻¹ := hb
    _ = (2-r)/(1-r)^2 := heq
    _ ≤ _ := div_le_div_of_nonneg_right (by linarith) (sq_nonneg _)

variable {X : Type*} [Fintype X]

/-- Uniform exponential moment from the raw geometric intersection tail.
Its excess above one is proportional to the initial-hit tail coefficient A. -/
theorem exponential_count_moment_closed (μ : X → ℝ) (N : X → ℕ)
    (hμ : ∀ x, 0 ≤ μ x) (hprob : ∑ x, μ x = 1)
    (H : ℕ) (hN : ∀ x, N x ≤ H) {Λ A q : ℝ}
    (hΛ : 0 ≤ Λ) (hA : 0 ≤ A) (hq : 0 ≤ q) (hsmall : Λ*q < 1)
    (htail : ∀ k, (∑ x, if k+1 ≤ N x then μ x else 0) ≤ A*q^k) :
    (∑ x, μ x*Λ^(N x)) ≤ 1+A*Λ/(1-Λ*q) := by
  have hb := exponential_count_moment_of_tail μ N hμ hprob H hN hΛ hA hq htail
  have hg := finite_geometric_sum_le_inverse (mul_nonneg hΛ hq) hsmall H
  have hh := mul_le_mul_of_nonneg_left hg (mul_nonneg hA hΛ)
  exact hb.trans (by simpa only [div_eq_mul_inv] using add_le_add (le_refl 1) hh)

/-- The energy-count moment is O(A), uniformly in the finite route horizon;
the zero-intersection indicator is retained literally. -/
theorem positive_count_energy_moment_closed (μ : X → ℝ) (N : X → ℕ)
    (hμ : ∀ x, 0 ≤ μ x) (H : ℕ) (hN : ∀ x, N x ≤ H)
    {Λ A q : ℝ} (hΛ : 0 ≤ Λ) (hA : 0 ≤ A) (hq : 0 ≤ q) (hsmall : Λ*q < 1)
    (htail : ∀ k, (∑ x, if k+1 ≤ N x then μ x else 0) ≤ A*q^k) :
    (∑ x, μ x*(if 1 ≤ N x then (1+(N x:ℝ))*Λ^(N x) else 0)) ≤
      2*A*Λ/(1-Λ*q)^2 := by
  have hb := positive_count_energy_moment_of_tail μ N hμ H hN hΛ hA hq htail
  have hg := finite_linear_geometric_sum_le (mul_nonneg hΛ hq) hsmall H
  have hh := mul_le_mul_of_nonneg_left hg (mul_nonneg hA hΛ)
  exact hb.trans (by convert hh using 1 <;> ring)

end NearCritical.Section10
