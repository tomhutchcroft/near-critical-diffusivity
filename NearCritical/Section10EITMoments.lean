module

public import Mathlib.Tactic

/-! Section10 prop.nw.main: finite EIT-tail summation. The intersection law
and stochastic pair-process estimates must be supplied by their actual proofs;
the two moment bounds below are derived from the raw tail, not assumed. -/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open scoped Classical BigOperators
variable {X : Type*} [Fintype X]

/-- A nonnegative function of a positive integer count is bounded by summing
its tail indicators. The term at k=N is present; other terms are nonnegative. -/
theorem finite_count_moment_le_tail_sum (μ : X → ℝ) (N : X → ℕ)
    (hμ : ∀ x, 0 ≤ μ x) (H : ℕ) (hN : ∀ x, N x ≤ H)
    (f : ℕ → ℝ) (hf : ∀ k, 0 ≤ f k) :
    (∑ x, μ x*(if 1 ≤ N x then f (N x) else 0)) ≤
      ∑ k ∈ Finset.range H, f (k+1)*(∑ x, if k+1 ≤ N x then μ x else 0) := by
  have hp (x : X) : (if 1 ≤ N x then f (N x) else 0) ≤
      ∑ k ∈ Finset.range H, if k+1 ≤ N x then f (k+1) else 0 := by
    by_cases hn : 1 ≤ N x
    · rw [if_pos hn]
      have hk : N x-1 ∈ Finset.range H := Finset.mem_range.mpr (by have := hN x; omega)
      have hh := Finset.single_le_sum
        (fun k (_ : k ∈ Finset.range H) =>
          show 0 ≤ (if k+1 ≤ N x then f (k+1) else 0) from by
            split_ifs
            · exact hf _
            · exact le_rfl)
        hk
      simpa only [Nat.sub_add_cancel hn,le_refl,if_true] using hh
    · rw [if_neg hn]
      exact Finset.sum_nonneg (fun k _ => by
        split_ifs
        · exact hf _
        · exact le_rfl)
  calc
    _ ≤ ∑ x, μ x*(∑ k ∈ Finset.range H, if k+1 ≤ N x then f (k+1) else 0) :=
      Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (hp x) (hμ x))
    _ = _ := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro x _
      by_cases hk : k+1 ≤ N x <;> simp only [hk,if_true,if_false,mul_zero]
      ring

/-- The EIT tail yields the second-moment geometric series used for W.
The law μ is normalized here; no moment estimate is a premise. -/
theorem exponential_count_moment_of_tail (μ : X → ℝ) (N : X → ℕ)
    (hμ : ∀ x, 0 ≤ μ x) (hprob : ∑ x, μ x = 1)
    (H : ℕ) (hN : ∀ x, N x ≤ H) {Λ A q : ℝ}
    (hΛ : 0 ≤ Λ) (hA : 0 ≤ A) (hq : 0 ≤ q)
    (htail : ∀ k, (∑ x, if k+1 ≤ N x then μ x else 0) ≤ A*q^k) :
    (∑ x, μ x*Λ^(N x)) ≤ 1+A*Λ*(∑ k ∈ Finset.range H, (Λ*q)^k) := by
  have hp (x : X) : Λ^(N x) ≤ 1+(if 1 ≤ N x then Λ^(N x) else 0) := by
    by_cases hn : 1 ≤ N x
    · rw [if_pos hn]; linarith
    · have hz : N x = 0 := by omega
      simp [hz]
  calc
    _ ≤ ∑ x, μ x*(1+(if 1 ≤ N x then Λ^(N x) else 0)) :=
      Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (hp x) (hμ x))
    _ = 1+∑ x, μ x*(if 1 ≤ N x then Λ^(N x) else 0) := by
      simp_rw [mul_add,mul_one]
      rw [Finset.sum_add_distrib,hprob]
    _ ≤ 1+∑ k ∈ Finset.range H, Λ^(k+1)*(∑ x, if k+1 ≤ N x then μ x else 0) :=
      add_le_add (le_refl 1) (finite_count_moment_le_tail_sum μ N hμ H hN
        (fun k => Λ^k) (fun k => pow_nonneg hΛ k))
    _ ≤ 1+∑ k ∈ Finset.range H, Λ^(k+1)*(A*q^k) := by
      exact add_le_add (le_refl 1) (Finset.sum_le_sum
        (fun k _ => mul_le_mul_of_nonneg_left (htail k) (pow_nonneg hΛ _)))
    _ = _ := by
      rw [Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro k _
      rw [pow_succ,mul_pow]
      ring

/-- The EIT tail retains the positive-count indicator in the energy moment,
including the zero-intersection branch that must vanish. -/
theorem positive_count_energy_moment_of_tail (μ : X → ℝ) (N : X → ℕ)
    (hμ : ∀ x, 0 ≤ μ x) (H : ℕ) (hN : ∀ x, N x ≤ H)
    {Λ A q : ℝ} (hΛ : 0 ≤ Λ) (hA : 0 ≤ A) (hq : 0 ≤ q)
    (htail : ∀ k, (∑ x, if k+1 ≤ N x then μ x else 0) ≤ A*q^k) :
    (∑ x, μ x*(if 1 ≤ N x then (1+(N x:ℝ))*Λ^(N x) else 0)) ≤
      A*Λ*(∑ k ∈ Finset.range H, ((k:ℝ)+2)*(Λ*q)^k) := by
  calc
    _ ≤ ∑ k ∈ Finset.range H, (1+((k+1:ℕ):ℝ))*Λ^(k+1)*
        (∑ x, if k+1 ≤ N x then μ x else 0) :=
      finite_count_moment_le_tail_sum μ N hμ H hN
        (fun k => (1+(k:ℝ))*Λ^k) (fun k => by positivity)
    _ ≤ ∑ k ∈ Finset.range H, (1+((k+1:ℕ):ℝ))*Λ^(k+1)*(A*q^k) := by
      exact Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_left (htail k) (by positivity))
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      rw [pow_succ,mul_pow]
      push_cast
      ring

end NearCritical.Section10
