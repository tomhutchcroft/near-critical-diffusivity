module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Tactic

/-! Harmonic-sum bound `∑_{s=1}^{N} 1/s ≤ 1 + log N`, the `log n` ingredient behind the
Appendix-B remote-distance counting estimate `eq.RD_count`
(`∑_{w∈RD} s_w^{-2} ≲ ∑_{s=1}^{c₁n} s · n^{d-2} · s^{-2} = n^{d-2} ∑ 1/s ≲ n^{d-2} log n`).
Non-probabilistic; proved from `Real.log_le_sub_one_of_pos` + telescoping. -/
@[expose] public section
namespace NearCritical.AppendixVariance
open scoped BigOperators

/-- Key per-step bound: `1/(N+1) ≤ log(N+1) - log N` for `N ≥ 1`. -/
theorem log_step_le {N : ℕ} (hN : 1 ≤ N) :
    (1 : ℝ) / ((N : ℝ) + 1) ≤ Real.log ((N : ℝ) + 1) - Real.log (N : ℝ) := by
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hx : (0 : ℝ) < (N : ℝ) / ((N : ℝ) + 1) := by positivity
  have h := Real.log_le_sub_one_of_pos hx
  rw [Real.log_div (ne_of_gt hN0) (by positivity)] at h
  have heq : (N : ℝ) / ((N : ℝ) + 1) - 1 = -(1 / ((N : ℝ) + 1)) := by field_simp; ring
  rw [heq] at h
  linarith

/-- Harmonic-sum upper bound: `∑_{s<N} 1/(s+1) ≤ 1 + log N`. -/
theorem harmonic_le (N : ℕ) :
    ∑ s ∈ Finset.range N, (1 : ℝ) / ((s + 1 : ℕ) : ℝ) ≤ 1 + Real.log (N : ℝ) := by
  induction N with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_range_succ]
    rcases Nat.eq_zero_or_pos M with rfl | hM
    · simp [Real.log_one]
    · have hkey := log_step_le hM
      have hc : ((M + 1 : ℕ) : ℝ) = (M : ℝ) + 1 := by push_cast; ring
      rw [hc]
      linarith

/-- `eq.RD_count` reduction: if the number of remote-distance points with shortfall `s` is
`≲ s · D` (here `cnt s ≤ D·s`, the `∑_{r<s} n^{d-2} = s·n^{d-2}` count), then the weighted sum
`∑_{s=1}^{M} cnt(s)·s^{-2} ≤ D·(1 + log M)`. This is the clean combination of the geometric
per-`s` count with `harmonic_le` that gives the `n^{d-2} log n` bound of `eq.RD_count`; the
geometric count `cnt s ≤ D·s` (a `(d-1)`-dim shell count) is taken as the hypothesis `hcnt`. -/
theorem rd_count_template {M : ℕ} (D : ℝ) (hD : 0 ≤ D) (cnt : ℕ → ℝ)
    (hcnt : ∀ s ∈ Finset.range M, cnt (s + 1) ≤ D * ((s + 1 : ℕ) : ℝ)) :
    ∑ s ∈ Finset.range M, cnt (s + 1) / ((s + 1 : ℕ) : ℝ) ^ 2 ≤ D * (1 + Real.log (M : ℝ)) := by
  have hterm : ∀ s ∈ Finset.range M,
      cnt (s + 1) / ((s + 1 : ℕ) : ℝ) ^ 2 ≤ D * (1 / ((s + 1 : ℕ) : ℝ)) := by
    intro s hs
    have hspos : (0 : ℝ) < ((s + 1 : ℕ) : ℝ) := by positivity
    calc cnt (s + 1) / ((s + 1 : ℕ) : ℝ) ^ 2
        ≤ (D * ((s + 1 : ℕ) : ℝ)) / ((s + 1 : ℕ) : ℝ) ^ 2 := by gcongr; exact hcnt s hs
      _ = D * (1 / ((s + 1 : ℕ) : ℝ)) := by field_simp
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (harmonic_le M) hD

end NearCritical.AppendixVariance
