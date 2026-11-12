module

public import Mathlib.Algebra.Order.Ring.Pow
public import Mathlib.Tactic

/-! Appendix B (`sec.appendix_variance`) — reusable power-law lattice-sum core.

The four variance-term propositions `prop.var_term_1..4` all reduce to a power-law
sum with cutoff `∑_k (1+k)^a·max(r,k)^{−b} ≲ r^{a+1−b}`, whose crux is the sharp
p-series tail `∑_{m>r} m^{−s} ≤ r^{1−s}/(s−1)`. We prove the tail by DISCRETE
telescoping via Bernoulli (`one_add_mul_le_pow`), avoiding any measure-theoretic
machinery. This file builds the per-term step first. -/
@[expose] public section
namespace NearCritical.AppendixVariance
open scoped BigOperators

/-- Per-term telescoping bound: `1/m^{t+1} ≤ (1/t)(1/(m-1)^t − 1/m^t)` for
`m ≥ 2`, `t ≥ 1`. The engine for the sharp p-series tail. -/
theorem powerlaw_term_le {t : ℕ} (ht : 1 ≤ t) {m : ℕ} (hm : 2 ≤ m) :
    (1 : ℝ) / (m : ℝ) ^ (t + 1)
      ≤ (1 / (t : ℝ)) * (1 / ((m : ℝ) - 1) ^ t - 1 / (m : ℝ) ^ t) := by
  have hm2 : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  set x : ℝ := (m : ℝ) - 1 with hx
  have hx0 : 0 < x := by rw [hx]; linarith
  have hxne : x ≠ 0 := ne_of_gt hx0
  have hx1p : 0 < x + 1 := by linarith
  have hmx : (m : ℝ) = x + 1 := by rw [hx]; ring
  have ht0 : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
  have htne : (t : ℝ) ≠ 0 := ne_of_gt ht0
  have hxt : 0 < x ^ t := pow_pos hx0 t
  have hxtne : x ^ t ≠ 0 := ne_of_gt hxt
  have hx1t : 0 < (x + 1) ^ t := pow_pos hx1p t
  have hx1tne : (x + 1) ^ t ≠ 0 := ne_of_gt hx1t
  have hx1t1 : 0 < (x + 1) ^ (t + 1) := pow_pos hx1p (t + 1)
  have hx1t1ne : (x + 1) ^ (t + 1) ≠ 0 := ne_of_gt hx1t1
  -- Bernoulli at a = 1/x : 1 + t*(1/x) ≤ (1 + 1/x)^t
  have ha : (-2 : ℝ) ≤ 1 / x := by
    have : (0 : ℝ) ≤ 1 / x := by positivity
    linarith
  have hbern : 1 + (t : ℝ) * (1 / x) ≤ (1 + 1 / x) ^ t := by
    simpa using one_add_mul_le_pow ha t
  have hone : (1 : ℝ) + 1 / x = (x + 1) / x := by rw [add_div, div_self hxne]
  rw [hone, div_pow, le_div_iff₀ hxt] at hbern
  -- hbern : (1 + t*(1/x)) * x^t ≤ (x+1)^t
  have hexp : (1 + (t : ℝ) * (1 / x)) * x ^ t = x ^ t + (t : ℝ) * x ^ t / x := by ring
  rw [hexp] at hbern
  have hb : (t : ℝ) * x ^ t / x ≤ (x + 1) ^ t - x ^ t := by linarith
  -- key: t * x^t ≤ ((x+1)^t - x^t) * (x+1)
  have hkey : (t : ℝ) * x ^ t ≤ ((x + 1) ^ t - x ^ t) * (x + 1) := by
    have h1 : (t : ℝ) * x ^ t / x * (x + 1) ≤ ((x + 1) ^ t - x ^ t) * (x + 1) :=
      mul_le_mul_of_nonneg_right hb hx1p.le
    have h2 : (t : ℝ) * x ^ t ≤ (t : ℝ) * x ^ t / x * (x + 1) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hx0]
      nlinarith [mul_nonneg ht0.le hxt.le]
    linarith
  -- assemble
  rw [hmx, ← sub_nonneg]
  have heq : (1 / (t : ℝ)) * (1 / x ^ t - 1 / (x + 1) ^ t) - 1 / (x + 1) ^ (t + 1)
      = (((x + 1) ^ t - x ^ t) * (x + 1) - (t : ℝ) * x ^ t)
          / ((t : ℝ) * (x ^ t * (x + 1) ^ (t + 1))) := by
    field_simp <;> ring
  rw [heq]
  apply div_nonneg
  · linarith [hkey]
  · positivity

/-- Sharp p-series tail by discrete telescoping: for `t ≥ 1`, `r ≥ 1`, and any `K`,
`∑_{k<K} 1/(r+1+k)^{t+1} ≤ 1/(t·r^t)`. This is the `∑_{m>r} m^{-(t+1)} ≤ r^{-t}/t`
estimate underlying the Appendix-B variance sums. -/
theorem powerlaw_tail_le {t : ℕ} (ht : 1 ≤ t) {r : ℕ} (hr : 1 ≤ r) (K : ℕ) :
    ∑ k ∈ Finset.range K, (1 : ℝ) / ((r + 1 + k : ℕ) : ℝ) ^ (t + 1)
      ≤ 1 / ((t : ℝ) * (r : ℝ) ^ t) := by
  set g : ℕ → ℝ := fun j => 1 / ((t : ℝ) * (j : ℝ) ^ t) with hg
  have hterm : ∀ k, (1 : ℝ) / ((r + 1 + k : ℕ) : ℝ) ^ (t + 1) ≤ g (r + k) - g (r + k + 1) := by
    intro k
    have hm : 2 ≤ r + 1 + k := by omega
    have hpt := powerlaw_term_le ht hm
    have hRHS : (1 / (t : ℝ)) * (1 / (((r + 1 + k : ℕ) : ℝ) - 1) ^ t - 1 / ((r + 1 + k : ℕ) : ℝ) ^ t)
        = g (r + k) - g (r + k + 1) := by
      have h1 : ((r + 1 + k : ℕ) : ℝ) - 1 = ((r + k : ℕ) : ℝ) := by push_cast; ring
      have h2 : ((r + k + 1 : ℕ) : ℝ) = ((r + 1 + k : ℕ) : ℝ) := by push_cast; ring
      simp only [hg]
      rw [h1, h2]
      field_simp <;> ring
    exact hpt.trans_eq hRHS
  have htel : ∀ K, ∑ k ∈ Finset.range K, (g (r + k) - g (r + k + 1)) = g r - g (r + K) := by
    intro K
    induction K with
    | zero => simp
    | succ K ih =>
      rw [Finset.sum_range_succ, ih, show r + (K + 1) = r + K + 1 from by omega]
      ring
  calc ∑ k ∈ Finset.range K, (1 : ℝ) / ((r + 1 + k : ℕ) : ℝ) ^ (t + 1)
      ≤ ∑ k ∈ Finset.range K, (g (r + k) - g (r + k + 1)) :=
        Finset.sum_le_sum (fun k _ => hterm k)
    _ = g r - g (r + K) := htel K
    _ ≤ g r := by
        have hgnn : 0 ≤ g (r + K) := by simp only [hg]; positivity
        linarith
    _ = 1 / ((t : ℝ) * (r : ℝ) ^ t) := by simp only [hg]

/-- `c`-removal: a var_term summand `(k+1)^c / max(r,k+1)^{c+t+1}` is dominated by
the `c`-free form `1 / max(r,k+1)^{t+1}`, since `(k+1)^c ≤ max(r,k+1)^c`. This
reduces every weighted power-law sum to the degree-zero case handled by the
telescoping tail. -/
theorem powerlaw_c_removal (c t : ℕ) (r k : ℕ) :
    ((k + 1 : ℕ) : ℝ) ^ c / (max (r : ℝ) ((k + 1 : ℕ) : ℝ)) ^ (c + (t + 1))
      ≤ 1 / (max (r : ℝ) ((k + 1 : ℕ) : ℝ)) ^ (t + 1) := by
  set M : ℝ := max (r : ℝ) ((k + 1 : ℕ) : ℝ) with hM
  have hkM : ((k + 1 : ℕ) : ℝ) ≤ M := le_max_right _ _
  have hMpos : 0 < M := lt_of_lt_of_le (by positivity) hkM
  have hpow : ((k + 1 : ℕ) : ℝ) ^ c ≤ M ^ c := pow_le_pow_left₀ (by positivity) hkM c
  have hle1 : ((k + 1 : ℕ) : ℝ) ^ c / M ^ c ≤ 1 := (div_le_one (pow_pos hMpos c)).mpr hpow
  rw [pow_add, div_mul_eq_div_div, ← sub_nonneg, ← sub_div]
  exact div_nonneg (by linarith [hle1]) (pow_pos hMpos (t + 1)).le

/-- Combined power-law sum (c-free): `∑_{k<N} 1/max(r,k+1)^{t+1} ≤ (t+1)/(t·r^t)`,
assembling the `≤ r` head (`≤ 1/r^t`) and the `> r` tail (`≤ 1/(t·r^t)` via
`powerlaw_tail_le`). The direct workhorse for the Appendix-B variance sums. -/
theorem invmax_sum_le {t : ℕ} (ht : 1 ≤ t) {r : ℕ} (hr : 1 ≤ r) (N : ℕ) :
    ∑ k ∈ Finset.range N, (1 : ℝ) / (max (r : ℝ) ((k + 1 : ℕ) : ℝ)) ^ (t + 1)
      ≤ ((t : ℝ) + 1) / ((t : ℝ) * (r : ℝ) ^ t) := by
  have hrpos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have ht0 : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
  have hrt : (0 : ℝ) < (r : ℝ) ^ t := pow_pos hrpos t
  have hext : ∑ k ∈ Finset.range N, (1 : ℝ) / (max (r : ℝ) ((k + 1 : ℕ) : ℝ)) ^ (t + 1)
      ≤ ∑ k ∈ Finset.range (N + r), (1 : ℝ) / (max (r : ℝ) ((k + 1 : ℕ) : ℝ)) ^ (t + 1) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg
      (fun x hx => Finset.mem_range.mpr ((Finset.mem_range.mp hx).trans_le (Nat.le_add_right N r))) ?_
    intro k _ _; positivity
  refine hext.trans ?_
  rw [← Finset.sum_range_add_sum_Ico _ (show r ≤ N + r from by omega)]
  have hhead : ∑ k ∈ Finset.range r, (1 : ℝ) / (max (r : ℝ) ((k + 1 : ℕ) : ℝ)) ^ (t + 1)
      = 1 / (r : ℝ) ^ t := by
    have hcong : ∀ k ∈ Finset.range r, (1 : ℝ) / (max (r : ℝ) ((k + 1 : ℕ) : ℝ)) ^ (t + 1)
        = 1 / (r : ℝ) ^ (t + 1) := by
      intro k hk
      have hkr : ((k + 1 : ℕ) : ℝ) ≤ (r : ℝ) := by
        have := Finset.mem_range.mp hk
        exact_mod_cast (show k + 1 ≤ r from by omega)
      rw [max_eq_left hkr]
    rw [Finset.sum_congr rfl hcong, Finset.sum_const, Finset.card_range, nsmul_eq_mul, pow_succ]
    field_simp
  have htail : ∑ k ∈ Finset.Ico r (N + r), (1 : ℝ) / (max (r : ℝ) ((k + 1 : ℕ) : ℝ)) ^ (t + 1)
      ≤ 1 / ((t : ℝ) * (r : ℝ) ^ t) := by
    rw [Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel]
    have hcong : ∀ j ∈ Finset.range N,
        (1 : ℝ) / (max (r : ℝ) ((r + j + 1 : ℕ) : ℝ)) ^ (t + 1)
          = (1 : ℝ) / ((r + 1 + j : ℕ) : ℝ) ^ (t + 1) := by
      intro j _
      rw [show r + j + 1 = r + 1 + j from by omega]
      have hge : (r : ℝ) ≤ ((r + 1 + j : ℕ) : ℝ) := by
        exact_mod_cast (show r ≤ r + 1 + j from by omega)
      rw [max_eq_right hge]
    rw [Finset.sum_congr rfl hcong]
    exact powerlaw_tail_le ht hr N
  rw [hhead]
  refine (add_le_add le_rfl htail).trans (le_of_eq ?_)
  field_simp

/-- Full weighted power-law sum (combining `powerlaw_c_removal` and `invmax_sum_le`):
`∑_{k<N} (k+1)^c / max(r,k+1)^{c+t+1} ≤ (t+1)/(t·r^t)`. This is the exact form the
Appendix-B variance sums use — the `(k+1)^c` weight absorbs the shell count's
`(1+k)^{d-1}`. -/
theorem weighted_powerlaw_sum_le {c t : ℕ} (ht : 1 ≤ t) {r : ℕ} (hr : 1 ≤ r) (N : ℕ) :
    ∑ k ∈ Finset.range N, ((k + 1 : ℕ) : ℝ) ^ c / (max (r : ℝ) ((k + 1 : ℕ) : ℝ)) ^ (c + (t + 1))
      ≤ ((t : ℝ) + 1) / ((t : ℝ) * (r : ℝ) ^ t) :=
  le_trans (Finset.sum_le_sum (fun k _ => powerlaw_c_removal c t r k)) (invmax_sum_le ht hr N)

end NearCritical.AppendixVariance
