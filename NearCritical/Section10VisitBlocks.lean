module

public import Mathlib.Tactic

/-! Corrected Section10 EIT visit-block deduction. The source one-step return
argument is false; actual strong-Markov/Green inputs must prove the recurrence
below. -/
@[expose] public section
namespace NearCritical.Section10

/-- Restart after K visits, counting the current visit at index one. The
contraction yields the block-grid tail without an off-by-one loss. -/
theorem visit_tail_at_block_grid (f : ℕ → ℝ) {r : ℝ} (hr : 0 ≤ r)
    (K : ℕ) (hfirst : f 1 ≤ 1)
    (hstep : ∀ n, 1 ≤ n → f (n+K) ≤ r*f n) (l : ℕ) :
    f (l*K+1) ≤ r^l := by
  induction l with
  | zero => simpa using hfirst
  | succ l ih =>
    have hs := hstep (l*K+1) (by omega)
    have hi : (l+1)*K+1 = (l*K+1)+K := by ring
    rw [hi]
    calc
      _ ≤ r*f (l*K+1) := hs
      _ ≤ r*r^l := mul_le_mul_of_nonneg_left ih hr
      _ = _ := by rw [pow_succ]; ring

/-- Tail monotonicity fills the gaps between block restart indices. -/
theorem visit_tail_block_bound (f : ℕ → ℝ) (hmono : Antitone f)
    {r : ℝ} (hr : 0 ≤ r) {K : ℕ} (hK : 0 < K) (hfirst : f 1 ≤ 1)
    (hstep : ∀ n, 1 ≤ n → f (n+K) ≤ r*f n) {n : ℕ} (hn : 1 ≤ n) :
    f n ≤ r^((n-1)/K) := by
  have hgrid : ((n-1)/K)*K+1 ≤ n := by
    have h := Nat.div_mul_le_self (n-1) K
    omega
  exact (hmono hgrid).trans (visit_tail_at_block_grid f hr K hfirst hstep ((n-1)/K))

/-- Given q with block factor q^K, the repaired tail is bounded by q^(n-1)
with prefactor (q^K)^-1. Only the block recurrence is assumed; the geometric
all-count bound is a conclusion. A root of the half-contraction gives factor2. -/
theorem visit_tail_geometric_bound (f : ℕ → ℝ) (hmono : Antitone f)
    {q : ℝ} (hq : 0 < q) (hq1 : q ≤ 1) {K : ℕ} (hK : 0 < K)
    (hfirst : f 1 ≤ 1)
    (hstep : ∀ n, 1 ≤ n → f (n+K) ≤ q^K*f n) {n : ℕ} (hn : 1 ≤ n) :
    f n ≤ q^(n-1)/(q^K) := by
  let k := (n-1)/K
  have hr : 0 < q^K := pow_pos hq K
  have hb := visit_tail_block_bound f hmono hr.le hK hfirst hstep hn
  have hindex : n-1 ≤ (k+1)*K := by
    dsimp only [k]
    rw [Nat.mul_comm (_+1) K]
    exact (Nat.lt_mul_div_succ (n-1) hK).le
  apply (le_div_iff₀ hr).mpr
  calc
    _ ≤ (q^K)^k*(q^K) := mul_le_mul_of_nonneg_right hb hr.le
    _ = q^((k+1)*K) := by rw [← pow_succ,← pow_mul,Nat.mul_comm K (k+1)]
    _ ≤ q^(n-1) := pow_le_pow_of_le_one hq.le hq1 hindex

/-- Retain the initial-hit probability factor when converting the corrected
block recurrence to an exponential tail. The zero-hit case is handled without
dividing by zero. This is the factor needed for the source M^(2-d) rate. -/
theorem visit_tail_geometric_bound_with_first_hit (f : ℕ → ℝ) (hmono : Antitone f)
    {A q : ℝ} (hA : 0 ≤ A) (hq : 0 < q) (hq1 : q ≤ 1) {K : ℕ} (hK : 0 < K)
    (hfirst : f 1 ≤ A)
    (hstep : ∀ n, 1 ≤ n → f (n+K) ≤ q^K*f n) {n : ℕ} (hn : 1 ≤ n) :
    f n ≤ A*q^(n-1)/(q^K) := by
  by_cases hzero : A = 0
  · simpa only [hzero,zero_mul,zero_div] using (hmono hn).trans hfirst
  · have hpos : 0 < A := lt_of_le_of_ne hA (Ne.symm hzero)
    let g : ℕ → ℝ := fun m => f m/A
    have hgm : Antitone g := fun m n hmn =>
      div_le_div_of_nonneg_right (hmono hmn) hA
    have hgf : g 1 ≤ 1 := (div_le_one hpos).mpr hfirst
    have hgs (m : ℕ) (hm : 1 ≤ m) : g (m+K) ≤ q^K*g m := by
      have hh := div_le_div_of_nonneg_right (hstep m hm) hA
      simpa only [g,mul_div_assoc] using hh
    have hb := visit_tail_geometric_bound g hgm hq hq1 hK hgf hgs hn
    have hc : f n ≤ (q^(n-1)/(q^K))*A := (div_le_iff₀ hpos).mp hb
    calc
      _ ≤ (q^(n-1)/(q^K))*A := hc
      _ = _ := by ring

end NearCritical.Section10
