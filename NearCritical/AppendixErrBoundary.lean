module

public import NearCritical.AppendixShellCount

/-! Analytic cores of `lem.err_boundary` and `lem.err_cluster` (source main.tex 6645 / 6657),
the boundary/cluster error sums feeding `lem.box_twopoint_lower`. These are the DETERMINISTIC
lattice-sum cores: the probabilistic content (the expectation, `P[x↔w,x↔w'] = P[w,w'∈𝔠]`, the BK
tree decomposition, and the box two-point pointwise bounds) is taken as hypotheses; what remains is
pure summation over the lattice, which is this file's content. d > 6 throughout.

This file begins with the final radial tails — both reduce to the verified 1-D engine
`weighted_powerlaw_sum_le` — which are the `≲ r^{6-d}` steps that close each lemma after the
geometric 3-region split, followed by the single-center cubic shell sum that discharges the
`u nearest w` / `u nearest x` branch-point regions of both lemmas. Imports `AppendixShellCount`
read-only (which re-exports `AppendixVarianceSum`); edits nothing. -/
@[expose] public section
namespace NearCritical.AppendixVariance
open scoped BigOperators

/-- Final radial tail of `lem.err_boundary`: after the 3-region branch-point split reduces the
per-pair two-point bound to `h^{-d} k^{3-d}` and the face counting contributes the `k`-weight
(`|F|∼h^{d-1}`, `∼k^{d-2}` points at distance `k`), the remaining sum is
`∑_{k<N} (k+1)·max(r,k+1)^{4-d}`, which for `d>6` is `≲ r^{6-d}`. This is `weighted_powerlaw_sum_le`
at `c=1, t=d-6` (so the kernel exponent is `c+(t+1)=d-4` and the bound is `(d-5)/((d-6)r^{d-6})`). -/
theorem err_boundary_radial_tail {d : ℕ} (hd : 7 ≤ d) {r : ℕ} (hr : 1 ≤ r) (N : ℕ) :
    ∑ k ∈ Finset.range N, ((k + 1 : ℕ) : ℝ) / (max (r : ℝ) ((k + 1 : ℕ) : ℝ)) ^ (d - 4)
      ≤ (((d - 6 : ℕ) : ℝ) + 1) / (((d - 6 : ℕ) : ℝ) * (r : ℝ) ^ (d - 6)) := by
  have h := weighted_powerlaw_sum_le (c := 1) (t := d - 6) (by omega) hr N
  simpa [pow_one, show 1 + ((d - 6) + 1) = d - 4 from by omega] using h

/-- Final radial tail of `lem.err_cluster`: after the convolution `∑_v |u-v|^{1-d}max(r,|w-v|)^{2-d}
≲ max(r,|u-w|)^{3-d}` and the 3-region split, the remaining sum is `∑_{m<N} (m+1)²·max(r,m+1)^{3-d}`,
which for `d>6` is `≲ r^{6-d}`. This is `weighted_powerlaw_sum_le` at `c=2, t=d-6` (kernel exponent
`c+(t+1)=d-3`). -/
theorem err_cluster_radial_tail {d : ℕ} (hd : 7 ≤ d) {r : ℕ} (hr : 1 ≤ r) (N : ℕ) :
    ∑ k ∈ Finset.range N, ((k + 1 : ℕ) : ℝ) ^ 2 / (max (r : ℝ) ((k + 1 : ℕ) : ℝ)) ^ (d - 3)
      ≤ (((d - 6 : ℕ) : ℝ) + 1) / (((d - 6 : ℕ) : ℝ) * (r : ℝ) ^ (d - 6)) := by
  have h := weighted_powerlaw_sum_le (c := 2) (t := d - 6) (by omega) hr N
  simpa [show 2 + ((d - 6) + 1) = d - 3 from by omega] using h

/-- Single-center cubic shell sum: the branch-point weight `(1+|u-w|)³·|u-w|^{-d}` of both
`lem.err_boundary` and `lem.err_cluster`, regularized as `(|u-w|_∞+1)^{3-d} = 1/(|u-w|_∞+1)^{d-3}`,
sums over the `ℓ^∞` ball of radius `k` to `≲ (k+1)³`. This is the `u nearest w` (and, centered at `x`,
`u nearest x`) region step of both proofs: `∑_{|u-w|≲k}(1+|u-w|)³|u-w|^{-d} ≲ ∑_{m=1}^k m^{d-1+3-d}
= ∑ m² ∼ k³` (main.tex ~6755, ~6765). Mechanism: the shell count `(j+1)^{d-1}` from
`radial_sum_shell_bound` cancels the `(j+1)^{-(d-3)}` down to `(j+1)²`, whose `range (k+1)` sum is
`≤ (k+1)·(k+1)² = (k+1)³`. Constant `2d·3^{d-1}` is the shell-count constant. -/
theorem branch_shell_cubic_sum {d : ℕ} (hd : 3 ≤ d) (w : Fin d → ℤ) (k : ℕ) :
    ∑ u ∈ linfBall w (k : ℤ), (1 : ℝ) / ((linfDist w u + 1 : ℕ) : ℝ) ^ (d - 3)
      ≤ 2 * (d : ℝ) * 3 ^ (d - 1) * ((k : ℝ) + 1) ^ 3 := by
  refine le_trans (radial_sum_shell_bound (by omega) w k
    (fun j => (1 : ℝ) / ((j + 1 : ℕ) : ℝ) ^ (d - 3)) (fun j => by positivity)) ?_
  have hkey : ∀ j ∈ Finset.range (k + 1),
      2 * (d : ℝ) * 3 ^ (d - 1) * ((j + 1 : ℕ) : ℝ) ^ (d - 1)
          * ((1 : ℝ) / ((j + 1 : ℕ) : ℝ) ^ (d - 3))
        = 2 * (d : ℝ) * 3 ^ (d - 1) * ((j + 1 : ℕ) : ℝ) ^ 2 := by
    intro j _
    have hjpos : (0 : ℝ) < ((j + 1 : ℕ) : ℝ) := by positivity
    have hsplit : ((j + 1 : ℕ) : ℝ) ^ (d - 1)
        = ((j + 1 : ℕ) : ℝ) ^ (d - 3) * ((j + 1 : ℕ) : ℝ) ^ 2 := by
      rw [← pow_add]; congr 1; omega
    rw [hsplit]; field_simp
  calc ∑ j ∈ Finset.range (k + 1),
          2 * (d : ℝ) * 3 ^ (d - 1) * ((j + 1 : ℕ) : ℝ) ^ (d - 1)
            * ((1 : ℝ) / ((j + 1 : ℕ) : ℝ) ^ (d - 3))
      = ∑ j ∈ Finset.range (k + 1), 2 * (d : ℝ) * 3 ^ (d - 1) * ((j + 1 : ℕ) : ℝ) ^ 2 :=
        Finset.sum_congr rfl hkey
    _ = 2 * (d : ℝ) * 3 ^ (d - 1) * ∑ j ∈ Finset.range (k + 1), ((j + 1 : ℕ) : ℝ) ^ 2 := by
        rw [Finset.mul_sum]
    _ ≤ 2 * (d : ℝ) * 3 ^ (d - 1) * ((k : ℝ) + 1) ^ 3 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        calc ∑ j ∈ Finset.range (k + 1), ((j + 1 : ℕ) : ℝ) ^ 2
            ≤ ∑ _j ∈ Finset.range (k + 1), ((k : ℝ) + 1) ^ 2 := by
              apply Finset.sum_le_sum
              intro j hj
              have hjk : ((j + 1 : ℕ) : ℝ) ≤ (k : ℝ) + 1 := by
                have hh : j + 1 ≤ k + 1 := by have := Finset.mem_range.mp hj; omega
                exact_mod_cast hh
              exact pow_le_pow_left₀ (by positivity) hjk 2
          _ = ((k : ℝ) + 1) ^ 3 := by
              rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring

/-- General single-center shell sum: for `q ≤ d-1`, the regularized kernel `(|u-w|_∞+1)^{-q}`
sums over the `ℓ^∞` ball of radius `M` to `≤ 2d·3^{d-1}(M+1)^{d-q}`. The shell count `(j+1)^{d-1}`
from `radial_sum_shell_bound` leaves `(j+1)^{(d-1)-q}`, whose `range (M+1)` sum is `≤ (M+1)^{d-q}`.
Specializes to the branch-point regions: `q=d-3 → (M+1)³` (cf. `branch_shell_cubic_sum`),
`q=d-2 → (M+1)²`, `q=d-1 → (M+1)` — the three shell weights the convolution assembly needs. -/
theorem shell_pow_sum {d q : ℕ} (hd : 1 ≤ d) (hq : q ≤ d - 1) (w : Fin d → ℤ) (M : ℕ) :
    ∑ u ∈ linfBall w (M : ℤ), (1 : ℝ) / ((linfDist w u + 1 : ℕ) : ℝ) ^ q
      ≤ 2 * (d : ℝ) * 3 ^ (d - 1) * ((M : ℝ) + 1) ^ (d - q) := by
  refine le_trans (radial_sum_shell_bound hd w M
    (fun j => (1 : ℝ) / ((j + 1 : ℕ) : ℝ) ^ q) (fun j => by positivity)) ?_
  have hkey : ∀ j ∈ Finset.range (M + 1),
      2 * (d : ℝ) * 3 ^ (d - 1) * ((j + 1 : ℕ) : ℝ) ^ (d - 1)
          * ((1 : ℝ) / ((j + 1 : ℕ) : ℝ) ^ q)
        = 2 * (d : ℝ) * 3 ^ (d - 1) * ((j + 1 : ℕ) : ℝ) ^ ((d - 1) - q) := by
    intro j _
    have hjpos : (0 : ℝ) < ((j + 1 : ℕ) : ℝ) := by positivity
    have hsplit : ((j + 1 : ℕ) : ℝ) ^ (d - 1)
        = ((j + 1 : ℕ) : ℝ) ^ q * ((j + 1 : ℕ) : ℝ) ^ ((d - 1) - q) := by
      rw [← pow_add]; congr 1; omega
    rw [hsplit]; field_simp
  calc ∑ j ∈ Finset.range (M + 1),
          2 * (d : ℝ) * 3 ^ (d - 1) * ((j + 1 : ℕ) : ℝ) ^ (d - 1)
            * ((1 : ℝ) / ((j + 1 : ℕ) : ℝ) ^ q)
      = ∑ j ∈ Finset.range (M + 1),
          2 * (d : ℝ) * 3 ^ (d - 1) * ((j + 1 : ℕ) : ℝ) ^ ((d - 1) - q) :=
        Finset.sum_congr rfl hkey
    _ = 2 * (d : ℝ) * 3 ^ (d - 1)
          * ∑ j ∈ Finset.range (M + 1), ((j + 1 : ℕ) : ℝ) ^ ((d - 1) - q) := by
        rw [Finset.mul_sum]
    _ ≤ 2 * (d : ℝ) * 3 ^ (d - 1) * ((M : ℝ) + 1) ^ (d - q) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        calc ∑ j ∈ Finset.range (M + 1), ((j + 1 : ℕ) : ℝ) ^ ((d - 1) - q)
            ≤ ∑ _j ∈ Finset.range (M + 1), ((M : ℝ) + 1) ^ ((d - 1) - q) := by
              apply Finset.sum_le_sum
              intro j hj
              have hjk : ((j + 1 : ℕ) : ℝ) ≤ (M : ℝ) + 1 := by
                have hh : j + 1 ≤ M + 1 := by have := Finset.mem_range.mp hj; omega
                exact_mod_cast hh
              exact pow_le_pow_left₀ (by positivity) hjk _
          _ = ((M : ℝ) + 1) ^ (d - q) := by
              rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
                  show d - q = ((d - 1) - q) + 1 from by omega, pow_succ]
              push_cast; ring

theorem conv_R2 {d : ℕ} (hd : 3 ≤ d) (u w : Fin d → ℤ) {r : ℕ} (hr : 1 ≤ r)
    (c : Fin d → ℤ) (K : ℕ) :
    ∑ v ∈ (linfBall c (K : ℤ)).filter
        (fun v => ¬(2 * linfDist w v ≤ linfDist u w) ∧ 2 * linfDist u v ≤ linfDist u w),
        (1 : ℝ) / ((linfDist u v + 1 : ℕ) : ℝ) ^ (d - 1)
          * (1 / (max (r : ℝ) ((linfDist w v + 1 : ℕ) : ℝ)) ^ (d - 2))
      ≤ 2 ^ (d - 2) * (2 * (d : ℝ) * 3 ^ (d - 1))
          / (max (r : ℝ) ((linfDist u w + 1 : ℕ) : ℝ)) ^ (d - 3) := by
  set D := linfDist u w with hD
  set Dmax := max (r : ℝ) ((D + 1 : ℕ) : ℝ) with hDmax
  have hDmax_pos : (0 : ℝ) < Dmax := by
    rw [hDmax]
    exact lt_of_lt_of_le (by exact_mod_cast Nat.succ_pos D) (le_max_right _ _)
  -- Step 1: termwise pull-out of the w-kernel.
  have hterm : ∀ v ∈ (linfBall c (K : ℤ)).filter
      (fun v => ¬(2 * linfDist w v ≤ D) ∧ 2 * linfDist u v ≤ D),
      (1 : ℝ) / ((linfDist u v + 1 : ℕ) : ℝ) ^ (d - 1)
          * (1 / (max (r : ℝ) ((linfDist w v + 1 : ℕ) : ℝ)) ^ (d - 2))
        ≤ (2 ^ (d - 2) / Dmax ^ (d - 2))
            * (1 / ((linfDist u v + 1 : ℕ) : ℝ) ^ (d - 1)) := by
    intro v hv
    rw [Finset.mem_filter] at hv
    have hfar : ¬(2 * linfDist w v ≤ D) := hv.2.1
    have hBpos : (0 : ℝ) < max (r : ℝ) ((linfDist w v + 1 : ℕ) : ℝ) :=
      lt_of_lt_of_le (by exact_mod_cast Nat.succ_pos (linfDist w v)) (le_max_right _ _)
    -- Dmax ≤ 2 * max(r, |w-v|+1)
    have hcmp : Dmax ≤ 2 * max (r : ℝ) ((linfDist w v + 1 : ℕ) : ℝ) := by
      rw [hDmax]
      apply max_le
      · have h1 : (r : ℝ) ≤ max (r : ℝ) ((linfDist w v + 1 : ℕ) : ℝ) := le_max_left _ _
        nlinarith [le_max_left (r : ℝ) ((linfDist w v + 1 : ℕ) : ℝ), hBpos.le]
      · have hnat : D + 1 ≤ 2 * (linfDist w v + 1) := by omega
        have h2 : ((D + 1 : ℕ) : ℝ) ≤ 2 * ((linfDist w v + 1 : ℕ) : ℝ) := by
          exact_mod_cast hnat
        have h3 : ((linfDist w v + 1 : ℕ) : ℝ) ≤ max (r : ℝ) ((linfDist w v + 1 : ℕ) : ℝ) :=
          le_max_right _ _
        nlinarith [h2, h3]
    -- raise to d-2 and invert
    have hpow : Dmax ^ (d - 2) ≤ 2 ^ (d - 2) * max (r : ℝ) ((linfDist w v + 1 : ℕ) : ℝ) ^ (d - 2) := by
      calc Dmax ^ (d - 2) ≤ (2 * max (r : ℝ) ((linfDist w v + 1 : ℕ) : ℝ)) ^ (d - 2) :=
            pow_le_pow_left₀ hDmax_pos.le hcmp _
        _ = 2 ^ (d - 2) * max (r : ℝ) ((linfDist w v + 1 : ℕ) : ℝ) ^ (d - 2) := by rw [mul_pow]
    have hP : (1 : ℝ) / (max (r : ℝ) ((linfDist w v + 1 : ℕ) : ℝ)) ^ (d - 2)
        ≤ 2 ^ (d - 2) / Dmax ^ (d - 2) := by
      rw [div_le_div_iff₀ (pow_pos hBpos _) (pow_pos hDmax_pos _)]
      calc (1 : ℝ) * Dmax ^ (d - 2) = Dmax ^ (d - 2) := by ring
        _ ≤ 2 ^ (d - 2) * max (r : ℝ) ((linfDist w v + 1 : ℕ) : ℝ) ^ (d - 2) := hpow
    have hA : (0 : ℝ) ≤ (1 : ℝ) / ((linfDist u v + 1 : ℕ) : ℝ) ^ (d - 1) := by positivity
    calc (1 : ℝ) / ((linfDist u v + 1 : ℕ) : ℝ) ^ (d - 1)
            * (1 / (max (r : ℝ) ((linfDist w v + 1 : ℕ) : ℝ)) ^ (d - 2))
          = (1 / (max (r : ℝ) ((linfDist w v + 1 : ℕ) : ℝ)) ^ (d - 2))
            * (1 / ((linfDist u v + 1 : ℕ) : ℝ) ^ (d - 1)) := by ring
      _ ≤ (2 ^ (d - 2) / Dmax ^ (d - 2))
            * (1 / ((linfDist u v + 1 : ℕ) : ℝ) ^ (d - 1)) :=
          mul_le_mul_of_nonneg_right hP hA
  -- Step 2: sum the pulled-out bound, factor, subset-monotone, shell_pow_sum.
  calc ∑ v ∈ (linfBall c (K : ℤ)).filter
          (fun v => ¬(2 * linfDist w v ≤ D) ∧ 2 * linfDist u v ≤ D),
          (1 : ℝ) / ((linfDist u v + 1 : ℕ) : ℝ) ^ (d - 1)
            * (1 / (max (r : ℝ) ((linfDist w v + 1 : ℕ) : ℝ)) ^ (d - 2))
        ≤ ∑ v ∈ (linfBall c (K : ℤ)).filter
            (fun v => ¬(2 * linfDist w v ≤ D) ∧ 2 * linfDist u v ≤ D),
            (2 ^ (d - 2) / Dmax ^ (d - 2))
              * (1 / ((linfDist u v + 1 : ℕ) : ℝ) ^ (d - 1)) :=
        Finset.sum_le_sum hterm
    _ = (2 ^ (d - 2) / Dmax ^ (d - 2))
          * ∑ v ∈ (linfBall c (K : ℤ)).filter
              (fun v => ¬(2 * linfDist w v ≤ D) ∧ 2 * linfDist u v ≤ D),
              (1 / ((linfDist u v + 1 : ℕ) : ℝ) ^ (d - 1)) := by
        rw [Finset.mul_sum]
    _ ≤ (2 ^ (d - 2) / Dmax ^ (d - 2))
          * ∑ v ∈ linfBall u (D : ℤ), (1 / ((linfDist u v + 1 : ℕ) : ℝ) ^ (d - 1)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro v hv
          rw [Finset.mem_filter] at hv
          have h2uv : 2 * linfDist u v ≤ D := hv.2.2
          rw [mem_linfBall_iff_dist u v (by exact_mod_cast Nat.zero_le D)]
          simp only [Int.toNat_natCast]
          omega
        · intro v _ _; positivity
    _ ≤ (2 ^ (d - 2) / Dmax ^ (d - 2)) * (2 * (d : ℝ) * 3 ^ (d - 1) * ((D : ℝ) + 1)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have := shell_pow_sum (d := d) (q := d - 1) (by omega) (by omega) u D
        -- RHS exponent d-(d-1)=1
        simpa [show d - (d - 1) = 1 from by omega, pow_one] using this
    _ ≤ 2 ^ (d - 2) * (2 * (d : ℝ) * 3 ^ (d - 1)) / Dmax ^ (d - 3) := by
        have hEle : (D : ℝ) + 1 ≤ Dmax := by
          rw [hDmax]
          have : ((D + 1 : ℕ) : ℝ) ≤ max (r : ℝ) ((D + 1 : ℕ) : ℝ) := le_max_right _ _
          push_cast at this ⊢; linarith
        have hpos2 : (0 : ℝ) < Dmax ^ (d - 2) := pow_pos hDmax_pos _
        have hpos3 : (0 : ℝ) < Dmax ^ (d - 3) := pow_pos hDmax_pos _
        have hpe : Dmax ^ (d - 2) = Dmax ^ (d - 3) * Dmax := by
          rw [← pow_succ]; congr 1; omega
        rw [div_mul_eq_mul_div, div_le_div_iff₀ hpos2 hpos3, hpe]
        have hF : (0 : ℝ) ≤ 2 ^ (d - 2) * (2 * (d : ℝ) * 3 ^ (d - 1)) * Dmax ^ (d - 3) := by
          positivity
        nlinarith [mul_le_mul_of_nonneg_left hEle hF]

theorem conv_R1 {d : ℕ} (hd : 3 ≤ d) (u w : Fin d → ℤ) {r : ℕ} (hr : 1 ≤ r)
    (c : Fin d → ℤ) (K : ℕ) :
    ∑ v ∈ (linfBall c (K : ℤ)).filter (fun v => 2 * linfDist w v ≤ linfDist u w),
        (1 : ℝ) / ((linfDist u v + 1 : ℕ) : ℝ) ^ (d - 1)
          * (1 / (max (r : ℝ) ((linfDist w v + 1 : ℕ) : ℝ)) ^ (d - 2))
      ≤ 2 ^ (2 * d) * (2 * (d : ℝ) * 3 ^ (d - 1))
          / (max (r : ℝ) ((linfDist u w + 1 : ℕ) : ℝ)) ^ (d - 3) := by
  set D := linfDist u w with hD
  set Dmax := max (r : ℝ) ((D + 1 : ℕ) : ℝ) with hDmax
  have hDmax_pos : (0 : ℝ) < Dmax := by
    rw [hDmax]; exact lt_of_lt_of_le (by exact_mod_cast Nat.succ_pos D) (le_max_right _ _)
  have hD1pos : (0 : ℝ) < ((D + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos D
  -- Common pull-out of the |u-v| kernel: on R1, 2|u-v| ≥ D.
  have hpull : ∀ v ∈ (linfBall c (K : ℤ)).filter (fun v => 2 * linfDist w v ≤ D),
      (1 : ℝ) / ((linfDist u v + 1 : ℕ) : ℝ) ^ (d - 1)
          * (1 / (max (r : ℝ) ((linfDist w v + 1 : ℕ) : ℝ)) ^ (d - 2))
        ≤ (2 ^ (d - 1) / ((D + 1 : ℕ) : ℝ) ^ (d - 1))
            * (1 / (max (r : ℝ) ((linfDist w v + 1 : ℕ) : ℝ)) ^ (d - 2)) := by
    intro v hv
    rw [Finset.mem_filter] at hv
    have hfilt : 2 * linfDist w v ≤ D := hv.2
    have htri : D ≤ linfDist u v + linfDist w v := by
      have h := linfDist_triangle u v w; rw [linfDist_comm v w] at h; exact h
    have hnat : D + 1 ≤ 2 * (linfDist u v + 1) := by omega
    have hcast : ((D + 1 : ℕ) : ℝ) ≤ 2 * ((linfDist u v + 1 : ℕ) : ℝ) := by exact_mod_cast hnat
    have hApos : (0 : ℝ) < ((linfDist u v + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos _
    have hpow : ((D + 1 : ℕ) : ℝ) ^ (d - 1) ≤ 2 ^ (d - 1) * ((linfDist u v + 1 : ℕ) : ℝ) ^ (d - 1) := by
      calc ((D + 1 : ℕ) : ℝ) ^ (d - 1) ≤ (2 * ((linfDist u v + 1 : ℕ) : ℝ)) ^ (d - 1) :=
            pow_le_pow_left₀ hD1pos.le hcast _
        _ = 2 ^ (d - 1) * ((linfDist u v + 1 : ℕ) : ℝ) ^ (d - 1) := by rw [mul_pow]
    have hAle : (1 : ℝ) / ((linfDist u v + 1 : ℕ) : ℝ) ^ (d - 1)
        ≤ 2 ^ (d - 1) / ((D + 1 : ℕ) : ℝ) ^ (d - 1) := by
      rw [div_le_div_iff₀ (pow_pos hApos _) (pow_pos hD1pos _)]
      calc (1 : ℝ) * ((D + 1 : ℕ) : ℝ) ^ (d - 1) = ((D + 1 : ℕ) : ℝ) ^ (d - 1) := by ring
        _ ≤ 2 ^ (d - 1) * ((linfDist u v + 1 : ℕ) : ℝ) ^ (d - 1) := hpow
    exact mul_le_mul_of_nonneg_right hAle (by positivity)
  refine le_trans (Finset.sum_le_sum hpull) ?_
  rw [← Finset.mul_sum]
  by_cases hrD : r ≤ D
  · -- Case r ≤ D: drop floor, shell_pow_sum(q=d-2), Dmax = D+1.
    have hDval : Dmax = ((D + 1 : ℕ) : ℝ) := by
      rw [hDmax]; apply max_eq_right
      have : (r : ℝ) ≤ (D : ℝ) := by exact_mod_cast hrD
      push_cast; linarith
    have hW : ∑ v ∈ (linfBall c (K : ℤ)).filter (fun v => 2 * linfDist w v ≤ D),
        (1 : ℝ) / (max (r : ℝ) ((linfDist w v + 1 : ℕ) : ℝ)) ^ (d - 2)
          ≤ 2 * (d : ℝ) * 3 ^ (d - 1) * ((D : ℝ) + 1) ^ 2 := by
      have step1 : ∑ v ∈ (linfBall c (K : ℤ)).filter (fun v => 2 * linfDist w v ≤ D),
          (1 : ℝ) / (max (r : ℝ) ((linfDist w v + 1 : ℕ) : ℝ)) ^ (d - 2)
            ≤ ∑ v ∈ (linfBall c (K : ℤ)).filter (fun v => 2 * linfDist w v ≤ D),
              (1 : ℝ) / ((linfDist w v + 1 : ℕ) : ℝ) ^ (d - 2) := by
        apply Finset.sum_le_sum
        intro v _
        exact one_div_le_one_div_of_le (by positivity)
          (pow_le_pow_left₀ (by positivity) (le_max_right _ _) _)
      have step2 : ∑ v ∈ (linfBall c (K : ℤ)).filter (fun v => 2 * linfDist w v ≤ D),
          (1 : ℝ) / ((linfDist w v + 1 : ℕ) : ℝ) ^ (d - 2)
            ≤ ∑ v ∈ linfBall w (D : ℤ), (1 : ℝ) / ((linfDist w v + 1 : ℕ) : ℝ) ^ (d - 2) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro v hv
          rw [Finset.mem_filter] at hv
          rw [mem_linfBall_iff_dist w v (by positivity)]
          simp only [Int.toNat_natCast]; omega
        · intro v _ _; positivity
      have step3 := shell_pow_sum (d := d) (q := d - 2) (by omega) (by omega) w D
      refine step1.trans (step2.trans ?_)
      simpa [show d - (d - 2) = 2 from by omega] using step3
    calc (2 ^ (d - 1) / ((D + 1 : ℕ) : ℝ) ^ (d - 1))
          * ∑ v ∈ (linfBall c (K : ℤ)).filter (fun v => 2 * linfDist w v ≤ D),
              (1 : ℝ) / (max (r : ℝ) ((linfDist w v + 1 : ℕ) : ℝ)) ^ (d - 2)
        ≤ (2 ^ (d - 1) / ((D + 1 : ℕ) : ℝ) ^ (d - 1)) * (2 * (d : ℝ) * 3 ^ (d - 1) * ((D : ℝ) + 1) ^ 2) :=
          mul_le_mul_of_nonneg_left hW (by positivity)
      _ ≤ 2 ^ (2 * d) * (2 * (d : ℝ) * 3 ^ (d - 1)) / Dmax ^ (d - 3) := by
          rw [hDval]
          have hDR : ((D + 1 : ℕ) : ℝ) = (D : ℝ) + 1 := by push_cast; ring
          rw [hDR]
          have hpd1 : (0 : ℝ) < ((D : ℝ) + 1) ^ (d - 1) := by positivity
          have hpd3 : (0 : ℝ) < ((D : ℝ) + 1) ^ (d - 3) := by positivity
          have hsplit : ((D : ℝ) + 1) ^ (d - 1) = ((D : ℝ) + 1) ^ (d - 3) * ((D : ℝ) + 1) ^ 2 := by
            rw [← pow_add]; congr 1; omega
          rw [div_mul_eq_mul_div, div_le_div_iff₀ hpd1 hpd3, hsplit]
          have h2le : (2 : ℝ) ^ (d - 1) ≤ 2 ^ (2 * d) := by
            apply pow_le_pow_right₀ (by norm_num); omega
          have hfac : (0 : ℝ) ≤ (2 * (d : ℝ) * 3 ^ (d - 1)) * (((D : ℝ) + 1) ^ (d - 3) * ((D : ℝ) + 1) ^ 2) := by positivity
          nlinarith [mul_le_mul_of_nonneg_right h2le hfac]
  · -- Case r > D: 1/max^(d-2) ≤ 1/r^(d-2), card(R1) ≤ (2D+1)^d, Dmax = r.
    have hDval : Dmax = (r : ℝ) := by
      rw [hDmax]; apply max_eq_left
      have : (D : ℝ) + 1 ≤ (r : ℝ) := by
        have : D + 1 ≤ r := by omega
        exact_mod_cast this
      push_cast; linarith
    have hrpos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
    have hW : ∑ v ∈ (linfBall c (K : ℤ)).filter (fun v => 2 * linfDist w v ≤ D),
        (1 : ℝ) / (max (r : ℝ) ((linfDist w v + 1 : ℕ) : ℝ)) ^ (d - 2)
          ≤ 2 ^ d * ((D : ℝ) + 1) ^ d * (1 / (r : ℝ) ^ (d - 2)) := by
      have step1 : ∑ v ∈ (linfBall c (K : ℤ)).filter (fun v => 2 * linfDist w v ≤ D),
          (1 : ℝ) / (max (r : ℝ) ((linfDist w v + 1 : ℕ) : ℝ)) ^ (d - 2)
            ≤ ∑ v ∈ (linfBall c (K : ℤ)).filter (fun v => 2 * linfDist w v ≤ D),
              (1 : ℝ) / (r : ℝ) ^ (d - 2) := by
        apply Finset.sum_le_sum
        intro v _
        exact one_div_le_one_div_of_le (by positivity)
          (pow_le_pow_left₀ (by positivity) (le_max_left _ _) _)
      have hcard : ((linfBall c (K : ℤ)).filter (fun v => 2 * linfDist w v ≤ D)).card
          ≤ (linfBall w (D : ℤ)).card := by
        apply Finset.card_le_card
        intro v hv
        rw [Finset.mem_filter] at hv
        rw [mem_linfBall_iff_dist w v (by positivity)]
        simp only [Int.toNat_natCast]; omega
      have hcard2 : ((linfBall w (D : ℤ)).card : ℝ) ≤ 2 ^ d * ((D : ℝ) + 1) ^ d := by
        rw [linfBall_card]
        have hnat : (2 * (D : ℤ) + 1).toNat ≤ 2 * (D + 1) := by omega
        calc (((2 * (D : ℤ) + 1).toNat ^ d : ℕ) : ℝ)
            = (((2 * (D : ℤ) + 1).toNat : ℕ) : ℝ) ^ d := by push_cast; ring
          _ ≤ ((2 * (D + 1) : ℕ) : ℝ) ^ d := by
              apply pow_le_pow_left₀ (by positivity); exact_mod_cast hnat
          _ = 2 ^ d * ((D : ℝ) + 1) ^ d := by push_cast; rw [mul_pow]
      calc ∑ v ∈ (linfBall c (K : ℤ)).filter (fun v => 2 * linfDist w v ≤ D),
            (1 : ℝ) / (max (r : ℝ) ((linfDist w v + 1 : ℕ) : ℝ)) ^ (d - 2)
          ≤ ∑ v ∈ (linfBall c (K : ℤ)).filter (fun v => 2 * linfDist w v ≤ D),
              (1 : ℝ) / (r : ℝ) ^ (d - 2) := step1
        _ = (((linfBall c (K : ℤ)).filter (fun v => 2 * linfDist w v ≤ D)).card : ℝ)
              * (1 / (r : ℝ) ^ (d - 2)) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (2 ^ d * ((D : ℝ) + 1) ^ d) * (1 / (r : ℝ) ^ (d - 2)) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            exact le_trans (by exact_mod_cast hcard) hcard2
        _ = 2 ^ d * ((D : ℝ) + 1) ^ d * (1 / (r : ℝ) ^ (d - 2)) := by ring
    calc (2 ^ (d - 1) / ((D + 1 : ℕ) : ℝ) ^ (d - 1))
          * ∑ v ∈ (linfBall c (K : ℤ)).filter (fun v => 2 * linfDist w v ≤ D),
              (1 : ℝ) / (max (r : ℝ) ((linfDist w v + 1 : ℕ) : ℝ)) ^ (d - 2)
        ≤ (2 ^ (d - 1) / ((D + 1 : ℕ) : ℝ) ^ (d - 1)) * (2 ^ d * ((D : ℝ) + 1) ^ d * (1 / (r : ℝ) ^ (d - 2))) :=
          mul_le_mul_of_nonneg_left hW (by positivity)
      _ ≤ 2 ^ (2 * d) * (2 * (d : ℝ) * 3 ^ (d - 1)) / Dmax ^ (d - 3) := by
          rw [hDval]
          have hDR : ((D + 1 : ℕ) : ℝ) = (D : ℝ) + 1 := by push_cast; ring
          rw [hDR]
          have hDle : (D : ℝ) + 1 ≤ (r : ℝ) := by
            have : D + 1 ≤ r := by omega
            exact_mod_cast this
          have hpd1 : (0 : ℝ) < ((D : ℝ) + 1) ^ (d - 1) := by positivity
          have hrp2 : (0 : ℝ) < (r : ℝ) ^ (d - 2) := by positivity
          have hrp3 : (0 : ℝ) < (r : ℝ) ^ (d - 3) := by positivity
          have hC1 : (1 : ℝ) ≤ 2 * (d : ℝ) * 3 ^ (d - 1) := by
            have h1d : (1 : ℝ) ≤ 2 * (d : ℝ) := by
              have : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast (by omega : 1 ≤ d)
              linarith
            nlinarith [one_le_pow₀ (by norm_num : (1:ℝ) ≤ 3) (n := d - 1), h1d]
          have hlhs : (2 ^ (d - 1) / ((D : ℝ) + 1) ^ (d - 1))
              * (2 ^ d * ((D : ℝ) + 1) ^ d * (1 / (r : ℝ) ^ (d - 2)))
              = 2 ^ (d - 1) * 2 ^ d * ((D : ℝ) + 1) / (r : ℝ) ^ (d - 2) := by
            rw [show ((D : ℝ) + 1) ^ d = ((D : ℝ) + 1) ^ (d - 1) * ((D : ℝ) + 1)
                  from by rw [← pow_succ]; congr 1; omega]
            field_simp
          rw [hlhs, div_le_div_iff₀ hrp2 hrp3,
              show (r : ℝ) ^ (d - 2) = (r : ℝ) ^ (d - 3) * (r : ℝ)
                from by rw [← pow_succ]; congr 1; omega]
          have hA : (2 : ℝ) ^ (d - 1) * 2 ^ d ≤ 2 ^ (2 * d) * (2 * (d : ℝ) * 3 ^ (d - 1)) := by
            calc (2 : ℝ) ^ (d - 1) * 2 ^ d = 2 ^ (2 * d - 1) := by rw [← pow_add]; congr 1; omega
              _ ≤ 2 ^ (2 * d) := by apply pow_le_pow_right₀ (by norm_num); omega
              _ ≤ 2 ^ (2 * d) * (2 * (d : ℝ) * 3 ^ (d - 1)) :=
                  le_mul_of_one_le_right (by positivity) hC1
          calc 2 ^ (d - 1) * 2 ^ d * ((D : ℝ) + 1) * (r : ℝ) ^ (d - 3)
              ≤ 2 ^ (2 * d) * (2 * (d : ℝ) * 3 ^ (d - 1)) * (r : ℝ) * (r : ℝ) ^ (d - 3) :=
                mul_le_mul_of_nonneg_right
                  (mul_le_mul hA hDle (by positivity) (by positivity)) hrp3.le
            _ = 2 ^ (2 * d) * (2 * (d : ℝ) * 3 ^ (d - 1)) * ((r : ℝ) ^ (d - 3) * (r : ℝ)) := by ring


theorem conv_R3 {d : ℕ} (hd : 7 ≤ d) (u w : Fin d → ℤ) {r : ℕ} (hr : 1 ≤ r)
    (c : Fin d → ℤ) (K : ℕ) :
    ∑ v ∈ (linfBall c (K : ℤ)).filter
        (fun v => ¬(2 * linfDist w v ≤ linfDist u w) ∧ ¬(2 * linfDist u v ≤ linfDist u w)),
        (1 : ℝ) / ((linfDist u v + 1 : ℕ) : ℝ) ^ (d - 1)
          * (1 / (max (r : ℝ) ((linfDist w v + 1 : ℕ) : ℝ)) ^ (d - 2))
      ≤ 2 ^ (d - 3) * (3 ^ (d - 1) * (4 * (d : ℝ) * 3 ^ (d - 1)))
          / (max (r : ℝ) ((linfDist u w + 1 : ℕ) : ℝ)) ^ (d - 3) := by
  set D := linfDist u w with hD
  set Dmax := max (r : ℝ) ((D + 1 : ℕ) : ℝ) with hDmax
  have hDmax_pos : (0 : ℝ) < Dmax := by
    rw [hDmax]; exact lt_of_lt_of_le (by exact_mod_cast Nat.succ_pos D) (le_max_right _ _)
  -- single-center (w) radial bound, floor FL, clean constant 4d·3^{d-1}
  have hkey : ∀ (FL Kk : ℕ), 1 ≤ FL →
      ∑ v ∈ linfBall w (Kk : ℤ),
          (1 : ℝ) / (((linfDist w v + 1 : ℕ) : ℝ) ^ (d - 1)
            * (max (FL : ℝ) ((linfDist w v + 1 : ℕ) : ℝ)) ^ (d - 2))
        ≤ 4 * (d : ℝ) * 3 ^ (d - 1) / (FL : ℝ) ^ (d - 3) := by
    intro FL Kk hFL
    have hFLpos : (0 : ℝ) < (FL : ℝ) := by exact_mod_cast (by omega : 0 < FL)
    have hd3pos : (0 : ℝ) < ((d - 3 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < d - 3)
    have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
    have h := radial_div_sum_le (d := d) (by omega) w (d - 1) (by omega)
      (t := d - 3) (r := FL) (by omega) hFL Kk
    simp only [Nat.sub_self, Nat.zero_add, show d - 3 + 1 = d - 2 from by omega] at h
    refine le_trans h ?_
    rw [← mul_div_assoc,
        div_le_div_iff₀ (mul_pos hd3pos (pow_pos hFLpos _)) (pow_pos hFLpos _)]
    have h1 : (1 : ℝ) ≤ ((d - 3 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ d - 3)
    have hnum : 2 * (d : ℝ) * 3 ^ (d - 1) * (((d - 3 : ℕ) : ℝ) + 1)
        ≤ 4 * (d : ℝ) * 3 ^ (d - 1) * ((d - 3 : ℕ) : ℝ) := by
      nlinarith [h1, mul_pos hdpos (pow_pos (by norm_num : (0 : ℝ) < 3) (d - 1))]
    nlinarith [mul_le_mul_of_nonneg_right hnum (pow_nonneg hFLpos.le (d - 3))]
  -- subset: R3 ⊆ linfBall w (linfDist w c + K)
  have hsub : (linfBall c (K : ℤ)).filter
      (fun v => ¬(2 * linfDist w v ≤ D) ∧ ¬(2 * linfDist u v ≤ D))
      ⊆ linfBall w ((linfDist w c + K : ℕ) : ℤ) := by
    intro v hv
    rw [Finset.mem_filter] at hv
    have hvc : v ∈ linfBall c (K : ℤ) := hv.1
    rw [mem_linfBall_iff_dist c v (by positivity)] at hvc
    simp only [Int.toNat_natCast] at hvc
    rw [mem_linfBall_iff_dist w v (by positivity)]
    simp only [Int.toNat_natCast]
    have := linfDist_triangle w c v
    omega
  -- pull-out: on R3, |w-v|+1 ≤ 3(|u-v|+1), so 1/(|u-v|+1)^{d-1} ≤ 3^{d-1}/(|w-v|+1)^{d-1}.
  have hpull : ∀ v ∈ (linfBall c (K : ℤ)).filter
      (fun v => ¬(2 * linfDist w v ≤ D) ∧ ¬(2 * linfDist u v ≤ D)),
      (1 : ℝ) / ((linfDist u v + 1 : ℕ) : ℝ) ^ (d - 1)
          * (1 / (max (r : ℝ) ((linfDist w v + 1 : ℕ) : ℝ)) ^ (d - 2))
        ≤ 3 ^ (d - 1) * ((1 : ℝ) / (((linfDist w v + 1 : ℕ) : ℝ) ^ (d - 1)
            * (max (r : ℝ) ((linfDist w v + 1 : ℕ) : ℝ)) ^ (d - 2))) := by
    intro v hv
    rw [Finset.mem_filter] at hv
    have hwv : ¬(2 * linfDist w v ≤ D) := hv.2.1
    have huv : ¬(2 * linfDist u v ≤ D) := hv.2.2
    have htri : linfDist w v ≤ D + linfDist u v := by
      have h := linfDist_triangle w u v
      rw [linfDist_comm w u, ← hD] at h; omega
    have hnat : linfDist w v + 1 ≤ 3 * (linfDist u v + 1) := by omega
    have hcast : ((linfDist w v + 1 : ℕ) : ℝ) ≤ 3 * ((linfDist u v + 1 : ℕ) : ℝ) := by
      exact_mod_cast hnat
    have hWpos : (0 : ℝ) < ((linfDist w v + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos _
    have hUpos : (0 : ℝ) < ((linfDist u v + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos _
    have hMpos : (0 : ℝ) < max (r : ℝ) ((linfDist w v + 1 : ℕ) : ℝ) :=
      lt_of_lt_of_le hWpos (le_max_right _ _)
    have hUle : (1 : ℝ) / ((linfDist u v + 1 : ℕ) : ℝ) ^ (d - 1)
        ≤ 3 ^ (d - 1) / ((linfDist w v + 1 : ℕ) : ℝ) ^ (d - 1) := by
      rw [div_le_div_iff₀ (pow_pos hUpos _) (pow_pos hWpos _)]
      have hpw : ((linfDist w v + 1 : ℕ) : ℝ) ^ (d - 1)
          ≤ 3 ^ (d - 1) * ((linfDist u v + 1 : ℕ) : ℝ) ^ (d - 1) := by
        calc ((linfDist w v + 1 : ℕ) : ℝ) ^ (d - 1)
            ≤ (3 * ((linfDist u v + 1 : ℕ) : ℝ)) ^ (d - 1) := pow_le_pow_left₀ hWpos.le hcast _
          _ = 3 ^ (d - 1) * ((linfDist u v + 1 : ℕ) : ℝ) ^ (d - 1) := by rw [mul_pow]
      nlinarith [hpw]
    calc (1 : ℝ) / ((linfDist u v + 1 : ℕ) : ℝ) ^ (d - 1)
          * (1 / (max (r : ℝ) ((linfDist w v + 1 : ℕ) : ℝ)) ^ (d - 2))
        ≤ (3 ^ (d - 1) / ((linfDist w v + 1 : ℕ) : ℝ) ^ (d - 1))
            * (1 / (max (r : ℝ) ((linfDist w v + 1 : ℕ) : ℝ)) ^ (d - 2)) :=
          mul_le_mul_of_nonneg_right hUle (by positivity)
      _ = 3 ^ (d - 1) * ((1 : ℝ) / (((linfDist w v + 1 : ℕ) : ℝ) ^ (d - 1)
            * (max (r : ℝ) ((linfDist w v + 1 : ℕ) : ℝ)) ^ (d - 2))) := by
          rw [div_mul_div_comm, mul_one, ← mul_one_div]
  refine le_trans (Finset.sum_le_sum hpull) ?_
  rw [← Finset.mul_sum]
  by_cases hrD : r ≤ D
  · -- Case r ≤ D: bump floor r → L := D/2+1 (valid on R3), radial_div_sum_le @ L, max = D+1.
    set L := D / 2 + 1 with hLdef
    have hLpos : 1 ≤ L := by omega
    have hDval : Dmax = ((D + 1 : ℕ) : ℝ) := by
      rw [hDmax]; apply max_eq_right
      have : (r : ℝ) ≤ (D : ℝ) := by exact_mod_cast hrD
      push_cast; linarith
    have step1 : ∑ v ∈ (linfBall c (K : ℤ)).filter
          (fun v => ¬(2 * linfDist w v ≤ D) ∧ ¬(2 * linfDist u v ≤ D)),
          (1 : ℝ) / (((linfDist w v + 1 : ℕ) : ℝ) ^ (d - 1)
            * (max (r : ℝ) ((linfDist w v + 1 : ℕ) : ℝ)) ^ (d - 2))
        ≤ ∑ v ∈ (linfBall c (K : ℤ)).filter
          (fun v => ¬(2 * linfDist w v ≤ D) ∧ ¬(2 * linfDist u v ≤ D)),
          (1 : ℝ) / (((linfDist w v + 1 : ℕ) : ℝ) ^ (d - 1)
            * (max (L : ℝ) ((linfDist w v + 1 : ℕ) : ℝ)) ^ (d - 2)) := by
      apply Finset.sum_le_sum
      intro v hv
      rw [Finset.mem_filter] at hv
      have hwv : ¬(2 * linfDist w v ≤ D) := hv.2.1
      have hge : (L : ℝ) ≤ ((linfDist w v + 1 : ℕ) : ℝ) := by
        have : L ≤ linfDist w v + 1 := by omega
        exact_mod_cast this
      have hmm : max (L : ℝ) ((linfDist w v + 1 : ℕ) : ℝ)
          ≤ max (r : ℝ) ((linfDist w v + 1 : ℕ) : ℝ) := by
        rw [max_eq_right hge]; exact le_max_right _ _
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hmm _) (by positivity)
    have step2 := Finset.sum_le_sum_of_subset_of_nonneg hsub
      (f := fun v => (1 : ℝ) / (((linfDist w v + 1 : ℕ) : ℝ) ^ (d - 1)
        * (max (L : ℝ) ((linfDist w v + 1 : ℕ) : ℝ)) ^ (d - 2)))
      (fun v _ _ => by positivity)
    have hchain := step1.trans (step2.trans (hkey L _ hLpos))
    calc 3 ^ (d - 1) * ∑ v ∈ (linfBall c (K : ℤ)).filter
            (fun v => ¬(2 * linfDist w v ≤ D) ∧ ¬(2 * linfDist u v ≤ D)),
            (1 : ℝ) / (((linfDist w v + 1 : ℕ) : ℝ) ^ (d - 1)
              * (max (r : ℝ) ((linfDist w v + 1 : ℕ) : ℝ)) ^ (d - 2))
          ≤ 3 ^ (d - 1) * (4 * (d : ℝ) * 3 ^ (d - 1) / (L : ℝ) ^ (d - 3)) :=
            mul_le_mul_of_nonneg_left hchain (by positivity)
      _ ≤ 2 ^ (d - 3) * (3 ^ (d - 1) * (4 * (d : ℝ) * 3 ^ (d - 1))) / Dmax ^ (d - 3) := by
          rw [hDval]
          have hDR : ((D + 1 : ℕ) : ℝ) = (D : ℝ) + 1 := by push_cast; ring
          rw [hDR, ← mul_div_assoc]
          have hLp : (0 : ℝ) < (L : ℝ) ^ (d - 3) := by positivity
          have hDp : (0 : ℝ) < ((D : ℝ) + 1) ^ (d - 3) := by positivity
          rw [div_le_div_iff₀ hLp hDp]
          have h2L : ((D : ℝ) + 1) ≤ 2 * (L : ℝ) := by
            have : D + 1 ≤ 2 * L := by omega
            calc ((D : ℝ) + 1) = ((D + 1 : ℕ) : ℝ) := by push_cast; ring
              _ ≤ ((2 * L : ℕ) : ℝ) := by exact_mod_cast this
              _ = 2 * (L : ℝ) := by push_cast; ring
          have hple : ((D : ℝ) + 1) ^ (d - 3) ≤ 2 ^ (d - 3) * (L : ℝ) ^ (d - 3) := by
            calc ((D : ℝ) + 1) ^ (d - 3) ≤ (2 * (L : ℝ)) ^ (d - 3) :=
                  pow_le_pow_left₀ (by positivity) h2L _
              _ = 2 ^ (d - 3) * (L : ℝ) ^ (d - 3) := by rw [mul_pow]
          nlinarith [hple, pow_nonneg (by positivity : (0 : ℝ) ≤ (L : ℝ)) (d - 3),
            mul_nonneg (by positivity : (0:ℝ) ≤ 3 ^ (d - 1) * (4 * (d : ℝ) * 3 ^ (d - 1)))
              (pow_nonneg (by positivity : (0 : ℝ) ≤ (L : ℝ)) (d - 3))]
  · -- Case r > D: floor = r, radial_div_sum_le @ r, max = r.
    have hDval : Dmax = (r : ℝ) := by
      rw [hDmax]; apply max_eq_left
      have : (D : ℝ) + 1 ≤ (r : ℝ) := by
        have : D + 1 ≤ r := by omega
        exact_mod_cast this
      push_cast; linarith
    have step2 := Finset.sum_le_sum_of_subset_of_nonneg hsub
      (f := fun v => (1 : ℝ) / (((linfDist w v + 1 : ℕ) : ℝ) ^ (d - 1)
        * (max (r : ℝ) ((linfDist w v + 1 : ℕ) : ℝ)) ^ (d - 2)))
      (fun v _ _ => by positivity)
    have hchain := step2.trans (hkey r _ hr)
    calc 3 ^ (d - 1) * ∑ v ∈ (linfBall c (K : ℤ)).filter
            (fun v => ¬(2 * linfDist w v ≤ D) ∧ ¬(2 * linfDist u v ≤ D)),
            (1 : ℝ) / (((linfDist w v + 1 : ℕ) : ℝ) ^ (d - 1)
              * (max (r : ℝ) ((linfDist w v + 1 : ℕ) : ℝ)) ^ (d - 2))
          ≤ 3 ^ (d - 1) * (4 * (d : ℝ) * 3 ^ (d - 1) / (r : ℝ) ^ (d - 3)) :=
            mul_le_mul_of_nonneg_left hchain (by positivity)
      _ ≤ 2 ^ (d - 3) * (3 ^ (d - 1) * (4 * (d : ℝ) * 3 ^ (d - 1))) / Dmax ^ (d - 3) := by
          rw [hDval, ← mul_div_assoc]
          have hrp3 : (0 : ℝ) < (r : ℝ) ^ (d - 3) := by positivity
          rw [div_le_div_iff₀ hrp3 hrp3]
          have h1le : (1 : ℝ) ≤ 2 ^ (d - 3) := one_le_pow₀ (by norm_num)
          nlinarith [h1le, pow_nonneg (by positivity : (0 : ℝ) ≤ (r : ℝ)) (d - 3),
            mul_nonneg (by positivity : (0:ℝ) ≤ 3 ^ (d - 1) * (4 * (d : ℝ) * 3 ^ (d - 1)))
              (pow_nonneg (by positivity : (0 : ℝ) ≤ (r : ℝ)) (d - 3))]

/-- The two-center convolution estimate `∑_v |u-v|^{1-d} max(r,|w-v|)^{2-d} ≲ max(r,|u-w|)^{3-d}`
(main.tex ~6730, the key analytic step of `lem.err_cluster`), regularized and `K`-uniform. Proved by
the 3-region split `conv_R1`/`conv_R2`/`conv_R3` (partition of the ball by `v` nearest `w`/`u`/far),
each discharged by the shell engine. Constant depends on `d` only. -/
theorem conv_pointwise_le {d : ℕ} (hd : 7 ≤ d) (u w : Fin d → ℤ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {r : ℕ}, 1 ≤ r → ∀ (c : Fin d → ℤ) (K : ℕ),
      ∑ v ∈ linfBall c (K : ℤ),
          (1 : ℝ) / ((linfDist u v + 1 : ℕ) : ℝ) ^ (d - 1)
            * (1 / (max (r : ℝ) ((linfDist w v + 1 : ℕ) : ℝ)) ^ (d - 2))
        ≤ C / (max (r : ℝ) ((linfDist u w + 1 : ℕ) : ℝ)) ^ (d - 3) := by
  refine ⟨2 ^ (2 * d) * (2 * (d : ℝ) * 3 ^ (d - 1))
      + (2 ^ (d - 2) * (2 * (d : ℝ) * 3 ^ (d - 1))
        + 2 ^ (d - 3) * (3 ^ (d - 1) * (4 * (d : ℝ) * 3 ^ (d - 1)))), by positivity, ?_⟩
  intro r hr c K
  rw [← Finset.sum_filter_add_sum_filter_not (linfBall c (K : ℤ))
        (fun v => 2 * linfDist w v ≤ linfDist u w),
      ← Finset.sum_filter_add_sum_filter_not
        ((linfBall c (K : ℤ)).filter (fun v => ¬(2 * linfDist w v ≤ linfDist u w)))
        (fun v => 2 * linfDist u v ≤ linfDist u w),
      Finset.filter_filter, Finset.filter_filter]
  have h1 := conv_R1 (by omega) u w hr c K
  have h2 := conv_R2 (by omega) u w hr c K
  have h3 := conv_R3 hd u w hr c K
  calc ∑ v ∈ (linfBall c (K : ℤ)).filter (fun v => 2 * linfDist w v ≤ linfDist u w),
          (1 : ℝ) / ((linfDist u v + 1 : ℕ) : ℝ) ^ (d - 1)
            * (1 / (max (r : ℝ) ((linfDist w v + 1 : ℕ) : ℝ)) ^ (d - 2))
        + (∑ v ∈ (linfBall c (K : ℤ)).filter
            (fun v => ¬(2 * linfDist w v ≤ linfDist u w) ∧ 2 * linfDist u v ≤ linfDist u w),
            (1 : ℝ) / ((linfDist u v + 1 : ℕ) : ℝ) ^ (d - 1)
              * (1 / (max (r : ℝ) ((linfDist w v + 1 : ℕ) : ℝ)) ^ (d - 2))
          + ∑ v ∈ (linfBall c (K : ℤ)).filter
            (fun v => ¬(2 * linfDist w v ≤ linfDist u w) ∧ ¬(2 * linfDist u v ≤ linfDist u w)),
            (1 : ℝ) / ((linfDist u v + 1 : ℕ) : ℝ) ^ (d - 1)
              * (1 / (max (r : ℝ) ((linfDist w v + 1 : ℕ) : ℝ)) ^ (d - 2)))
      ≤ 2 ^ (2 * d) * (2 * (d : ℝ) * 3 ^ (d - 1))
            / (max (r : ℝ) ((linfDist u w + 1 : ℕ) : ℝ)) ^ (d - 3)
          + (2 ^ (d - 2) * (2 * (d : ℝ) * 3 ^ (d - 1))
              / (max (r : ℝ) ((linfDist u w + 1 : ℕ) : ℝ)) ^ (d - 3)
            + 2 ^ (d - 3) * (3 ^ (d - 1) * (4 * (d : ℝ) * 3 ^ (d - 1)))
              / (max (r : ℝ) ((linfDist u w + 1 : ℕ) : ℝ)) ^ (d - 3)) :=
        add_le_add h1 (add_le_add h2 h3)
    _ = (2 ^ (2 * d) * (2 * (d : ℝ) * 3 ^ (d - 1))
          + (2 ^ (d - 2) * (2 * (d : ℝ) * 3 ^ (d - 1))
            + 2 ^ (d - 3) * (3 ^ (d - 1) * (4 * (d : ℝ) * 3 ^ (d - 1)))))
          / (max (r : ℝ) ((linfDist u w + 1 : ℕ) : ℝ)) ^ (d - 3) := by
        rw [← add_div, ← add_div]

/-- The `u`-near-`w` branch region of `lem.err_cluster` after the convolution: the shell count
cancels `(|u-w|+1)^{3-d}` down to `(|u-w|+1)^2`, leaving the convergent `m`-tail
`err_cluster_radial_tail`. `K`-uniform; the `|x-u|^{-d} ∼ h^{-d}` factor is pulled out separately. -/
theorem cluster_branch_tail {d : ℕ} (hd : 7 ≤ d) {r : ℕ} (hr : 1 ≤ r) (w : Fin d → ℤ) (K : ℕ) :
    ∑ u ∈ linfBall w (K : ℤ),
        (1 : ℝ) / (((linfDist w u + 1 : ℕ) : ℝ) ^ (d - 3)
          * (max (r : ℝ) ((linfDist w u + 1 : ℕ) : ℝ)) ^ (d - 3))
      ≤ 2 * (d : ℝ) * 3 ^ (d - 1)
          * ((((d - 6 : ℕ) : ℝ) + 1) / (((d - 6 : ℕ) : ℝ) * (r : ℝ) ^ (d - 6))) := by
  refine le_trans (radial_sum_shell_bound (by omega) w K
    (fun j => (1 : ℝ) / (((j + 1 : ℕ) : ℝ) ^ (d - 3)
      * (max (r : ℝ) ((j + 1 : ℕ) : ℝ)) ^ (d - 3))) (fun j => by positivity)) ?_
  have hkey : ∀ j ∈ Finset.range (K + 1),
      2 * (d : ℝ) * 3 ^ (d - 1) * ((j + 1 : ℕ) : ℝ) ^ (d - 1)
          * ((1 : ℝ) / (((j + 1 : ℕ) : ℝ) ^ (d - 3)
              * (max (r : ℝ) ((j + 1 : ℕ) : ℝ)) ^ (d - 3)))
        = 2 * (d : ℝ) * 3 ^ (d - 1)
            * (((j + 1 : ℕ) : ℝ) ^ 2 / (max (r : ℝ) ((j + 1 : ℕ) : ℝ)) ^ (d - 3)) := by
    intro j _
    have hjpos : (0 : ℝ) < ((j + 1 : ℕ) : ℝ) := by positivity
    have hmax : (0 : ℝ) < max (r : ℝ) ((j + 1 : ℕ) : ℝ) :=
      lt_of_lt_of_le (by exact_mod_cast hr) (le_max_left _ _)
    have hsplit : ((j + 1 : ℕ) : ℝ) ^ (d - 1)
        = ((j + 1 : ℕ) : ℝ) ^ (d - 3) * ((j + 1 : ℕ) : ℝ) ^ 2 := by
      rw [← pow_add]; congr 1; omega
    rw [hsplit]; field_simp
  rw [Finset.sum_congr rfl hkey, ← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (err_cluster_radial_tail hd hr (K + 1)) (by positivity)

/-- Convergent shell tail from a cutoff: for `q ≥ d+1`, summing `(dist+1)^{-q}` over the lattice
points at `ℓ^∞`-distance `> L` from `c` gives `≲ (L+1)^{d-q}` (`K`-uniform). This is the
`|u-w| > k` tail that the source's `lem.err_boundary` per-pair sketch glosses over; it follows from
`radial_div_sum_le` at `p=0, t=q-d, r=L+1` (the max-floor at `L+1` equals `dist+1` on the tail). -/
theorem shell_tail_cutoff {d q : ℕ} (hd : 1 ≤ d) (hq : d + 1 ≤ q) (c : Fin d → ℤ) (L K : ℕ) :
    ∑ u ∈ (linfBall c (K : ℤ)).filter (fun u => L < linfDist c u),
        (1 : ℝ) / ((linfDist c u + 1 : ℕ) : ℝ) ^ q
      ≤ 2 * (d : ℝ) * 3 ^ (d - 1)
          * ((((q - d : ℕ) : ℝ) + 1) / (((q - d : ℕ) : ℝ) * ((L + 1 : ℕ) : ℝ) ^ (q - d))) := by
  have hrdl := radial_div_sum_le (d := d) hd c 0 (by omega) (t := q - d) (r := L + 1)
    (by omega) (by omega) K
  simp only [pow_zero, one_mul, show ((d - 1) - 0) + ((q - d) + 1) = q from by omega] at hrdl
  refine le_trans ?_ hrdl
  have hstep : ∑ u ∈ (linfBall c (K : ℤ)).filter (fun u => L < linfDist c u),
        (1 : ℝ) / ((linfDist c u + 1 : ℕ) : ℝ) ^ q
      = ∑ u ∈ (linfBall c (K : ℤ)).filter (fun u => L < linfDist c u),
        (1 : ℝ) / (max ((L + 1 : ℕ) : ℝ) ((linfDist c u + 1 : ℕ) : ℝ)) ^ q := by
    apply Finset.sum_congr rfl
    intro u hu
    rw [Finset.mem_filter] at hu
    have hge : ((L + 1 : ℕ) : ℝ) ≤ ((linfDist c u + 1 : ℕ) : ℝ) := by
      have : L + 1 ≤ linfDist c u + 1 := by omega
      exact_mod_cast this
    rw [max_eq_right hge]
  rw [hstep]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun u _ _ => by positivity)

/-- Explicit-constant form of `conv_pointwise_le` (same assembly, constant exposed so it can be
summed over the branch point `u` in the per-`w` err_cluster derivation). -/
theorem conv_pointwise_le_const {d : ℕ} (hd : 7 ≤ d) (u w : Fin d → ℤ) {r : ℕ} (hr : 1 ≤ r)
    (c : Fin d → ℤ) (K : ℕ) :
    ∑ v ∈ linfBall c (K : ℤ),
        (1 : ℝ) / ((linfDist u v + 1 : ℕ) : ℝ) ^ (d - 1)
          * (1 / (max (r : ℝ) ((linfDist w v + 1 : ℕ) : ℝ)) ^ (d - 2))
      ≤ (2 ^ (2 * d) * (2 * (d : ℝ) * 3 ^ (d - 1))
          + (2 ^ (d - 2) * (2 * (d : ℝ) * 3 ^ (d - 1))
            + 2 ^ (d - 3) * (3 ^ (d - 1) * (4 * (d : ℝ) * 3 ^ (d - 1)))))
          / (max (r : ℝ) ((linfDist u w + 1 : ℕ) : ℝ)) ^ (d - 3) := by
  rw [← Finset.sum_filter_add_sum_filter_not (linfBall c (K : ℤ))
        (fun v => 2 * linfDist w v ≤ linfDist u w),
      ← Finset.sum_filter_add_sum_filter_not
        ((linfBall c (K : ℤ)).filter (fun v => ¬(2 * linfDist w v ≤ linfDist u w)))
        (fun v => 2 * linfDist u v ≤ linfDist u w),
      Finset.filter_filter, Finset.filter_filter]
  have h1 := conv_R1 (by omega) u w hr c K
  have h2 := conv_R2 (by omega) u w hr c K
  have h3 := conv_R3 hd u w hr c K
  calc ∑ v ∈ (linfBall c (K : ℤ)).filter (fun v => 2 * linfDist w v ≤ linfDist u w),
          (1 : ℝ) / ((linfDist u v + 1 : ℕ) : ℝ) ^ (d - 1)
            * (1 / (max (r : ℝ) ((linfDist w v + 1 : ℕ) : ℝ)) ^ (d - 2))
        + (∑ v ∈ (linfBall c (K : ℤ)).filter
            (fun v => ¬(2 * linfDist w v ≤ linfDist u w) ∧ 2 * linfDist u v ≤ linfDist u w),
            (1 : ℝ) / ((linfDist u v + 1 : ℕ) : ℝ) ^ (d - 1)
              * (1 / (max (r : ℝ) ((linfDist w v + 1 : ℕ) : ℝ)) ^ (d - 2))
          + ∑ v ∈ (linfBall c (K : ℤ)).filter
            (fun v => ¬(2 * linfDist w v ≤ linfDist u w) ∧ ¬(2 * linfDist u v ≤ linfDist u w)),
            (1 : ℝ) / ((linfDist u v + 1 : ℕ) : ℝ) ^ (d - 1)
              * (1 / (max (r : ℝ) ((linfDist w v + 1 : ℕ) : ℝ)) ^ (d - 2)))
      ≤ 2 ^ (2 * d) * (2 * (d : ℝ) * 3 ^ (d - 1))
            / (max (r : ℝ) ((linfDist u w + 1 : ℕ) : ℝ)) ^ (d - 3)
          + (2 ^ (d - 2) * (2 * (d : ℝ) * 3 ^ (d - 1))
              / (max (r : ℝ) ((linfDist u w + 1 : ℕ) : ℝ)) ^ (d - 3)
            + 2 ^ (d - 3) * (3 ^ (d - 1) * (4 * (d : ℝ) * 3 ^ (d - 1)))
              / (max (r : ℝ) ((linfDist u w + 1 : ℕ) : ℝ)) ^ (d - 3)) :=
        add_le_add h1 (add_le_add h2 h3)
    _ = (2 ^ (2 * d) * (2 * (d : ℝ) * 3 ^ (d - 1))
          + (2 ^ (d - 2) * (2 * (d : ℝ) * 3 ^ (d - 1))
            + 2 ^ (d - 3) * (3 ^ (d - 1) * (4 * (d : ℝ) * 3 ^ (d - 1)))))
          / (max (r : ℝ) ((linfDist u w + 1 : ℕ) : ℝ)) ^ (d - 3) := by
        rw [← add_div, ← add_div]

/-- Per-`w` convolution step of `lem.err_cluster` (deterministic): given the BK + one-sided pointwise
bound `hBK` (`P v ≤ ∑_u A u·(|u-v|_∞+1)^{1-d}`, where `A u` lumps `τ(x,u)·τ(u,w)·(1+l_u)`), the
`v`-sum of `P v · max(r,|w-v|)^{2-d}` is bounded by the branch-point sum `∑_u A u·C/max(r,|u-w|+1)^{d-3}`
via `conv_pointwise_le_const`. This is the exact point where the convolution estimate enters the
err_cluster proof; `A`, `P` are abstract, so the only cited content (BK + the one pointwise bound) is
in `hBK`. -/
theorem perW_conv_step {d : ℕ} (hd : 7 ≤ d) (w : Fin d → ℤ) {r : ℕ} (hr : 1 ≤ r)
    (c : Fin d → ℤ) (K : ℕ) (A : (Fin d → ℤ) → ℝ) (hA : ∀ u, 0 ≤ A u)
    (P : (Fin d → ℤ) → ℝ)
    (hBK : ∀ v ∈ linfBall c (K : ℤ),
      P v ≤ ∑ u ∈ linfBall c (K : ℤ), A u * (1 / ((linfDist u v + 1 : ℕ) : ℝ) ^ (d - 1))) :
    ∑ v ∈ linfBall c (K : ℤ),
        P v * (1 / (max (r : ℝ) ((linfDist w v + 1 : ℕ) : ℝ)) ^ (d - 2))
      ≤ ∑ u ∈ linfBall c (K : ℤ),
          A u * ((2 ^ (2 * d) * (2 * (d : ℝ) * 3 ^ (d - 1))
              + (2 ^ (d - 2) * (2 * (d : ℝ) * 3 ^ (d - 1))
                + 2 ^ (d - 3) * (3 ^ (d - 1) * (4 * (d : ℝ) * 3 ^ (d - 1)))))
            / (max (r : ℝ) ((linfDist u w + 1 : ℕ) : ℝ)) ^ (d - 3)) := by
  -- Step 1: bound P v by hBK, times the nonneg weight M(v).
  have hMnn : ∀ v, (0 : ℝ) ≤ 1 / (max (r : ℝ) ((linfDist w v + 1 : ℕ) : ℝ)) ^ (d - 2) :=
    fun v => by positivity
  refine le_trans (Finset.sum_le_sum (fun v hv =>
    mul_le_mul_of_nonneg_right (hBK v hv) (hMnn v))) ?_
  -- Now: ∑_v (∑_u A u/(|uv|+1)^{d-1}) * M(v) ≤ RHS.  Distribute, swap, factor, apply conv_const.
  have hstep : ∀ v ∈ linfBall c (K : ℤ),
      (∑ u ∈ linfBall c (K : ℤ), A u * (1 / ((linfDist u v + 1 : ℕ) : ℝ) ^ (d - 1)))
        * (1 / (max (r : ℝ) ((linfDist w v + 1 : ℕ) : ℝ)) ^ (d - 2))
      = ∑ u ∈ linfBall c (K : ℤ),
          A u * ((1 / ((linfDist u v + 1 : ℕ) : ℝ) ^ (d - 1))
            * (1 / (max (r : ℝ) ((linfDist w v + 1 : ℕ) : ℝ)) ^ (d - 2))) := by
    intro v _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro u _
    ring
  rw [Finset.sum_congr rfl hstep, Finset.sum_comm]
  apply Finset.sum_le_sum
  intro u _
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (conv_pointwise_le_const hd u w hr c K) (hA u)

/-- u-near-w region of the err_cluster per-w branch sum: pull out `|x-u|^{-d} ≤ 2^d/(h+1)^d`
(from `2|x-u| ≥ |x-w| ≥ h`), bound `(ℓu+1)³ ≤ 8(|w-u|+1)³`, residual is `cluster_branch_tail`. -/
theorem perW_Rw {d : ℕ} (hd : 7 ≤ d) (x w : Fin d → ℤ) (ℓ : (Fin d → ℤ) → ℕ) {r : ℕ} (hr : 1 ≤ r)
    {h : ℕ} (hh : 1 ≤ h) (hxw : h ≤ linfDist x w)
    (hℓ : ∀ u, ℓ u ≤ 1 + min (linfDist x u) (linfDist u w)) (c : Fin d → ℤ) (K : ℕ) :
    ∑ u ∈ (linfBall c (K : ℤ)).filter (fun u => linfDist u w ≤ linfDist x u),
        ((ℓ u + 1 : ℕ) : ℝ) ^ 3
          / (((linfDist x u + 1 : ℕ) : ℝ) ^ d * ((linfDist w u + 1 : ℕ) : ℝ) ^ d
            * (max (r : ℝ) ((linfDist w u + 1 : ℕ) : ℝ)) ^ (d - 3))
      ≤ (8 * 2 ^ d / ((h : ℝ) + 1) ^ d)
          * (2 * (d : ℝ) * 3 ^ (d - 1)
            * ((((d - 6 : ℕ) : ℝ) + 1) / (((d - 6 : ℕ) : ℝ) * (r : ℝ) ^ (d - 6)))) := by
  have hsub : (linfBall c (K : ℤ)).filter (fun u => linfDist u w ≤ linfDist x u)
      ⊆ linfBall w ((linfDist w c + K : ℕ) : ℤ) := by
    intro u hu
    rw [Finset.mem_filter] at hu
    have huc : u ∈ linfBall c (K : ℤ) := hu.1
    rw [mem_linfBall_iff_dist c u (by positivity)] at huc
    simp only [Int.toNat_natCast] at huc
    rw [mem_linfBall_iff_dist w u (by positivity)]
    simp only [Int.toNat_natCast]
    have := linfDist_triangle w c u
    omega
  have hterm : ∀ u ∈ (linfBall c (K : ℤ)).filter (fun u => linfDist u w ≤ linfDist x u),
      ((ℓ u + 1 : ℕ) : ℝ) ^ 3
          / (((linfDist x u + 1 : ℕ) : ℝ) ^ d * ((linfDist w u + 1 : ℕ) : ℝ) ^ d
            * (max (r : ℝ) ((linfDist w u + 1 : ℕ) : ℝ)) ^ (d - 3))
        ≤ (8 * 2 ^ d / ((h : ℝ) + 1) ^ d)
          * (1 / (((linfDist w u + 1 : ℕ) : ℝ) ^ (d - 3)
              * (max (r : ℝ) ((linfDist w u + 1 : ℕ) : ℝ)) ^ (d - 3))) := by
    intro u hu
    rw [Finset.mem_filter] at hu
    have hreg : linfDist u w ≤ linfDist x u := hu.2
    have hx2 : h ≤ 2 * linfDist x u := by
      have htri := linfDist_triangle x u w; omega
    have hwu : linfDist w u = linfDist u w := linfDist_comm w u
    have hlcube : ((ℓ u + 1 : ℕ) : ℝ) ^ 3 ≤ 8 * ((linfDist w u + 1 : ℕ) : ℝ) ^ 3 := by
      have hln : ℓ u + 1 ≤ 2 * (linfDist w u + 1) := by have := hℓ u; omega
      have hc1 : ((ℓ u + 1 : ℕ) : ℝ) ≤ 2 * ((linfDist w u + 1 : ℕ) : ℝ) := by
        calc ((ℓ u + 1 : ℕ) : ℝ) ≤ ((2 * (linfDist w u + 1) : ℕ) : ℝ) := by exact_mod_cast hln
          _ = 2 * ((linfDist w u + 1 : ℕ) : ℝ) := by push_cast; ring
      calc ((ℓ u + 1 : ℕ) : ℝ) ^ 3 ≤ (2 * ((linfDist w u + 1 : ℕ) : ℝ)) ^ 3 :=
            pow_le_pow_left₀ (by positivity) hc1 3
        _ = 8 * ((linfDist w u + 1 : ℕ) : ℝ) ^ 3 := by ring
    have hxpow : ((h : ℝ) + 1) ^ d ≤ 2 ^ d * ((linfDist x u + 1 : ℕ) : ℝ) ^ d := by
      have hc2 : ((h : ℝ) + 1) ≤ 2 * ((linfDist x u + 1 : ℕ) : ℝ) := by
        have : h + 1 ≤ 2 * (linfDist x u + 1) := by omega
        calc ((h : ℝ) + 1) = ((h + 1 : ℕ) : ℝ) := by push_cast; ring
          _ ≤ ((2 * (linfDist x u + 1) : ℕ) : ℝ) := by exact_mod_cast this
          _ = 2 * ((linfDist x u + 1 : ℕ) : ℝ) := by push_cast; ring
      calc ((h : ℝ) + 1) ^ d ≤ (2 * ((linfDist x u + 1 : ℕ) : ℝ)) ^ d :=
            pow_le_pow_left₀ (by positivity) hc2 _
        _ = 2 ^ d * ((linfDist x u + 1 : ℕ) : ℝ) ^ d := by rw [mul_pow]
    have hWpos : (0 : ℝ) < ((linfDist w u + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos _
    have hXpos : (0 : ℝ) < ((linfDist x u + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos _
    have hMpos : (0 : ℝ) < max (r : ℝ) ((linfDist w u + 1 : ℕ) : ℝ) :=
      lt_of_lt_of_le (by exact_mod_cast hr) (le_max_left _ _)
    have hhpos : (0 : ℝ) < (h : ℝ) + 1 := by positivity
    rw [div_mul_div_comm, mul_one,
        div_le_div_iff₀ (by positivity) (by positivity),
        show ((linfDist w u + 1 : ℕ) : ℝ) ^ d
            = ((linfDist w u + 1 : ℕ) : ℝ) ^ (d - 3) * ((linfDist w u + 1 : ℕ) : ℝ) ^ 3
          from by rw [← pow_add]; congr 1; omega]
    have hprod : ((ℓ u + 1 : ℕ) : ℝ) ^ 3 * ((h : ℝ) + 1) ^ d
        ≤ 8 * 2 ^ d * (((linfDist x u + 1 : ℕ) : ℝ) ^ d * ((linfDist w u + 1 : ℕ) : ℝ) ^ 3) := by
      calc ((ℓ u + 1 : ℕ) : ℝ) ^ 3 * ((h : ℝ) + 1) ^ d
          ≤ (8 * ((linfDist w u + 1 : ℕ) : ℝ) ^ 3) * (2 ^ d * ((linfDist x u + 1 : ℕ) : ℝ) ^ d) :=
            mul_le_mul hlcube hxpow (by positivity) (by positivity)
        _ = 8 * 2 ^ d * (((linfDist x u + 1 : ℕ) : ℝ) ^ d * ((linfDist w u + 1 : ℕ) : ℝ) ^ 3) := by
            ring
    nlinarith [mul_le_mul_of_nonneg_right hprod
      (mul_nonneg (pow_nonneg hWpos.le (d - 3)) (pow_nonneg hMpos.le (d - 3))),
      pow_pos hWpos (d - 3), pow_pos hMpos (d - 3), pow_pos hXpos d]
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.mul_sum]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun u _ _ => by positivity))
    (cluster_branch_tail hd hr w ((linfDist w c + K : ℕ)))

/-- u-near-x region of the err_cluster per-w branch sum: near/far sub-split on `|x-u| ≤ h`;
near uses `|u-w| ≥ h/2` + `branch_shell_cubic_sum`, far uses `|u-w| > |x-u| > h` + `shell_tail_cutoff`. -/
theorem perW_Rx {d : ℕ} (hd : 7 ≤ d) (x w : Fin d → ℤ) (ℓ : (Fin d → ℤ) → ℕ) {r : ℕ} (hr : 1 ≤ r)
    {h : ℕ} (hh : 1 ≤ h) (hxw : h ≤ linfDist x w)
    (hℓ : ∀ u, ℓ u ≤ 1 + min (linfDist x u) (linfDist u w)) (c : Fin d → ℤ) (K : ℕ) :
    ∑ u ∈ (linfBall c (K : ℤ)).filter (fun u => linfDist x u < linfDist u w),
        ((ℓ u + 1 : ℕ) : ℝ) ^ 3
          / (((linfDist x u + 1 : ℕ) : ℝ) ^ d * ((linfDist w u + 1 : ℕ) : ℝ) ^ d
            * (max (r : ℝ) ((linfDist w u + 1 : ℕ) : ℝ)) ^ (d - 3))
      ≤ 2 ^ (2 * d) * (2 * (d : ℝ) * 3 ^ (d - 1)) * (((h : ℝ) + 1) ^ 3 / ((h : ℝ) + 1) ^ (2 * d - 3))
        + 8 * (2 * (d : ℝ) * 3 ^ (d - 1))
          * ((((2 * d - 6 : ℕ) : ℝ) + 1)
            / (((2 * d - 6 : ℕ) : ℝ) * ((h + 1 : ℕ) : ℝ) ^ (2 * d - 6))) := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not
        ((linfBall c (K : ℤ)).filter (fun u => linfDist x u < linfDist u w))
        (fun u => linfDist x u ≤ h), Finset.filter_filter, Finset.filter_filter]
  apply add_le_add
  · -- NEAR: |x-u| < |u-w| ∧ |x-u| ≤ h
    have hterm : ∀ u ∈ (linfBall c (K : ℤ)).filter
        (fun u => linfDist x u < linfDist u w ∧ linfDist x u ≤ h),
        ((ℓ u + 1 : ℕ) : ℝ) ^ 3
          / (((linfDist x u + 1 : ℕ) : ℝ) ^ d * ((linfDist w u + 1 : ℕ) : ℝ) ^ d
            * (max (r : ℝ) ((linfDist w u + 1 : ℕ) : ℝ)) ^ (d - 3))
        ≤ (2 ^ (2 * d) / ((h : ℝ) + 1) ^ (2 * d - 3))
            * (1 / ((linfDist x u + 1 : ℕ) : ℝ) ^ (d - 3)) := by
      intro u hu
      rw [Finset.mem_filter] at hu
      obtain ⟨_, hreg, hle⟩ := hu
      have hwu : linfDist w u = linfDist u w := linfDist_comm w u
      have h2w : h ≤ 2 * linfDist u w := by
        have htri := linfDist_triangle x u w; omega
      have hXpos : (0 : ℝ) < ((linfDist x u + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos _
      have hWpos : (0 : ℝ) < ((linfDist w u + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos _
      have hMpos : (0 : ℝ) < max (r : ℝ) ((linfDist w u + 1 : ℕ) : ℝ) :=
        lt_of_lt_of_le (by exact_mod_cast hr) (le_max_left _ _)
      have hhpos : (0 : ℝ) < (h : ℝ) + 1 := by positivity
      -- (ℓu+1)³ ≤ 8 (|x-u|+1)³
      have hlx : ((ℓ u + 1 : ℕ) : ℝ) ^ 3 ≤ 8 * ((linfDist x u + 1 : ℕ) : ℝ) ^ 3 := by
        have hln : ℓ u + 1 ≤ 2 * (linfDist x u + 1) := by have := hℓ u; omega
        have : ((ℓ u + 1 : ℕ) : ℝ) ≤ 2 * ((linfDist x u + 1 : ℕ) : ℝ) := by
          calc ((ℓ u + 1 : ℕ) : ℝ) ≤ ((2 * (linfDist x u + 1) : ℕ) : ℝ) := by exact_mod_cast hln
            _ = 2 * ((linfDist x u + 1 : ℕ) : ℝ) := by push_cast; ring
        calc ((ℓ u + 1 : ℕ) : ℝ) ^ 3 ≤ (2 * ((linfDist x u + 1 : ℕ) : ℝ)) ^ 3 :=
              pow_le_pow_left₀ (by positivity) this 3
          _ = 8 * ((linfDist x u + 1 : ℕ) : ℝ) ^ 3 := by ring
      -- (h+1) ≤ 2 (|w-u|+1)
      have hhw : ((h : ℝ) + 1) ≤ 2 * ((linfDist w u + 1 : ℕ) : ℝ) := by
        have : h + 1 ≤ 2 * (linfDist w u + 1) := by omega
        calc ((h : ℝ) + 1) = ((h + 1 : ℕ) : ℝ) := by push_cast; ring
          _ ≤ ((2 * (linfDist w u + 1) : ℕ) : ℝ) := by exact_mod_cast this
          _ = 2 * ((linfDist w u + 1 : ℕ) : ℝ) := by push_cast; ring
      have hwpow : ((h : ℝ) + 1) ^ d ≤ 2 ^ d * ((linfDist w u + 1 : ℕ) : ℝ) ^ d := by
        calc ((h : ℝ) + 1) ^ d ≤ (2 * ((linfDist w u + 1 : ℕ) : ℝ)) ^ d :=
              pow_le_pow_left₀ (by positivity) hhw _
          _ = 2 ^ d * ((linfDist w u + 1 : ℕ) : ℝ) ^ d := by rw [mul_pow]
      have hmpow : ((h : ℝ) + 1) ^ (d - 3)
          ≤ 2 ^ (d - 3) * (max (r : ℝ) ((linfDist w u + 1 : ℕ) : ℝ)) ^ (d - 3) := by
        calc ((h : ℝ) + 1) ^ (d - 3)
            ≤ (2 * max (r : ℝ) ((linfDist w u + 1 : ℕ) : ℝ)) ^ (d - 3) :=
              pow_le_pow_left₀ (by positivity)
                (le_trans hhw (by nlinarith [le_max_right (r : ℝ) ((linfDist w u + 1 : ℕ) : ℝ),
                  hWpos.le])) _
          _ = 2 ^ (d - 3) * (max (r : ℝ) ((linfDist w u + 1 : ℕ) : ℝ)) ^ (d - 3) := by rw [mul_pow]
      rw [div_mul_div_comm, mul_one, div_le_div_iff₀ (by positivity) (by positivity),
          show ((linfDist x u + 1 : ℕ) : ℝ) ^ d
              = ((linfDist x u + 1 : ℕ) : ℝ) ^ 3 * ((linfDist x u + 1 : ℕ) : ℝ) ^ (d - 3)
            from by rw [← pow_add]; congr 1; omega,
          show ((h : ℝ) + 1) ^ (2 * d - 3)
              = (((h : ℝ) + 1) ^ d * ((h : ℝ) + 1) ^ (d - 3)) * 1
            from by rw [mul_one, ← pow_add]; congr 1; omega]
      have hprod : ((ℓ u + 1 : ℕ) : ℝ) ^ 3 * ((h : ℝ) + 1) ^ d * ((h : ℝ) + 1) ^ (d - 3)
          ≤ 2 ^ (2 * d) * (((linfDist x u + 1 : ℕ) : ℝ) ^ 3 * ((linfDist w u + 1 : ℕ) : ℝ) ^ d
              * (max (r : ℝ) ((linfDist w u + 1 : ℕ) : ℝ)) ^ (d - 3)) := by
        have e1 := mul_le_mul hlx hwpow (by positivity) (by positivity)
        have e2 := mul_le_mul e1 hmpow (by positivity) (by positivity)
        calc ((ℓ u + 1 : ℕ) : ℝ) ^ 3 * ((h : ℝ) + 1) ^ d * ((h : ℝ) + 1) ^ (d - 3)
            ≤ 8 * ((linfDist x u + 1 : ℕ) : ℝ) ^ 3 * (2 ^ d * ((linfDist w u + 1 : ℕ) : ℝ) ^ d)
                * (2 ^ (d - 3) * (max (r : ℝ) ((linfDist w u + 1 : ℕ) : ℝ)) ^ (d - 3)) := e2
          _ = (8 * 2 ^ d * 2 ^ (d - 3)) * (((linfDist x u + 1 : ℕ) : ℝ) ^ 3
                * ((linfDist w u + 1 : ℕ) : ℝ) ^ d
                * (max (r : ℝ) ((linfDist w u + 1 : ℕ) : ℝ)) ^ (d - 3)) := by ring
          _ = 2 ^ (2 * d) * (((linfDist x u + 1 : ℕ) : ℝ) ^ 3 * ((linfDist w u + 1 : ℕ) : ℝ) ^ d
                * (max (r : ℝ) ((linfDist w u + 1 : ℕ) : ℝ)) ^ (d - 3)) := by
              rw [show (8 : ℝ) * 2 ^ d * 2 ^ (d - 3) = 2 ^ (2 * d) from by
                rw [show (8 : ℝ) = 2 ^ 3 from by norm_num, ← pow_add, ← pow_add]; congr 1; omega]
      nlinarith [mul_le_mul_of_nonneg_right hprod
        (pow_nonneg hXpos.le (d - 3)), pow_pos hXpos (d - 3)]
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [← Finset.mul_sum]
    have hsub : (linfBall c (K : ℤ)).filter
        (fun u => linfDist x u < linfDist u w ∧ linfDist x u ≤ h)
        ⊆ linfBall x (h : ℤ) := by
      intro u hu
      rw [Finset.mem_filter] at hu
      rw [mem_linfBall_iff_dist x u (by positivity)]
      simp only [Int.toNat_natCast]
      exact hu.2.2
    have hbsc := le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun u _ _ => by positivity))
      (branch_shell_cubic_sum (by omega) x h)
    calc (2 ^ (2 * d) / ((h : ℝ) + 1) ^ (2 * d - 3))
          * ∑ u ∈ (linfBall c (K : ℤ)).filter
              (fun u => linfDist x u < linfDist u w ∧ linfDist x u ≤ h),
              (1 / ((linfDist x u + 1 : ℕ) : ℝ) ^ (d - 3))
        ≤ (2 ^ (2 * d) / ((h : ℝ) + 1) ^ (2 * d - 3)) * (2 * (d : ℝ) * 3 ^ (d - 1) * ((h : ℝ) + 1) ^ 3) :=
          mul_le_mul_of_nonneg_left hbsc (by positivity)
      _ = 2 ^ (2 * d) * (2 * (d : ℝ) * 3 ^ (d - 1)) * (((h : ℝ) + 1) ^ 3 / ((h : ℝ) + 1) ^ (2 * d - 3)) := by
          ring
  · -- FAR: |x-u| < |u-w| ∧ ¬(|x-u| ≤ h)
    have hterm : ∀ u ∈ (linfBall c (K : ℤ)).filter
        (fun u => linfDist x u < linfDist u w ∧ ¬ linfDist x u ≤ h),
        ((ℓ u + 1 : ℕ) : ℝ) ^ 3
          / (((linfDist x u + 1 : ℕ) : ℝ) ^ d * ((linfDist w u + 1 : ℕ) : ℝ) ^ d
            * (max (r : ℝ) ((linfDist w u + 1 : ℕ) : ℝ)) ^ (d - 3))
        ≤ 8 * (1 / ((linfDist x u + 1 : ℕ) : ℝ) ^ (3 * d - 6)) := by
      intro u hu
      rw [Finset.mem_filter] at hu
      obtain ⟨_, hreg, _⟩ := hu
      have hwu : linfDist w u = linfDist u w := linfDist_comm w u
      have hXpos : (0 : ℝ) < ((linfDist x u + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos _
      have hWpos : (0 : ℝ) < ((linfDist w u + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos _
      have hMpos : (0 : ℝ) < max (r : ℝ) ((linfDist w u + 1 : ℕ) : ℝ) :=
        lt_of_lt_of_le (by exact_mod_cast hr) (le_max_left _ _)
      have hlx : ((ℓ u + 1 : ℕ) : ℝ) ^ 3 ≤ 8 * ((linfDist x u + 1 : ℕ) : ℝ) ^ 3 := by
        have hln : ℓ u + 1 ≤ 2 * (linfDist x u + 1) := by have := hℓ u; omega
        have : ((ℓ u + 1 : ℕ) : ℝ) ≤ 2 * ((linfDist x u + 1 : ℕ) : ℝ) := by
          calc ((ℓ u + 1 : ℕ) : ℝ) ≤ ((2 * (linfDist x u + 1) : ℕ) : ℝ) := by exact_mod_cast hln
            _ = 2 * ((linfDist x u + 1 : ℕ) : ℝ) := by push_cast; ring
        calc ((ℓ u + 1 : ℕ) : ℝ) ^ 3 ≤ (2 * ((linfDist x u + 1 : ℕ) : ℝ)) ^ 3 :=
              pow_le_pow_left₀ (by positivity) this 3
          _ = 8 * ((linfDist x u + 1 : ℕ) : ℝ) ^ 3 := by ring
      have hxw' : ((linfDist x u + 1 : ℕ) : ℝ) ≤ ((linfDist w u + 1 : ℕ) : ℝ) := by
        have : linfDist x u + 1 ≤ linfDist w u + 1 := by omega
        exact_mod_cast this
      have hxm : ((linfDist x u + 1 : ℕ) : ℝ) ≤ max (r : ℝ) ((linfDist w u + 1 : ℕ) : ℝ) :=
        le_trans hxw' (le_max_right _ _)
      have hdenge : ((linfDist x u + 1 : ℕ) : ℝ) ^ (3 * d - 3)
          ≤ ((linfDist x u + 1 : ℕ) : ℝ) ^ d * ((linfDist w u + 1 : ℕ) : ℝ) ^ d
            * (max (r : ℝ) ((linfDist w u + 1 : ℕ) : ℝ)) ^ (d - 3) := by
        rw [show 3 * d - 3 = d + d + (d - 3) from by omega, pow_add, pow_add]
        gcongr
      calc ((ℓ u + 1 : ℕ) : ℝ) ^ 3
            / (((linfDist x u + 1 : ℕ) : ℝ) ^ d * ((linfDist w u + 1 : ℕ) : ℝ) ^ d
              * (max (r : ℝ) ((linfDist w u + 1 : ℕ) : ℝ)) ^ (d - 3))
          ≤ (8 * ((linfDist x u + 1 : ℕ) : ℝ) ^ 3)
            / (((linfDist x u + 1 : ℕ) : ℝ) ^ d * ((linfDist w u + 1 : ℕ) : ℝ) ^ d
              * (max (r : ℝ) ((linfDist w u + 1 : ℕ) : ℝ)) ^ (d - 3)) := by gcongr
        _ ≤ (8 * ((linfDist x u + 1 : ℕ) : ℝ) ^ 3) / ((linfDist x u + 1 : ℕ) : ℝ) ^ (3 * d - 3) := by
            gcongr
        _ = 8 * (1 / ((linfDist x u + 1 : ℕ) : ℝ) ^ (3 * d - 6)) := by
            rw [show 3 * d - 3 = 3 + (3 * d - 6) from by omega, pow_add, mul_div_assoc,
                div_mul_eq_div_div, div_self (by positivity)]
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [← Finset.mul_sum]
    have hsub : (linfBall c (K : ℤ)).filter
        (fun u => linfDist x u < linfDist u w ∧ ¬ linfDist x u ≤ h)
        ⊆ (linfBall x ((linfDist x c + K : ℕ) : ℤ)).filter (fun u => h < linfDist x u) := by
      intro u hu
      rw [Finset.mem_filter] at hu ⊢
      refine ⟨?_, by omega⟩
      have huc : u ∈ linfBall c (K : ℤ) := hu.1
      rw [mem_linfBall_iff_dist c u (by positivity)] at huc
      simp only [Int.toNat_natCast] at huc
      rw [mem_linfBall_iff_dist x u (by positivity)]
      simp only [Int.toNat_natCast]
      have := linfDist_triangle x c u
      omega
    have hst := le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun u _ _ => by positivity))
      (shell_tail_cutoff (d := d) (q := 3 * d - 6) (by omega) (by omega) x h
        ((linfDist x c + K : ℕ)))
    calc (8 : ℝ) * ∑ u ∈ (linfBall c (K : ℤ)).filter
            (fun u => linfDist x u < linfDist u w ∧ ¬ linfDist x u ≤ h),
            (1 / ((linfDist x u + 1 : ℕ) : ℝ) ^ (3 * d - 6))
        ≤ 8 * (2 * (d : ℝ) * 3 ^ (d - 1)
            * ((((3 * d - 6 - d : ℕ) : ℝ) + 1)
              / (((3 * d - 6 - d : ℕ) : ℝ) * ((h + 1 : ℕ) : ℝ) ^ (3 * d - 6 - d)))) :=
          mul_le_mul_of_nonneg_left hst (by norm_num)
      _ = 8 * (2 * (d : ℝ) * 3 ^ (d - 1))
          * ((((2 * d - 6 : ℕ) : ℝ) + 1)
            / (((2 * d - 6 : ℕ) : ℝ) * ((h + 1 : ℕ) : ℝ) ^ (2 * d - 6))) := by
          rw [show 3 * d - 6 - d = 2 * d - 6 from by omega]; ring

/-- The u-branch step of the err_cluster per-w derivation: given the (A)-pointwise bound `hApt`
(`A u ≤ (ℓu+1)³/((|x-u|+1)^d(|w-u|+1)^d)`, i.e. `τ(x,u)·τ(u,w)·(1+l_u) ≤ (1+l_u)³|x-u|^{-d}|u-w|^{-d}`),
the branch-point sum is bounded by the two region bounds `perW_Rw` + `perW_Rx`. Partitions `u` by
`|u-w| ≤ |x-u|`. -/
theorem perW_branch_step {d : ℕ} (hd : 7 ≤ d) (x w : Fin d → ℤ) (ℓ : (Fin d → ℤ) → ℕ) {r : ℕ}
    (hr : 1 ≤ r) {h : ℕ} (hh : 1 ≤ h) (hxw : h ≤ linfDist x w)
    (hℓ : ∀ u, ℓ u ≤ 1 + min (linfDist x u) (linfDist u w)) (c : Fin d → ℤ) (K : ℕ)
    (A : (Fin d → ℤ) → ℝ)
    (hApt : ∀ u, A u ≤ ((ℓ u + 1 : ℕ) : ℝ) ^ 3
      / (((linfDist x u + 1 : ℕ) : ℝ) ^ d * ((linfDist w u + 1 : ℕ) : ℝ) ^ d))
    (Cc : ℝ) (hCc : 0 ≤ Cc) :
    ∑ u ∈ linfBall c (K : ℤ),
        A u * (Cc / (max (r : ℝ) ((linfDist u w + 1 : ℕ) : ℝ)) ^ (d - 3))
      ≤ Cc * ((8 * 2 ^ d / ((h : ℝ) + 1) ^ d)
            * (2 * (d : ℝ) * 3 ^ (d - 1)
              * ((((d - 6 : ℕ) : ℝ) + 1) / (((d - 6 : ℕ) : ℝ) * (r : ℝ) ^ (d - 6)))))
        + Cc * (2 ^ (2 * d) * (2 * (d : ℝ) * 3 ^ (d - 1))
              * (((h : ℝ) + 1) ^ 3 / ((h : ℝ) + 1) ^ (2 * d - 3))
            + 8 * (2 * (d : ℝ) * 3 ^ (d - 1))
              * ((((2 * d - 6 : ℕ) : ℝ) + 1)
                / (((2 * d - 6 : ℕ) : ℝ) * ((h + 1 : ℕ) : ℝ) ^ (2 * d - 6)))) := by
  have hterm : ∀ u ∈ linfBall c (K : ℤ),
      A u * (Cc / (max (r : ℝ) ((linfDist u w + 1 : ℕ) : ℝ)) ^ (d - 3))
        ≤ Cc * (((ℓ u + 1 : ℕ) : ℝ) ^ 3
          / (((linfDist x u + 1 : ℕ) : ℝ) ^ d * ((linfDist w u + 1 : ℕ) : ℝ) ^ d
            * (max (r : ℝ) ((linfDist w u + 1 : ℕ) : ℝ)) ^ (d - 3))) := by
    intro u _
    have hcomm : linfDist u w = linfDist w u := linfDist_comm u w
    rw [hcomm]
    have hMpos : (0 : ℝ) < max (r : ℝ) ((linfDist w u + 1 : ℕ) : ℝ) :=
      lt_of_lt_of_le (by exact_mod_cast hr) (le_max_left _ _)
    calc A u * (Cc / (max (r : ℝ) ((linfDist w u + 1 : ℕ) : ℝ)) ^ (d - 3))
        = (Cc / (max (r : ℝ) ((linfDist w u + 1 : ℕ) : ℝ)) ^ (d - 3)) * A u := by ring
      _ ≤ (Cc / (max (r : ℝ) ((linfDist w u + 1 : ℕ) : ℝ)) ^ (d - 3))
            * (((ℓ u + 1 : ℕ) : ℝ) ^ 3
              / (((linfDist x u + 1 : ℕ) : ℝ) ^ d * ((linfDist w u + 1 : ℕ) : ℝ) ^ d)) :=
          mul_le_mul_of_nonneg_left (hApt u) (by positivity)
      _ = Cc * (((ℓ u + 1 : ℕ) : ℝ) ^ 3
          / (((linfDist x u + 1 : ℕ) : ℝ) ^ d * ((linfDist w u + 1 : ℕ) : ℝ) ^ d
            * (max (r : ℝ) ((linfDist w u + 1 : ℕ) : ℝ)) ^ (d - 3))) := by ring
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.mul_sum,
      ← Finset.sum_filter_add_sum_filter_not (linfBall c (K : ℤ))
        (fun u => linfDist u w ≤ linfDist x u), mul_add]
  apply add_le_add
  · exact mul_le_mul_of_nonneg_left (perW_Rw hd x w ℓ hr hh hxw hℓ c K) hCc
  · have hfilter : ((linfBall c (K : ℤ)).filter (fun u => ¬ linfDist u w ≤ linfDist x u))
        = (linfBall c (K : ℤ)).filter (fun u => linfDist x u < linfDist u w) := by
      apply Finset.filter_congr
      intro u _; simp only [Nat.not_le]
    rw [hfilter]
    exact mul_le_mul_of_nonneg_left (perW_Rx hd x w ℓ hr hh hxw hℓ c K) hCc

/-- Full per-`w` bound of `lem.err_cluster` from the raw cited inputs: given the BK + one-sided
pointwise bound `hBK` and the two-sided (A)-pointwise bound `hApt`, the per-`w` two-point sum
`∑_v P v·max(r,|w-v|)^{2-d}` is `≤` an explicit `B ∼ h^{-d}r^{6-d}`. Chains `perW_conv_step`
(v-sum/convolution) with `perW_branch_step` (u-sum). After this, the only unformalized content is
`hBK` (the BK tree bound) and `hApt` (the (A)-conditional box two-point pointwise bounds). -/
theorem perW_bound {d : ℕ} (hd : 7 ≤ d) (x w : Fin d → ℤ) (ℓ : (Fin d → ℤ) → ℕ) {r : ℕ}
    (hr : 1 ≤ r) {h : ℕ} (hh : 1 ≤ h) (hxw : h ≤ linfDist x w)
    (hℓ : ∀ u, ℓ u ≤ 1 + min (linfDist x u) (linfDist u w)) (c : Fin d → ℤ) (K : ℕ)
    (P A : (Fin d → ℤ) → ℝ) (hA : ∀ u, 0 ≤ A u)
    (hApt : ∀ u, A u ≤ ((ℓ u + 1 : ℕ) : ℝ) ^ 3
      / (((linfDist x u + 1 : ℕ) : ℝ) ^ d * ((linfDist w u + 1 : ℕ) : ℝ) ^ d))
    (hBK : ∀ v ∈ linfBall c (K : ℤ),
      P v ≤ ∑ u ∈ linfBall c (K : ℤ), A u * (1 / ((linfDist u v + 1 : ℕ) : ℝ) ^ (d - 1))) :
    ∑ v ∈ linfBall c (K : ℤ),
        P v * (1 / (max (r : ℝ) ((linfDist w v + 1 : ℕ) : ℝ)) ^ (d - 2))
      ≤ (2 ^ (2 * d) * (2 * (d : ℝ) * 3 ^ (d - 1))
          + (2 ^ (d - 2) * (2 * (d : ℝ) * 3 ^ (d - 1))
            + 2 ^ (d - 3) * (3 ^ (d - 1) * (4 * (d : ℝ) * 3 ^ (d - 1)))))
          * ((8 * 2 ^ d / ((h : ℝ) + 1) ^ d)
            * (2 * (d : ℝ) * 3 ^ (d - 1)
              * ((((d - 6 : ℕ) : ℝ) + 1) / (((d - 6 : ℕ) : ℝ) * (r : ℝ) ^ (d - 6)))))
        + (2 ^ (2 * d) * (2 * (d : ℝ) * 3 ^ (d - 1))
          + (2 ^ (d - 2) * (2 * (d : ℝ) * 3 ^ (d - 1))
            + 2 ^ (d - 3) * (3 ^ (d - 1) * (4 * (d : ℝ) * 3 ^ (d - 1)))))
          * (2 ^ (2 * d) * (2 * (d : ℝ) * 3 ^ (d - 1))
              * (((h : ℝ) + 1) ^ 3 / ((h : ℝ) + 1) ^ (2 * d - 3))
            + 8 * (2 * (d : ℝ) * 3 ^ (d - 1))
              * ((((2 * d - 6 : ℕ) : ℝ) + 1)
                / (((2 * d - 6 : ℕ) : ℝ) * ((h + 1 : ℕ) : ℝ) ^ (2 * d - 6)))) := by
  refine le_trans (perW_conv_step hd w hr c K A hA P hBK) ?_
  exact perW_branch_step hd x w ℓ hr hh hxw hℓ c K A hApt _ (by positivity)

/-- u-near-x region of the err_boundary per-pair branch sum. On `{u : |x-u| ≤ |u-w| ∧ |x-u| ≤ |u-w'|}`,
both `|u-w|,|u-w'| ≥ h/2`; split `|x-u| ≤ h` (near: pull both at h-scale, residual `branch_shell_cubic_sum`
up to h) and `|x-u| > h` (far: `|u-w|,|u-w'| ≥ |x-u| > h`, summand `≤ 8(|x-u|+1)^{3-3d}`, `shell_tail_cutoff`
from h). Both give `≲ (h+1)^{3-2d}`. -/
theorem box_pair_Rx {d : ℕ} (hd : 7 ≤ d) (x w w' : Fin d → ℤ) (ℓ : (Fin d → ℤ) → ℕ)
    {h : ℕ} (hh : 1 ≤ h) (hxw : h ≤ linfDist x w) (hxw' : h ≤ linfDist x w')
    (hℓ : ∀ u, ℓ u ≤ 1 + min (linfDist x u) (min (linfDist u w) (linfDist u w')))
    (c : Fin d → ℤ) (K : ℕ) :
    ∑ u ∈ (linfBall c (K : ℤ)).filter
        (fun u => linfDist x u ≤ linfDist u w ∧ linfDist x u ≤ linfDist u w'),
        ((ℓ u + 1 : ℕ) : ℝ) ^ 3
          / (((linfDist x u + 1 : ℕ) : ℝ) ^ d * ((linfDist u w + 1 : ℕ) : ℝ) ^ d
            * ((linfDist u w' + 1 : ℕ) : ℝ) ^ d)
      ≤ 2 ^ (2 * d + 3) * (2 * (d : ℝ) * 3 ^ (d - 1)) * (((h : ℝ) + 1) ^ 3 / ((h : ℝ) + 1) ^ (2 * d))
        + 8 * (2 * (d : ℝ) * 3 ^ (d - 1))
          * ((((2 * d - 3 : ℕ) : ℝ) + 1)
            / (((2 * d - 3 : ℕ) : ℝ) * ((h + 1 : ℕ) : ℝ) ^ (2 * d - 3))) := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not
        ((linfBall c (K : ℤ)).filter
          (fun u => linfDist x u ≤ linfDist u w ∧ linfDist x u ≤ linfDist u w'))
        (fun u => linfDist x u ≤ h), Finset.filter_filter, Finset.filter_filter]
  apply add_le_add
  · -- NEAR
    have hterm : ∀ u ∈ (linfBall c (K : ℤ)).filter
        (fun u => (linfDist x u ≤ linfDist u w ∧ linfDist x u ≤ linfDist u w') ∧ linfDist x u ≤ h),
        ((ℓ u + 1 : ℕ) : ℝ) ^ 3
          / (((linfDist x u + 1 : ℕ) : ℝ) ^ d * ((linfDist u w + 1 : ℕ) : ℝ) ^ d
            * ((linfDist u w' + 1 : ℕ) : ℝ) ^ d)
        ≤ (2 ^ (2 * d + 3) / ((h : ℝ) + 1) ^ (2 * d))
            * (1 / ((linfDist x u + 1 : ℕ) : ℝ) ^ (d - 3)) := by
      intro u hu
      rw [Finset.mem_filter] at hu
      obtain ⟨_, ⟨hw, hw'⟩, hle⟩ := hu
      have hXpos : (0 : ℝ) < ((linfDist x u + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos _
      have hWpos : (0 : ℝ) < ((linfDist u w + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos _
      have hW'pos : (0 : ℝ) < ((linfDist u w' + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos _
      have h2w : h ≤ 2 * linfDist u w := by
        have htri := linfDist_triangle x u w; omega
      have h2w' : h ≤ 2 * linfDist u w' := by
        have htri := linfDist_triangle x u w'; omega
      have hlx : ((ℓ u + 1 : ℕ) : ℝ) ^ 3 ≤ 8 * ((linfDist x u + 1 : ℕ) : ℝ) ^ 3 := by
        have hln : ℓ u + 1 ≤ 2 * (linfDist x u + 1) := by have := hℓ u; omega
        have : ((ℓ u + 1 : ℕ) : ℝ) ≤ 2 * ((linfDist x u + 1 : ℕ) : ℝ) := by
          calc ((ℓ u + 1 : ℕ) : ℝ) ≤ ((2 * (linfDist x u + 1) : ℕ) : ℝ) := by exact_mod_cast hln
            _ = 2 * ((linfDist x u + 1 : ℕ) : ℝ) := by push_cast; ring
        calc ((ℓ u + 1 : ℕ) : ℝ) ^ 3 ≤ (2 * ((linfDist x u + 1 : ℕ) : ℝ)) ^ 3 :=
              pow_le_pow_left₀ (by positivity) this 3
          _ = 8 * ((linfDist x u + 1 : ℕ) : ℝ) ^ 3 := by ring
      have hwpow : ((h : ℝ) + 1) ^ d ≤ 2 ^ d * ((linfDist u w + 1 : ℕ) : ℝ) ^ d := by
        have hc : ((h : ℝ) + 1) ≤ 2 * ((linfDist u w + 1 : ℕ) : ℝ) := by
          have : h + 1 ≤ 2 * (linfDist u w + 1) := by omega
          calc ((h : ℝ) + 1) = ((h + 1 : ℕ) : ℝ) := by push_cast; ring
            _ ≤ ((2 * (linfDist u w + 1) : ℕ) : ℝ) := by exact_mod_cast this
            _ = 2 * ((linfDist u w + 1 : ℕ) : ℝ) := by push_cast; ring
        calc ((h : ℝ) + 1) ^ d ≤ (2 * ((linfDist u w + 1 : ℕ) : ℝ)) ^ d :=
              pow_le_pow_left₀ (by positivity) hc _
          _ = 2 ^ d * ((linfDist u w + 1 : ℕ) : ℝ) ^ d := by rw [mul_pow]
      have hw'pow : ((h : ℝ) + 1) ^ d ≤ 2 ^ d * ((linfDist u w' + 1 : ℕ) : ℝ) ^ d := by
        have hc : ((h : ℝ) + 1) ≤ 2 * ((linfDist u w' + 1 : ℕ) : ℝ) := by
          have : h + 1 ≤ 2 * (linfDist u w' + 1) := by omega
          calc ((h : ℝ) + 1) = ((h + 1 : ℕ) : ℝ) := by push_cast; ring
            _ ≤ ((2 * (linfDist u w' + 1) : ℕ) : ℝ) := by exact_mod_cast this
            _ = 2 * ((linfDist u w' + 1 : ℕ) : ℝ) := by push_cast; ring
        calc ((h : ℝ) + 1) ^ d ≤ (2 * ((linfDist u w' + 1 : ℕ) : ℝ)) ^ d :=
              pow_le_pow_left₀ (by positivity) hc _
          _ = 2 ^ d * ((linfDist u w' + 1 : ℕ) : ℝ) ^ d := by rw [mul_pow]
      rw [div_mul_div_comm, mul_one, div_le_div_iff₀ (by positivity) (by positivity),
          show ((linfDist x u + 1 : ℕ) : ℝ) ^ d
              = ((linfDist x u + 1 : ℕ) : ℝ) ^ 3 * ((linfDist x u + 1 : ℕ) : ℝ) ^ (d - 3)
            from by rw [← pow_add]; congr 1; omega,
          show ((h : ℝ) + 1) ^ (2 * d) = (((h : ℝ) + 1) ^ d * ((h : ℝ) + 1) ^ d) * 1
            from by rw [mul_one, ← pow_add]; congr 1; omega]
      have hprod : ((ℓ u + 1 : ℕ) : ℝ) ^ 3 * (((h : ℝ) + 1) ^ d * ((h : ℝ) + 1) ^ d)
          ≤ 2 ^ (2 * d + 3) * (((linfDist x u + 1 : ℕ) : ℝ) ^ 3 * ((linfDist u w + 1 : ℕ) : ℝ) ^ d
              * ((linfDist u w' + 1 : ℕ) : ℝ) ^ d) := by
        have e1 := mul_le_mul hlx hwpow (by positivity) (by positivity)
        have e2 := mul_le_mul e1 hw'pow (by positivity) (by positivity)
        calc ((ℓ u + 1 : ℕ) : ℝ) ^ 3 * (((h : ℝ) + 1) ^ d * ((h : ℝ) + 1) ^ d)
            = ((ℓ u + 1 : ℕ) : ℝ) ^ 3 * ((h : ℝ) + 1) ^ d * ((h : ℝ) + 1) ^ d := by ring
          _ ≤ 8 * ((linfDist x u + 1 : ℕ) : ℝ) ^ 3 * (2 ^ d * ((linfDist u w + 1 : ℕ) : ℝ) ^ d)
                * (2 ^ d * ((linfDist u w' + 1 : ℕ) : ℝ) ^ d) := e2
          _ = (8 * 2 ^ d * 2 ^ d) * (((linfDist x u + 1 : ℕ) : ℝ) ^ 3
                * ((linfDist u w + 1 : ℕ) : ℝ) ^ d * ((linfDist u w' + 1 : ℕ) : ℝ) ^ d) := by ring
          _ = 2 ^ (2 * d + 3) * (((linfDist x u + 1 : ℕ) : ℝ) ^ 3 * ((linfDist u w + 1 : ℕ) : ℝ) ^ d
                * ((linfDist u w' + 1 : ℕ) : ℝ) ^ d) := by
              rw [show (8 : ℝ) * 2 ^ d * 2 ^ d = 2 ^ (2 * d + 3) from by
                rw [show (8 : ℝ) = 2 ^ 3 from by norm_num, ← pow_add, ← pow_add]; congr 1; omega]
      nlinarith [mul_le_mul_of_nonneg_right hprod (pow_nonneg hXpos.le (d - 3)),
        pow_pos hXpos (d - 3)]
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [← Finset.mul_sum]
    have hsub : (linfBall c (K : ℤ)).filter
        (fun u => (linfDist x u ≤ linfDist u w ∧ linfDist x u ≤ linfDist u w') ∧ linfDist x u ≤ h)
        ⊆ linfBall x (h : ℤ) := by
      intro u hu
      rw [Finset.mem_filter] at hu
      rw [mem_linfBall_iff_dist x u (by positivity)]
      simp only [Int.toNat_natCast]; exact hu.2.2
    have hbsc := le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun u _ _ => by positivity))
      (branch_shell_cubic_sum (by omega) x h)
    calc (2 ^ (2 * d + 3) / ((h : ℝ) + 1) ^ (2 * d))
          * ∑ u ∈ (linfBall c (K : ℤ)).filter
              (fun u => (linfDist x u ≤ linfDist u w ∧ linfDist x u ≤ linfDist u w') ∧ linfDist x u ≤ h),
              (1 / ((linfDist x u + 1 : ℕ) : ℝ) ^ (d - 3))
        ≤ (2 ^ (2 * d + 3) / ((h : ℝ) + 1) ^ (2 * d)) * (2 * (d : ℝ) * 3 ^ (d - 1) * ((h : ℝ) + 1) ^ 3) :=
          mul_le_mul_of_nonneg_left hbsc (by positivity)
      _ = 2 ^ (2 * d + 3) * (2 * (d : ℝ) * 3 ^ (d - 1)) * (((h : ℝ) + 1) ^ 3 / ((h : ℝ) + 1) ^ (2 * d)) := by
          ring
  · -- FAR
    have hterm : ∀ u ∈ (linfBall c (K : ℤ)).filter
        (fun u => (linfDist x u ≤ linfDist u w ∧ linfDist x u ≤ linfDist u w') ∧ ¬ linfDist x u ≤ h),
        ((ℓ u + 1 : ℕ) : ℝ) ^ 3
          / (((linfDist x u + 1 : ℕ) : ℝ) ^ d * ((linfDist u w + 1 : ℕ) : ℝ) ^ d
            * ((linfDist u w' + 1 : ℕ) : ℝ) ^ d)
        ≤ 8 * (1 / ((linfDist x u + 1 : ℕ) : ℝ) ^ (3 * d - 3)) := by
      intro u hu
      rw [Finset.mem_filter] at hu
      obtain ⟨_, ⟨hw, hw'⟩, _⟩ := hu
      have hXpos : (0 : ℝ) < ((linfDist x u + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos _
      have hlx : ((ℓ u + 1 : ℕ) : ℝ) ^ 3 ≤ 8 * ((linfDist x u + 1 : ℕ) : ℝ) ^ 3 := by
        have hln : ℓ u + 1 ≤ 2 * (linfDist x u + 1) := by have := hℓ u; omega
        have : ((ℓ u + 1 : ℕ) : ℝ) ≤ 2 * ((linfDist x u + 1 : ℕ) : ℝ) := by
          calc ((ℓ u + 1 : ℕ) : ℝ) ≤ ((2 * (linfDist x u + 1) : ℕ) : ℝ) := by exact_mod_cast hln
            _ = 2 * ((linfDist x u + 1 : ℕ) : ℝ) := by push_cast; ring
        calc ((ℓ u + 1 : ℕ) : ℝ) ^ 3 ≤ (2 * ((linfDist x u + 1 : ℕ) : ℝ)) ^ 3 :=
              pow_le_pow_left₀ (by positivity) this 3
          _ = 8 * ((linfDist x u + 1 : ℕ) : ℝ) ^ 3 := by ring
      have hxw'' : ((linfDist x u + 1 : ℕ) : ℝ) ≤ ((linfDist u w + 1 : ℕ) : ℝ) := by
        have : linfDist x u + 1 ≤ linfDist u w + 1 := by omega
        exact_mod_cast this
      have hxw2 : ((linfDist x u + 1 : ℕ) : ℝ) ≤ ((linfDist u w' + 1 : ℕ) : ℝ) := by
        have : linfDist x u + 1 ≤ linfDist u w' + 1 := by omega
        exact_mod_cast this
      have hdenge : ((linfDist x u + 1 : ℕ) : ℝ) ^ (3 * d)
          ≤ ((linfDist x u + 1 : ℕ) : ℝ) ^ d * ((linfDist u w + 1 : ℕ) : ℝ) ^ d
            * ((linfDist u w' + 1 : ℕ) : ℝ) ^ d := by
        rw [show 3 * d = d + d + d from by omega, pow_add, pow_add]
        gcongr
      calc ((ℓ u + 1 : ℕ) : ℝ) ^ 3
            / (((linfDist x u + 1 : ℕ) : ℝ) ^ d * ((linfDist u w + 1 : ℕ) : ℝ) ^ d
              * ((linfDist u w' + 1 : ℕ) : ℝ) ^ d)
          ≤ (8 * ((linfDist x u + 1 : ℕ) : ℝ) ^ 3)
            / (((linfDist x u + 1 : ℕ) : ℝ) ^ d * ((linfDist u w + 1 : ℕ) : ℝ) ^ d
              * ((linfDist u w' + 1 : ℕ) : ℝ) ^ d) := by gcongr
        _ ≤ (8 * ((linfDist x u + 1 : ℕ) : ℝ) ^ 3) / ((linfDist x u + 1 : ℕ) : ℝ) ^ (3 * d) := by
            gcongr
        _ = 8 * (1 / ((linfDist x u + 1 : ℕ) : ℝ) ^ (3 * d - 3)) := by
            rw [show ((linfDist x u + 1 : ℕ) : ℝ) ^ (3 * d)
                  = ((linfDist x u + 1 : ℕ) : ℝ) ^ 3 * ((linfDist x u + 1 : ℕ) : ℝ) ^ (3 * d - 3)
                from by rw [← pow_add]; congr 1; omega,
                mul_div_assoc, div_mul_eq_div_div, div_self (by positivity)]
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [← Finset.mul_sum]
    have hsub : (linfBall c (K : ℤ)).filter
        (fun u => (linfDist x u ≤ linfDist u w ∧ linfDist x u ≤ linfDist u w') ∧ ¬ linfDist x u ≤ h)
        ⊆ (linfBall x ((linfDist x c + K : ℕ) : ℤ)).filter (fun u => h < linfDist x u) := by
      intro u hu
      rw [Finset.mem_filter] at hu ⊢
      refine ⟨?_, by omega⟩
      have huc : u ∈ linfBall c (K : ℤ) := hu.1
      rw [mem_linfBall_iff_dist c u (by positivity)] at huc
      simp only [Int.toNat_natCast] at huc
      rw [mem_linfBall_iff_dist x u (by positivity)]
      simp only [Int.toNat_natCast]
      have := linfDist_triangle x c u
      omega
    have hst := le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun u _ _ => by positivity))
      (shell_tail_cutoff (d := d) (q := 3 * d - 3) (by omega) (by omega) x h
        ((linfDist x c + K : ℕ)))
    calc (8 : ℝ) * ∑ u ∈ (linfBall c (K : ℤ)).filter
            (fun u => (linfDist x u ≤ linfDist u w ∧ linfDist x u ≤ linfDist u w')
              ∧ ¬ linfDist x u ≤ h),
            (1 / ((linfDist x u + 1 : ℕ) : ℝ) ^ (3 * d - 3))
        ≤ 8 * (2 * (d : ℝ) * 3 ^ (d - 1)
            * ((((3 * d - 3 - d : ℕ) : ℝ) + 1)
              / (((3 * d - 3 - d : ℕ) : ℝ) * ((h + 1 : ℕ) : ℝ) ^ (3 * d - 3 - d)))) :=
          mul_le_mul_of_nonneg_left hst (by norm_num)
      _ = 8 * (2 * (d : ℝ) * 3 ^ (d - 1))
          * ((((2 * d - 3 : ℕ) : ℝ) + 1)
            / (((2 * d - 3 : ℕ) : ℝ) * ((h + 1 : ℕ) : ℝ) ^ (2 * d - 3))) := by
          rw [show 3 * d - 3 - d = 2 * d - 3 from by omega]; ring

/-- u-near-w region of the err_boundary per-pair branch sum. On `{u : |u-w| ≤ |x-u| ∧ |u-w| ≤ |u-w'|}`:
`2|x-u| ≥ h` and `2|u-w'| ≥ k` (`k ≤ |w-w'|`). Pull `|x-u|^{-d}` at the h-scale always; split
`|u-w| ≤ k` (near: pull `|u-w'|^{-d}` at the k-scale, residual `branch_shell_cubic_sum` at `w` up to `k`)
and `|u-w| > k` (far: `|u-w'| ≥ |u-w|`, residual `shell_tail_cutoff` q=2d-3 at `w`). Both `≲ h^{-d}k^{3-d}`.
By symmetry (swap `w,w'`) this also bounds the u-near-w' region. -/
theorem box_pair_Rw {d : ℕ} (hd : 7 ≤ d) (x w w' : Fin d → ℤ) (ℓ : (Fin d → ℤ) → ℕ)
    {h k : ℕ} (hh : 1 ≤ h) (hk : 1 ≤ k) (hxw : h ≤ linfDist x w) (hkw : k ≤ linfDist w w')
    (hℓ : ∀ u, ℓ u ≤ 1 + min (linfDist x u) (min (linfDist u w) (linfDist u w')))
    (c : Fin d → ℤ) (K : ℕ) :
    ∑ u ∈ (linfBall c (K : ℤ)).filter
        (fun u => linfDist u w ≤ linfDist x u ∧ linfDist u w ≤ linfDist u w'),
        ((ℓ u + 1 : ℕ) : ℝ) ^ 3
          / (((linfDist x u + 1 : ℕ) : ℝ) ^ d * ((linfDist u w + 1 : ℕ) : ℝ) ^ d
            * ((linfDist u w' + 1 : ℕ) : ℝ) ^ d)
      ≤ (2 ^ (2 * d + 3) / (((h : ℝ) + 1) ^ d * ((k : ℝ) + 1) ^ d))
          * (2 * (d : ℝ) * 3 ^ (d - 1) * ((k : ℝ) + 1) ^ 3)
        + (8 * 2 ^ d / ((h : ℝ) + 1) ^ d)
          * (2 * (d : ℝ) * 3 ^ (d - 1)
            * ((((d - 3 : ℕ) : ℝ) + 1) / (((d - 3 : ℕ) : ℝ) * ((k : ℝ) + 1) ^ (d - 3)))) := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not
        ((linfBall c (K : ℤ)).filter
          (fun u => linfDist u w ≤ linfDist x u ∧ linfDist u w ≤ linfDist u w'))
        (fun u => linfDist u w ≤ k), Finset.filter_filter, Finset.filter_filter]
  apply add_le_add
  · -- NEAR: |u-w| ≤ k
    have hterm : ∀ u ∈ (linfBall c (K : ℤ)).filter
        (fun u => (linfDist u w ≤ linfDist x u ∧ linfDist u w ≤ linfDist u w') ∧ linfDist u w ≤ k),
        ((ℓ u + 1 : ℕ) : ℝ) ^ 3
          / (((linfDist x u + 1 : ℕ) : ℝ) ^ d * ((linfDist u w + 1 : ℕ) : ℝ) ^ d
            * ((linfDist u w' + 1 : ℕ) : ℝ) ^ d)
        ≤ (2 ^ (2 * d + 3) / (((h : ℝ) + 1) ^ d * ((k : ℝ) + 1) ^ d))
            * (1 / ((linfDist w u + 1 : ℕ) : ℝ) ^ (d - 3)) := by
      intro u hu
      rw [Finset.mem_filter] at hu
      obtain ⟨_, ⟨hwx, hww'⟩, _⟩ := hu
      have hcomm : linfDist u w = linfDist w u := linfDist_comm u w
      have hXpos : (0 : ℝ) < ((linfDist x u + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos _
      have hWpos : (0 : ℝ) < ((linfDist u w + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos _
      have hW'pos : (0 : ℝ) < ((linfDist u w' + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos _
      have h2x : h ≤ 2 * linfDist x u := by
        have htri := linfDist_triangle x u w; omega
      have h2w' : k ≤ 2 * linfDist u w' := by
        have htri := linfDist_triangle w u w'
        rw [linfDist_comm w u] at htri; omega
      have hlx : ((ℓ u + 1 : ℕ) : ℝ) ^ 3 ≤ 8 * ((linfDist u w + 1 : ℕ) : ℝ) ^ 3 := by
        have hln : ℓ u + 1 ≤ 2 * (linfDist u w + 1) := by have := hℓ u; omega
        have : ((ℓ u + 1 : ℕ) : ℝ) ≤ 2 * ((linfDist u w + 1 : ℕ) : ℝ) := by
          calc ((ℓ u + 1 : ℕ) : ℝ) ≤ ((2 * (linfDist u w + 1) : ℕ) : ℝ) := by exact_mod_cast hln
            _ = 2 * ((linfDist u w + 1 : ℕ) : ℝ) := by push_cast; ring
        calc ((ℓ u + 1 : ℕ) : ℝ) ^ 3 ≤ (2 * ((linfDist u w + 1 : ℕ) : ℝ)) ^ 3 :=
              pow_le_pow_left₀ (by positivity) this 3
          _ = 8 * ((linfDist u w + 1 : ℕ) : ℝ) ^ 3 := by ring
      have hxpow : ((h : ℝ) + 1) ^ d ≤ 2 ^ d * ((linfDist x u + 1 : ℕ) : ℝ) ^ d := by
        have hc : ((h : ℝ) + 1) ≤ 2 * ((linfDist x u + 1 : ℕ) : ℝ) := by
          have : h + 1 ≤ 2 * (linfDist x u + 1) := by omega
          calc ((h : ℝ) + 1) = ((h + 1 : ℕ) : ℝ) := by push_cast; ring
            _ ≤ ((2 * (linfDist x u + 1) : ℕ) : ℝ) := by exact_mod_cast this
            _ = 2 * ((linfDist x u + 1 : ℕ) : ℝ) := by push_cast; ring
        calc ((h : ℝ) + 1) ^ d ≤ (2 * ((linfDist x u + 1 : ℕ) : ℝ)) ^ d :=
              pow_le_pow_left₀ (by positivity) hc _
          _ = 2 ^ d * ((linfDist x u + 1 : ℕ) : ℝ) ^ d := by rw [mul_pow]
      have hw'pow : ((k : ℝ) + 1) ^ d ≤ 2 ^ d * ((linfDist u w' + 1 : ℕ) : ℝ) ^ d := by
        have hc : ((k : ℝ) + 1) ≤ 2 * ((linfDist u w' + 1 : ℕ) : ℝ) := by
          have : k + 1 ≤ 2 * (linfDist u w' + 1) := by omega
          calc ((k : ℝ) + 1) = ((k + 1 : ℕ) : ℝ) := by push_cast; ring
            _ ≤ ((2 * (linfDist u w' + 1) : ℕ) : ℝ) := by exact_mod_cast this
            _ = 2 * ((linfDist u w' + 1 : ℕ) : ℝ) := by push_cast; ring
        calc ((k : ℝ) + 1) ^ d ≤ (2 * ((linfDist u w' + 1 : ℕ) : ℝ)) ^ d :=
              pow_le_pow_left₀ (by positivity) hc _
          _ = 2 ^ d * ((linfDist u w' + 1 : ℕ) : ℝ) ^ d := by rw [mul_pow]
      rw [hcomm, div_mul_div_comm, mul_one, div_le_div_iff₀ (by positivity) (by positivity),
          show ((linfDist w u + 1 : ℕ) : ℝ) ^ d
              = ((linfDist w u + 1 : ℕ) : ℝ) ^ 3 * ((linfDist w u + 1 : ℕ) : ℝ) ^ (d - 3)
            from by rw [← pow_add]; congr 1; omega,
          show ((h : ℝ) + 1) ^ d * ((k : ℝ) + 1) ^ d
              = (((h : ℝ) + 1) ^ d * ((k : ℝ) + 1) ^ d) * 1 from by rw [mul_one]]
      have hprod : ((ℓ u + 1 : ℕ) : ℝ) ^ 3 * (((h : ℝ) + 1) ^ d * ((k : ℝ) + 1) ^ d)
          ≤ 2 ^ (2 * d + 3) * (((linfDist x u + 1 : ℕ) : ℝ) ^ d * ((linfDist w u + 1 : ℕ) : ℝ) ^ 3
              * ((linfDist u w' + 1 : ℕ) : ℝ) ^ d) := by
        have e1 := mul_le_mul hlx hxpow (by positivity) (by positivity)
        have e2 := mul_le_mul e1 hw'pow (by positivity) (by positivity)
        rw [hcomm] at e2
        calc ((ℓ u + 1 : ℕ) : ℝ) ^ 3 * (((h : ℝ) + 1) ^ d * ((k : ℝ) + 1) ^ d)
            = ((ℓ u + 1 : ℕ) : ℝ) ^ 3 * ((h : ℝ) + 1) ^ d * ((k : ℝ) + 1) ^ d := by ring
          _ ≤ 8 * ((linfDist w u + 1 : ℕ) : ℝ) ^ 3 * (2 ^ d * ((linfDist x u + 1 : ℕ) : ℝ) ^ d)
                * (2 ^ d * ((linfDist u w' + 1 : ℕ) : ℝ) ^ d) := e2
          _ = (8 * 2 ^ d * 2 ^ d) * (((linfDist x u + 1 : ℕ) : ℝ) ^ d
                * ((linfDist w u + 1 : ℕ) : ℝ) ^ 3 * ((linfDist u w' + 1 : ℕ) : ℝ) ^ d) := by ring
          _ = 2 ^ (2 * d + 3) * (((linfDist x u + 1 : ℕ) : ℝ) ^ d
                * ((linfDist w u + 1 : ℕ) : ℝ) ^ 3 * ((linfDist u w' + 1 : ℕ) : ℝ) ^ d) := by
              rw [show (8 : ℝ) * 2 ^ d * 2 ^ d = 2 ^ (2 * d + 3) from by
                rw [show (8 : ℝ) = 2 ^ 3 from by norm_num, ← pow_add, ← pow_add]; congr 1; omega]
      have hWupos : (0 : ℝ) < ((linfDist w u + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos _
      nlinarith [mul_le_mul_of_nonneg_right hprod (pow_nonneg hWupos.le (d - 3)),
        pow_pos hWupos (d - 3), pow_pos hW'pos d]
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [← Finset.mul_sum]
    have hsub : (linfBall c (K : ℤ)).filter
        (fun u => (linfDist u w ≤ linfDist x u ∧ linfDist u w ≤ linfDist u w') ∧ linfDist u w ≤ k)
        ⊆ linfBall w (k : ℤ) := by
      intro u hu
      rw [Finset.mem_filter] at hu
      rw [mem_linfBall_iff_dist w u (by positivity)]
      simp only [Int.toNat_natCast]
      have : linfDist u w ≤ k := hu.2.2
      rw [linfDist_comm w u]; exact this
    have hbsc := le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun u _ _ => by positivity))
      (branch_shell_cubic_sum (by omega) w k)
    exact mul_le_mul_of_nonneg_left hbsc (by positivity)
  · -- FAR: |u-w| > k
    have hterm : ∀ u ∈ (linfBall c (K : ℤ)).filter
        (fun u => (linfDist u w ≤ linfDist x u ∧ linfDist u w ≤ linfDist u w') ∧ ¬ linfDist u w ≤ k),
        ((ℓ u + 1 : ℕ) : ℝ) ^ 3
          / (((linfDist x u + 1 : ℕ) : ℝ) ^ d * ((linfDist u w + 1 : ℕ) : ℝ) ^ d
            * ((linfDist u w' + 1 : ℕ) : ℝ) ^ d)
        ≤ (8 * 2 ^ d / ((h : ℝ) + 1) ^ d)
            * (1 / ((linfDist u w + 1 : ℕ) : ℝ) ^ (2 * d - 3)) := by
      intro u hu
      rw [Finset.mem_filter] at hu
      obtain ⟨_, ⟨hwx, hww'⟩, _⟩ := hu
      have hXpos : (0 : ℝ) < ((linfDist x u + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos _
      have hWpos : (0 : ℝ) < ((linfDist u w + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos _
      have hW'pos : (0 : ℝ) < ((linfDist u w' + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos _
      have h2x : h ≤ 2 * linfDist x u := by
        have htri := linfDist_triangle x u w; omega
      have hlx : ((ℓ u + 1 : ℕ) : ℝ) ^ 3 ≤ 8 * ((linfDist u w + 1 : ℕ) : ℝ) ^ 3 := by
        have hln : ℓ u + 1 ≤ 2 * (linfDist u w + 1) := by have := hℓ u; omega
        have : ((ℓ u + 1 : ℕ) : ℝ) ≤ 2 * ((linfDist u w + 1 : ℕ) : ℝ) := by
          calc ((ℓ u + 1 : ℕ) : ℝ) ≤ ((2 * (linfDist u w + 1) : ℕ) : ℝ) := by exact_mod_cast hln
            _ = 2 * ((linfDist u w + 1 : ℕ) : ℝ) := by push_cast; ring
        calc ((ℓ u + 1 : ℕ) : ℝ) ^ 3 ≤ (2 * ((linfDist u w + 1 : ℕ) : ℝ)) ^ 3 :=
              pow_le_pow_left₀ (by positivity) this 3
          _ = 8 * ((linfDist u w + 1 : ℕ) : ℝ) ^ 3 := by ring
      have hxpow : ((h : ℝ) + 1) ^ d ≤ 2 ^ d * ((linfDist x u + 1 : ℕ) : ℝ) ^ d := by
        have hc : ((h : ℝ) + 1) ≤ 2 * ((linfDist x u + 1 : ℕ) : ℝ) := by
          have : h + 1 ≤ 2 * (linfDist x u + 1) := by omega
          calc ((h : ℝ) + 1) = ((h + 1 : ℕ) : ℝ) := by push_cast; ring
            _ ≤ ((2 * (linfDist x u + 1) : ℕ) : ℝ) := by exact_mod_cast this
            _ = 2 * ((linfDist x u + 1 : ℕ) : ℝ) := by push_cast; ring
        calc ((h : ℝ) + 1) ^ d ≤ (2 * ((linfDist x u + 1 : ℕ) : ℝ)) ^ d :=
              pow_le_pow_left₀ (by positivity) hc _
          _ = 2 ^ d * ((linfDist x u + 1 : ℕ) : ℝ) ^ d := by rw [mul_pow]
      have hww'' : ((linfDist u w + 1 : ℕ) : ℝ) ≤ ((linfDist u w' + 1 : ℕ) : ℝ) := by
        have : linfDist u w + 1 ≤ linfDist u w' + 1 := by omega
        exact_mod_cast this
      rw [div_mul_div_comm, mul_one, div_le_div_iff₀ (by positivity) (by positivity)]
      have hXd : ((h : ℝ) + 1) ^ d ≤ 2 ^ d * ((linfDist x u + 1 : ℕ) : ℝ) ^ d := hxpow
      have hBd : ((linfDist u w + 1 : ℕ) : ℝ) ^ d ≤ ((linfDist u w' + 1 : ℕ) : ℝ) ^ d :=
        pow_le_pow_left₀ (by positivity) hww'' d
      calc ((ℓ u + 1 : ℕ) : ℝ) ^ 3
            * (((h : ℝ) + 1) ^ d * ((linfDist u w + 1 : ℕ) : ℝ) ^ (2 * d - 3))
          = (((ℓ u + 1 : ℕ) : ℝ) ^ 3 * ((h : ℝ) + 1) ^ d)
              * ((linfDist u w + 1 : ℕ) : ℝ) ^ (2 * d - 3) := by ring
        _ ≤ (8 * ((linfDist u w + 1 : ℕ) : ℝ) ^ 3 * (2 ^ d * ((linfDist x u + 1 : ℕ) : ℝ) ^ d))
              * ((linfDist u w + 1 : ℕ) : ℝ) ^ (2 * d - 3) :=
            mul_le_mul_of_nonneg_right (mul_le_mul hlx hXd (by positivity) (by positivity))
              (by positivity)
        _ = 8 * 2 ^ d * ((linfDist x u + 1 : ℕ) : ℝ) ^ d
              * (((linfDist u w + 1 : ℕ) : ℝ) ^ 3 * ((linfDist u w + 1 : ℕ) : ℝ) ^ (2 * d - 3)) := by
            ring
        _ = 8 * 2 ^ d * ((linfDist x u + 1 : ℕ) : ℝ) ^ d
              * (((linfDist u w + 1 : ℕ) : ℝ) ^ d * ((linfDist u w + 1 : ℕ) : ℝ) ^ d) := by
            rw [show ((linfDist u w + 1 : ℕ) : ℝ) ^ 3 * ((linfDist u w + 1 : ℕ) : ℝ) ^ (2 * d - 3)
                  = ((linfDist u w + 1 : ℕ) : ℝ) ^ d * ((linfDist u w + 1 : ℕ) : ℝ) ^ d
                from by rw [← pow_add, ← pow_add]; congr 1; omega]
        _ ≤ 8 * 2 ^ d * ((linfDist x u + 1 : ℕ) : ℝ) ^ d
              * (((linfDist u w + 1 : ℕ) : ℝ) ^ d * ((linfDist u w' + 1 : ℕ) : ℝ) ^ d) := by gcongr
        _ = 8 * 2 ^ d * (((linfDist x u + 1 : ℕ) : ℝ) ^ d * ((linfDist u w + 1 : ℕ) : ℝ) ^ d
              * ((linfDist u w' + 1 : ℕ) : ℝ) ^ d) := by ring
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [← Finset.mul_sum,
        Finset.sum_congr rfl (g := fun u => 1 / ((linfDist w u + 1 : ℕ) : ℝ) ^ (2 * d - 3))
          (fun u _ => by rw [linfDist_comm u w])]
    have hsub : (linfBall c (K : ℤ)).filter
        (fun u => (linfDist u w ≤ linfDist x u ∧ linfDist u w ≤ linfDist u w') ∧ ¬ linfDist u w ≤ k)
        ⊆ (linfBall w ((linfDist w c + K : ℕ) : ℤ)).filter (fun u => k < linfDist w u) := by
      intro u hu
      rw [Finset.mem_filter] at hu ⊢
      refine ⟨?_, by rw [linfDist_comm w u]; have := hu.2.2; omega⟩
      have huc : u ∈ linfBall c (K : ℤ) := hu.1
      rw [mem_linfBall_iff_dist c u (by positivity)] at huc
      simp only [Int.toNat_natCast] at huc
      rw [mem_linfBall_iff_dist w u (by positivity)]
      simp only [Int.toNat_natCast]
      have := linfDist_triangle w c u
      omega
    have hst := le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun u _ _ => by positivity))
      (shell_tail_cutoff (d := d) (q := 2 * d - 3) (by omega) (by omega) w k
        ((linfDist w c + K : ℕ)))
    calc (8 * 2 ^ d / ((h : ℝ) + 1) ^ d)
          * ∑ u ∈ (linfBall c (K : ℤ)).filter
              (fun u => (linfDist u w ≤ linfDist x u ∧ linfDist u w ≤ linfDist u w')
                ∧ ¬ linfDist u w ≤ k),
              (1 / ((linfDist w u + 1 : ℕ) : ℝ) ^ (2 * d - 3))
        ≤ (8 * 2 ^ d / ((h : ℝ) + 1) ^ d)
            * (2 * (d : ℝ) * 3 ^ (d - 1)
              * ((((2 * d - 3 - d : ℕ) : ℝ) + 1)
                / (((2 * d - 3 - d : ℕ) : ℝ) * ((k + 1 : ℕ) : ℝ) ^ (2 * d - 3 - d)))) :=
          mul_le_mul_of_nonneg_left hst (by positivity)
      _ = (8 * 2 ^ d / ((h : ℝ) + 1) ^ d)
          * (2 * (d : ℝ) * 3 ^ (d - 1)
            * ((((d - 3 : ℕ) : ℝ) + 1) / (((d - 3 : ℕ) : ℝ) * ((k : ℝ) + 1) ^ (d - 3)))) := by
          rw [show 2 * d - 3 - d = d - 3 from by omega]
          have : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
          rw [this]

/-- Assembly of the err_boundary per-pair branch sum over the full box. Partition `u` by the
nearest of `x, w, w'`: `Rx` (`|x-u|` smallest) via `box_pair_Rx`; `Rw` (`|u-w|` smallest) via
`box_pair_Rw`; `Rw'` (`|u-w'|` smallest) via `box_pair_Rw` with `w,w'` swapped. The three filters
are made disjoint (`P1`, then `¬P1 ∧ P2'`, `¬P1 ∧ ¬P2'`) and each is a subset of the corresponding
region filter, so the full sum is `≤` the sum of the three region bounds. -/
theorem box_pair_branch_sum {d : ℕ} (hd : 7 ≤ d) (x w w' : Fin d → ℤ) (ℓ : (Fin d → ℤ) → ℕ)
    {h k : ℕ} (hh : 1 ≤ h) (hk : 1 ≤ k) (hxw : h ≤ linfDist x w) (hxw' : h ≤ linfDist x w')
    (hkw : k ≤ linfDist w w')
    (hℓ : ∀ u, ℓ u ≤ 1 + min (linfDist x u) (min (linfDist u w) (linfDist u w')))
    (c : Fin d → ℤ) (K : ℕ) :
    ∑ u ∈ linfBall c (K : ℤ),
        ((ℓ u + 1 : ℕ) : ℝ) ^ 3
          / (((linfDist x u + 1 : ℕ) : ℝ) ^ d * ((linfDist u w + 1 : ℕ) : ℝ) ^ d
            * ((linfDist u w' + 1 : ℕ) : ℝ) ^ d)
      ≤ (2 ^ (2 * d + 3) * (2 * (d : ℝ) * 3 ^ (d - 1)) * (((h : ℝ) + 1) ^ 3 / ((h : ℝ) + 1) ^ (2 * d))
          + 8 * (2 * (d : ℝ) * 3 ^ (d - 1))
            * ((((2 * d - 3 : ℕ) : ℝ) + 1)
              / (((2 * d - 3 : ℕ) : ℝ) * ((h + 1 : ℕ) : ℝ) ^ (2 * d - 3))))
        + (((2 ^ (2 * d + 3) / (((h : ℝ) + 1) ^ d * ((k : ℝ) + 1) ^ d))
                * (2 * (d : ℝ) * 3 ^ (d - 1) * ((k : ℝ) + 1) ^ 3)
              + (8 * 2 ^ d / ((h : ℝ) + 1) ^ d)
                * (2 * (d : ℝ) * 3 ^ (d - 1)
                  * ((((d - 3 : ℕ) : ℝ) + 1) / (((d - 3 : ℕ) : ℝ) * ((k : ℝ) + 1) ^ (d - 3)))))
          + ((2 ^ (2 * d + 3) / (((h : ℝ) + 1) ^ d * ((k : ℝ) + 1) ^ d))
                * (2 * (d : ℝ) * 3 ^ (d - 1) * ((k : ℝ) + 1) ^ 3)
              + (8 * 2 ^ d / ((h : ℝ) + 1) ^ d)
                * (2 * (d : ℝ) * 3 ^ (d - 1)
                  * ((((d - 3 : ℕ) : ℝ) + 1) / (((d - 3 : ℕ) : ℝ) * ((k : ℝ) + 1) ^ (d - 3)))))) := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not (linfBall c (K : ℤ))
        (fun u => linfDist x u ≤ linfDist u w ∧ linfDist x u ≤ linfDist u w'),
      ← Finset.sum_filter_add_sum_filter_not
        ((linfBall c (K : ℤ)).filter
          (fun u => ¬(linfDist x u ≤ linfDist u w ∧ linfDist x u ≤ linfDist u w')))
        (fun u => linfDist u w ≤ linfDist u w'),
      Finset.filter_filter, Finset.filter_filter]
  refine add_le_add (box_pair_Rx hd x w w' ℓ hh hxw hxw' hℓ c K) (add_le_add ?_ ?_)
  · -- Rw region: {¬P1 ∧ |u-w| ≤ |u-w'|} ⊆ {|u-w| ≤ |x-u| ∧ |u-w| ≤ |u-w'|}
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_)
      (box_pair_Rw hd x w w' ℓ hh hk hxw hkw hℓ c K)
    · intro u hu
      rw [Finset.mem_filter] at hu ⊢
      obtain ⟨hmem, hnp1, hle⟩ := hu
      exact ⟨hmem, by omega, hle⟩
    · intro u _ _; positivity
  · -- Rw' region: {¬P1 ∧ ¬(|u-w| ≤ |u-w'|)} ⊆ {|u-w'| ≤ |x-u| ∧ |u-w'| ≤ |u-w|}
    calc ∑ u ∈ (linfBall c (K : ℤ)).filter
              (fun a => ¬(linfDist x a ≤ linfDist a w ∧ linfDist x a ≤ linfDist a w')
                ∧ ¬ linfDist a w ≤ linfDist a w'),
            ((ℓ u + 1 : ℕ) : ℝ) ^ 3
              / (((linfDist x u + 1 : ℕ) : ℝ) ^ d * ((linfDist u w + 1 : ℕ) : ℝ) ^ d
                * ((linfDist u w' + 1 : ℕ) : ℝ) ^ d)
        = ∑ u ∈ (linfBall c (K : ℤ)).filter
              (fun a => ¬(linfDist x a ≤ linfDist a w ∧ linfDist x a ≤ linfDist a w')
                ∧ ¬ linfDist a w ≤ linfDist a w'),
            ((ℓ u + 1 : ℕ) : ℝ) ^ 3
              / (((linfDist x u + 1 : ℕ) : ℝ) ^ d * ((linfDist u w' + 1 : ℕ) : ℝ) ^ d
                * ((linfDist u w + 1 : ℕ) : ℝ) ^ d) := by
          apply Finset.sum_congr rfl
          intro u _; ring
      _ ≤ ∑ u ∈ (linfBall c (K : ℤ)).filter
              (fun u => linfDist u w' ≤ linfDist x u ∧ linfDist u w' ≤ linfDist u w),
            ((ℓ u + 1 : ℕ) : ℝ) ^ 3
              / (((linfDist x u + 1 : ℕ) : ℝ) ^ d * ((linfDist u w' + 1 : ℕ) : ℝ) ^ d
                * ((linfDist u w + 1 : ℕ) : ℝ) ^ d) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro u hu
            rw [Finset.mem_filter] at hu ⊢
            obtain ⟨hmem, hnp1, hle⟩ := hu
            exact ⟨hmem, by omega, by omega⟩
          · intro u _ _; positivity
      _ ≤ _ := box_pair_Rw hd x w' w ℓ hh hk hxw' (by rw [linfDist_comm w' w]; exact hkw)
              (fun u => by have := hℓ u; omega) c K

end NearCritical.AppendixVariance
