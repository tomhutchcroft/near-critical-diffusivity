module

public import NearCritical.AppendixShellCount

/-! Appendix B: the `F`-pointwise convolution bound `F(u) = ∑_y M(y)^{2-d} τ(u,y) ≲ M(u)^{4-d}`
(`eq.F_pointwise` / `eq.F1_bound`), where `M(v) = max{r,|x-v|}`. This is a lattice CONVOLUTION
of the `r`-floored power law `M(·)^{2-d}` with the two-point `τ(u,·) ≲ (1+|·-u|)^{2-d}` — analytic
given the two-point bound (the paper's assumption (A)); only `τ` itself is probabilistic.

This file (NEW; imports AppendixShellCount read-only, edits nothing) proves the DOMINANT region of
that estimate: the near-`u` region `|y-u| ≤ M(u)/2`, where `M(y) ≳ M(u)` so the `r`-floored factor
is uniformly bounded and pulls out, leaving `∑ (1+|u-y|)^{2-d} ≲ M(u)^2` (the verified
`ball_inv_pow_sum`), giving the `M(u)^{4-d}` main term. Same shape as `bubble_near_region` but with
the `max(r,·)` kernel. -/
@[expose] public section
namespace NearCritical.AppendixVariance
open scoped BigOperators

/-- Dominant (near-`u`) region of the `F`-pointwise convolution: on `S ⊆ ball u K` where the
`r`-floored distance to `x`, `M(y) = max(r, |x-y|_∞+1)`, is uniformly `≥ c` (which holds on
`|y-u| ≤ M(u)/2` with `c = M(u)/2`), the kernel `M(y)^{2-d}·(|y-u|_∞+1)^{2-d}` sums to
`≤ c^{2-d} · 2d·3^{d-1}(K+1)^2`. The `r`-floored `x`-factor is pulled out (uniformly bounded, since
`t ↦ t^{2-d}` is decreasing) and the `u`-sum is `ball_inv_pow_sum`. With `c ∼ M(u)` this is the
`M(u)^{2-d}·M(u)^2 = M(u)^{4-d}` main term of `F(u)`. -/
theorem F_near_region {d : ℕ} (hd : 2 ≤ d) (x u : Fin d → ℤ) (r c K : ℕ) (hc : 1 ≤ c)
    (S : Finset (Fin d → ℤ)) (hS : S ⊆ linfBall u (K : ℤ))
    (hMy : ∀ y ∈ S, (c : ℝ) ≤ max (r : ℝ) ((linfDist x y + 1 : ℕ) : ℝ)) :
    ∑ y ∈ S, (1 / (max (r : ℝ) ((linfDist x y + 1 : ℕ) : ℝ)) ^ (d - 2))
          * (1 / ((linfDist u y + 1 : ℕ) : ℝ) ^ (d - 2))
      ≤ (1 / ((c : ℝ)) ^ (d - 2)) * (2 * (d : ℝ) * 3 ^ (d - 1) * ((K : ℝ) + 1) ^ 2) := by
  have hc0 : (0 : ℝ) < (c : ℝ) := by exact_mod_cast hc
  calc ∑ y ∈ S, (1 / (max (r : ℝ) ((linfDist x y + 1 : ℕ) : ℝ)) ^ (d - 2))
            * (1 / ((linfDist u y + 1 : ℕ) : ℝ) ^ (d - 2))
      ≤ ∑ y ∈ S, (1 / ((c : ℝ)) ^ (d - 2)) * (1 / ((linfDist u y + 1 : ℕ) : ℝ) ^ (d - 2)) := by
        apply Finset.sum_le_sum
        intro y hy
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        apply one_div_le_one_div_of_le (pow_pos hc0 (d - 2))
        exact pow_le_pow_left₀ hc0.le (hMy y hy) (d - 2)
    _ = (1 / ((c : ℝ)) ^ (d - 2)) * ∑ y ∈ S, (1 / ((linfDist u y + 1 : ℕ) : ℝ) ^ (d - 2)) := by
        rw [← Finset.mul_sum]
    _ ≤ (1 / ((c : ℝ)) ^ (d - 2)) * (2 * (d : ℝ) * 3 ^ (d - 1) * ((K : ℝ) + 1) ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact le_trans
          (Finset.sum_le_sum_of_subset_of_nonneg hS (fun y _ _ => by positivity))
          (ball_inv_pow_sum hd u K)

/-- Radial tail bound (the convergent far-region ingredient of the `F`-estimate, region 2): for
`d ≥ 5`, the kernel `1/(|u-y|_∞+1)^{2d-4}` summed over the lattice points with `|u-y|_∞ > T`
decays like `T^{4-d}`:
`∑_{y∈ball u K, T<|u-y|} 1/(|u-y|_∞+1)^{2d-4} ≤ 2d·3^{d-1} / ((d-4)·(T+1)^{d-4})`.
After radial grouping the exponent is `(j+1)^{3-d}`, and the tail from `T` converges via the
verified `powerlaw_tail_le`. -/
theorem ball_inv_pow_tail {d : ℕ} (hd : 5 ≤ d) (u : Fin d → ℤ) (T K : ℕ) :
    ∑ y ∈ linfBall u (K : ℤ),
        (if T < linfDist u y then (1 : ℝ) / ((linfDist u y + 1 : ℕ) : ℝ) ^ (2 * d - 4) else 0)
      ≤ 2 * (d : ℝ) * 3 ^ (d - 1) * (1 / (((d - 4 : ℕ) : ℝ) * ((T + 1 : ℕ) : ℝ) ^ (d - 4))) := by
  refine le_trans (radial_sum_shell_bound (by omega) u K
    (fun j => if T < j then (1 : ℝ) / ((j + 1 : ℕ) : ℝ) ^ (2 * d - 4) else 0)
    (fun j => by split_ifs <;> positivity)) ?_
  have hterm : ∀ j ∈ Finset.range (K + 1),
      2 * (d : ℝ) * 3 ^ (d - 1) * ((j + 1 : ℕ) : ℝ) ^ (d - 1)
          * (if T < j then (1 : ℝ) / ((j + 1 : ℕ) : ℝ) ^ (2 * d - 4) else 0)
      = 2 * (d : ℝ) * 3 ^ (d - 1)
          * (if T < j then (1 : ℝ) / ((j + 1 : ℕ) : ℝ) ^ (d - 3) else 0) := by
    intro j _
    have hpos : (0 : ℝ) < ((j + 1 : ℕ) : ℝ) := by positivity
    have hsplit : ((j + 1 : ℕ) : ℝ) ^ (2 * d - 4)
        = ((j + 1 : ℕ) : ℝ) ^ (d - 1) * ((j + 1 : ℕ) : ℝ) ^ (d - 3) := by
      rw [← pow_add]; congr 1; omega
    split_ifs with h
    · rw [hsplit]; field_simp
    · ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [← Finset.sum_filter]
  have hset : (Finset.range (K + 1)).filter (fun j => T < j) = Finset.Ico (T + 1) (K + 1) := by
    ext j; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega
  rw [hset, Finset.sum_Ico_eq_sum_range]
  refine le_trans (le_of_eq (Finset.sum_congr rfl (fun k _ => ?_)))
    (powerlaw_tail_le (t := d - 4) (by omega) (r := T + 1) (by omega) ((K + 1) - (T + 1)))
  rw [show T + 1 + k + 1 = T + 1 + 1 + k by omega, show d - 3 = (d - 4) + 1 by omega]

/-- Near-`x` sum of the `r`-floored kernel (region-3 ingredient of the `F`-estimate):
`∑_{y∈ball x K} 1/max(r,|x-y|_∞+1)^{d-2} ≤ 2d·3^{d-1}(K+1)^2`. Since `max(r,·) ≥ (·)`, the floored
kernel is `≤` the plain one, so this follows from `ball_inv_pow_sum`. (With `K ∼ k = |x-u|` this is
the `≲ k^2` factor in region 3, where `y` is near `x` and `|y-u| ∼ k`.) -/
theorem ball_maxr_pow_sum {d : ℕ} (hd : 2 ≤ d) (x : Fin d → ℤ) (r K : ℕ) :
    ∑ y ∈ linfBall x (K : ℤ), (1 : ℝ) / (max (r : ℝ) ((linfDist x y + 1 : ℕ) : ℝ)) ^ (d - 2)
      ≤ 2 * (d : ℝ) * 3 ^ (d - 1) * ((K : ℝ) + 1) ^ 2 := by
  refine le_trans (Finset.sum_le_sum (fun y _ => ?_)) (ball_inv_pow_sum hd x K)
  apply one_div_le_one_div_of_le (by positivity)
  exact pow_le_pow_left₀ (by positivity) (le_max_right _ _) (d - 2)

/-- Region 2 of the `F`-estimate (`|x-y| ≥ |y-u|/2`, i.e. `|y-u| ≤ 2|x-y|`, beyond radius `c`):
there `2·M(y) ≥ 2(|x-y|+1) ≥ |y-u|+1`, so `M(y)^{2-d}(|y-u|+1)^{2-d} ≤ 2^{d-2}/(|y-u|+1)^{2d-4}`,
and the tail (`c < |y-u|`) is `ball_inv_pow_tail`. -/
theorem F_far2_region {d : ℕ} (hd : 5 ≤ d) (x u : Fin d → ℤ) (r c K : ℕ)
    (S : Finset (Fin d → ℤ)) (hS : S ⊆ linfBall u (K : ℤ))
    (hreg : ∀ y ∈ S, c < linfDist u y ∧ linfDist u y ≤ 2 * linfDist x y) :
    ∑ y ∈ S, (1 / (max (r : ℝ) ((linfDist x y + 1 : ℕ) : ℝ)) ^ (d - 2))
          * (1 / ((linfDist u y + 1 : ℕ) : ℝ) ^ (d - 2))
      ≤ (2 : ℝ) ^ (d - 2)
          * (2 * (d : ℝ) * 3 ^ (d - 1) * (1 / (((d - 4 : ℕ) : ℝ) * ((c + 1 : ℕ) : ℝ) ^ (d - 4)))) := by
  have key : ∑ y ∈ S, (1 / (max (r : ℝ) ((linfDist x y + 1 : ℕ) : ℝ)) ^ (d - 2))
          * (1 / ((linfDist u y + 1 : ℕ) : ℝ) ^ (d - 2))
      ≤ (2 : ℝ) ^ (d - 2) * ∑ y ∈ linfBall u (K : ℤ),
          (if c < linfDist u y then (1 : ℝ) / ((linfDist u y + 1 : ℕ) : ℝ) ^ (2 * d - 4) else 0) := by
    rw [Finset.mul_sum]
    refine le_trans (Finset.sum_le_sum (fun y hy => ?_))
      (Finset.sum_le_sum_of_subset_of_nonneg hS
        (fun y _ _ => mul_nonneg (by positivity) (by split_ifs <;> positivity)))
    obtain ⟨hcy, hxy⟩ := hreg y hy
    rw [if_pos hcy]
    have hM : ((linfDist u y + 1 : ℕ) : ℝ) / 2 ≤ max (r : ℝ) ((linfDist x y + 1 : ℕ) : ℝ) := by
      have h1 : linfDist u y + 1 ≤ 2 * (linfDist x y + 1) := by omega
      have h1' : ((linfDist u y + 1 : ℕ) : ℝ) ≤ 2 * ((linfDist x y + 1 : ℕ) : ℝ) := by exact_mod_cast h1
      have h2 := le_max_right (r : ℝ) ((linfDist x y + 1 : ℕ) : ℝ)
      linarith
    have hbound : (1 : ℝ) / (max (r : ℝ) ((linfDist x y + 1 : ℕ) : ℝ)) ^ (d - 2)
        ≤ (2 : ℝ) ^ (d - 2) / ((linfDist u y + 1 : ℕ) : ℝ) ^ (d - 2) := by
      refine le_trans (one_div_le_one_div_of_le (by positivity)
        (pow_le_pow_left₀ (by positivity) hM (d - 2))) (le_of_eq ?_)
      rw [div_pow, one_div_div]
    calc (1 / (max (r : ℝ) ((linfDist x y + 1 : ℕ) : ℝ)) ^ (d - 2))
            * (1 / ((linfDist u y + 1 : ℕ) : ℝ) ^ (d - 2))
        ≤ ((2 : ℝ) ^ (d - 2) / ((linfDist u y + 1 : ℕ) : ℝ) ^ (d - 2))
            * (1 / ((linfDist u y + 1 : ℕ) : ℝ) ^ (d - 2)) :=
          mul_le_mul_of_nonneg_right hbound (by positivity)
      _ = (2 : ℝ) ^ (d - 2) * (1 / ((linfDist u y + 1 : ℕ) : ℝ) ^ (2 * d - 4)) := by
          rw [show 2 * d - 4 = (d - 2) + (d - 2) by omega, pow_add]; ring
  exact le_trans key (mul_le_mul_of_nonneg_left (ball_inv_pow_tail hd u c K) (by positivity))

/-- Region 3 of the `F`-estimate (`|x-y| < |y-u|/2`, beyond radius `c`): here `|y-u| > c` lets the
`u`-factor be pulled out (`(|y-u|+1)^{2-d} ≤ (c+1)^{2-d}`), and `∑_{y∈S} M(y)^{2-d} ≤
ball_maxr_pow_sum` over the `x`-ball `S ⊆ ball x K'`. (In the assembly `K' = |x-u|` and `c ∼ M(u)/2`.) -/
theorem F_far3_region {d : ℕ} (hd : 2 ≤ d) (x u : Fin d → ℤ) (r c K' : ℕ) (hc : 1 ≤ c)
    (S : Finset (Fin d → ℤ)) (hSx : S ⊆ linfBall x (K' : ℤ))
    (hreg : ∀ y ∈ S, c < linfDist u y) :
    ∑ y ∈ S, (1 / (max (r : ℝ) ((linfDist x y + 1 : ℕ) : ℝ)) ^ (d - 2))
          * (1 / ((linfDist u y + 1 : ℕ) : ℝ) ^ (d - 2))
      ≤ (1 / ((c + 1 : ℕ) : ℝ) ^ (d - 2)) * (2 * (d : ℝ) * 3 ^ (d - 1) * ((K' : ℝ) + 1) ^ 2) := by
  calc ∑ y ∈ S, (1 / (max (r : ℝ) ((linfDist x y + 1 : ℕ) : ℝ)) ^ (d - 2))
            * (1 / ((linfDist u y + 1 : ℕ) : ℝ) ^ (d - 2))
      ≤ ∑ y ∈ S, (1 / (max (r : ℝ) ((linfDist x y + 1 : ℕ) : ℝ)) ^ (d - 2))
            * (1 / ((c + 1 : ℕ) : ℝ) ^ (d - 2)) := by
        apply Finset.sum_le_sum
        intro y hy
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply one_div_le_one_div_of_le (by positivity)
        have : c + 1 ≤ linfDist u y + 1 := by have := hreg y hy; omega
        exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast this) (d - 2)
    _ = (1 / ((c + 1 : ℕ) : ℝ) ^ (d - 2))
          * ∑ y ∈ S, (1 / (max (r : ℝ) ((linfDist x y + 1 : ℕ) : ℝ)) ^ (d - 2)) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun y _ => by ring)
    _ ≤ (1 / ((c + 1 : ℕ) : ℝ) ^ (d - 2)) * (2 * (d : ℝ) * 3 ^ (d - 1) * ((K' : ℝ) + 1) ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact le_trans (Finset.sum_le_sum_of_subset_of_nonneg hSx (fun y _ _ => by positivity))
          (ball_maxr_pow_sum hd x r K')

/-- Top-level ball-splitting assembly of the `F`-pointwise estimate: over ANY ℓ∞ ball `linfBall u N`
(the bound is uniform in `N`, so it bounds the full convergent lattice sum `F(u)`), the two-center
kernel `M(y)^{2-d}(|u-y|+1)^{2-d}` with `M(y)=max(r,|x-y|_∞+1)` sums to the sum of the three
per-region bounds. The partition is on `|u-y|_∞ ≶ c` (near/far) and, within the far part, on
`|u-y|_∞ ≤ 2|x-y|_∞` (regions 2 vs 3). The two far regions are discharged UNCONDITIONALLY via the
ℓ∞ triangle inequality (region 3's points satisfy `|x-y|_∞ ≤ |x-u|_∞`, so they lie in `ball x |x-u|`);
the near region needs the domination `c ≤ M(y)` on `|u-y|_∞ ≤ c`, supplied as `hnear` (which holds
with `c = ⌊M(u)/2⌋` by the triangle inequality — see `F_pointwise_bound`). This is the
geometric/combinatorial content of `eq.F_pointwise`; it is still conditional on the two-point bound
`τ(u,y) ≤ (|u-y|_∞+1)^{2-d}` (assumption (A)), which is where `τ` has been replaced by its kernel. -/
theorem F_pointwise_split {d : ℕ} (hd : 5 ≤ d) (x u : Fin d → ℤ) (r c N : ℕ) (hc : 1 ≤ c)
    (hnear : ∀ y : Fin d → ℤ, linfDist u y ≤ c →
      (c : ℝ) ≤ max (r : ℝ) ((linfDist x y + 1 : ℕ) : ℝ)) :
    ∑ y ∈ linfBall u (N : ℤ),
        (1 / (max (r : ℝ) ((linfDist x y + 1 : ℕ) : ℝ)) ^ (d - 2))
          * (1 / ((linfDist u y + 1 : ℕ) : ℝ) ^ (d - 2))
      ≤ (1 / ((c : ℝ)) ^ (d - 2)) * (2 * (d : ℝ) * 3 ^ (d - 1) * ((c : ℝ) + 1) ^ 2)
        + (2 : ℝ) ^ (d - 2)
            * (2 * (d : ℝ) * 3 ^ (d - 1) * (1 / (((d - 4 : ℕ) : ℝ) * ((c + 1 : ℕ) : ℝ) ^ (d - 4))))
        + (1 / ((c + 1 : ℕ) : ℝ) ^ (d - 2))
            * (2 * (d : ℝ) * 3 ^ (d - 1) * ((linfDist x u : ℝ) + 1) ^ 2) := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not (linfBall u (N : ℤ)) (fun y => c < linfDist u y),
      ← Finset.sum_filter_add_sum_filter_not
        ((linfBall u (N : ℤ)).filter (fun y => c < linfDist u y))
        (fun y => linfDist u y ≤ 2 * linfDist x y)]
  have hb2 : ∑ y ∈ ((linfBall u (N : ℤ)).filter (fun y => c < linfDist u y)).filter
        (fun y => linfDist u y ≤ 2 * linfDist x y),
        (1 / (max (r : ℝ) ((linfDist x y + 1 : ℕ) : ℝ)) ^ (d - 2))
          * (1 / ((linfDist u y + 1 : ℕ) : ℝ) ^ (d - 2))
      ≤ (2 : ℝ) ^ (d - 2)
          * (2 * (d : ℝ) * 3 ^ (d - 1) * (1 / (((d - 4 : ℕ) : ℝ) * ((c + 1 : ℕ) : ℝ) ^ (d - 4)))) := by
    refine F_far2_region hd x u r c N _ ?_ ?_
    · exact (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)
    · intro y hy
      simp only [Finset.mem_filter] at hy
      exact ⟨hy.1.2, hy.2⟩
  have hb3 : ∑ y ∈ ((linfBall u (N : ℤ)).filter (fun y => c < linfDist u y)).filter
        (fun y => ¬ linfDist u y ≤ 2 * linfDist x y),
        (1 / (max (r : ℝ) ((linfDist x y + 1 : ℕ) : ℝ)) ^ (d - 2))
          * (1 / ((linfDist u y + 1 : ℕ) : ℝ) ^ (d - 2))
      ≤ (1 / ((c + 1 : ℕ) : ℝ) ^ (d - 2))
          * (2 * (d : ℝ) * 3 ^ (d - 1) * ((linfDist x u : ℝ) + 1) ^ 2) := by
    refine F_far3_region (by omega) x u r c (linfDist x u) hc _ ?_ ?_
    · intro y hy
      simp only [Finset.mem_filter] at hy
      obtain ⟨⟨_, _⟩, hq⟩ := hy
      refine (mem_linfBall_iff_dist x y (k := (linfDist x u : ℤ)) (by positivity)).mpr ?_
      have htri := linfDist_triangle u x y
      have hcomm := linfDist_comm u x
      have hq' := Nat.not_le.mp hq
      omega
    · intro y hy
      simp only [Finset.mem_filter] at hy
      exact hy.1.2
  have hb1 : ∑ y ∈ (linfBall u (N : ℤ)).filter (fun y => ¬ c < linfDist u y),
        (1 / (max (r : ℝ) ((linfDist x y + 1 : ℕ) : ℝ)) ^ (d - 2))
          * (1 / ((linfDist u y + 1 : ℕ) : ℝ) ^ (d - 2))
      ≤ (1 / ((c : ℝ)) ^ (d - 2)) * (2 * (d : ℝ) * 3 ^ (d - 1) * ((c : ℝ) + 1) ^ 2) := by
    refine F_near_region (by omega) x u r c c hc _ ?_ ?_
    · intro y hy
      simp only [Finset.mem_filter] at hy
      refine (mem_linfBall_iff_dist u y (k := (c : ℤ)) (by positivity)).mpr ?_
      have := Nat.not_lt.mp hy.2
      omega
    · intro y hy
      simp only [Finset.mem_filter] at hy
      exact hnear y (Nat.not_lt.mp hy.2)
  exact le_trans (add_le_add (add_le_add hb2 hb3) hb1) (le_of_eq (by ring))

/-- Unconditional form of the `F`-pointwise split: the near-region domination hypothesis `hnear` of
`F_pointwise_split` is discharged from the single numeric hypothesis `2*c ≤ M(u) = max r (|x-u|_∞+1)`
(which holds for `c = ⌊M(u)/2⌋`). The discharge is pure ℓ∞ geometry: for `|u-y|_∞ ≤ c`, the triangle
inequality gives `|x-y|_∞ + 1 ≥ |x-u|_∞ + 1 - c ≥ M(u) - c ≥ c`, and `M(y) = max(r,|x-y|_∞+1) ≥ c`
always when `2c ≤ r`. Thus over any ball `linfBall u N`, with `c` at most half the `u`-scale,
`∑ M(y)^{2-d}(|u-y|_∞+1)^{2-d}` is bounded by the three explicit region terms — the geometric content
of `eq.F_pointwise`, still conditional only on the two-point bound (assumption (A)). -/
theorem F_pointwise_bound {d : ℕ} (hd : 5 ≤ d) (x u : Fin d → ℤ) (r c N : ℕ) (hc : 1 ≤ c)
    (h2c : 2 * c ≤ max r (linfDist x u + 1)) :
    ∑ y ∈ linfBall u (N : ℤ),
        (1 / (max (r : ℝ) ((linfDist x y + 1 : ℕ) : ℝ)) ^ (d - 2))
          * (1 / ((linfDist u y + 1 : ℕ) : ℝ) ^ (d - 2))
      ≤ (1 / ((c : ℝ)) ^ (d - 2)) * (2 * (d : ℝ) * 3 ^ (d - 1) * ((c : ℝ) + 1) ^ 2)
        + (2 : ℝ) ^ (d - 2)
            * (2 * (d : ℝ) * 3 ^ (d - 1) * (1 / (((d - 4 : ℕ) : ℝ) * ((c + 1 : ℕ) : ℝ) ^ (d - 4))))
        + (1 / ((c + 1 : ℕ) : ℝ) ^ (d - 2))
            * (2 * (d : ℝ) * 3 ^ (d - 1) * ((linfDist x u : ℝ) + 1) ^ 2) := by
  refine F_pointwise_split hd x u r c N hc ?_
  intro y hdu
  have htri := linfDist_triangle x y u
  have hcomm := linfDist_comm y u
  rw [hcomm] at htri
  have hnat : c ≤ max r (linfDist x y + 1) := by
    rcases le_total r (linfDist x u + 1) with hMu | hMu
    · rw [Nat.max_eq_right hMu] at h2c
      refine le_trans ?_ (le_max_right r (linfDist x y + 1))
      omega
    · rw [Nat.max_eq_left hMu] at h2c
      refine le_trans ?_ (le_max_left r (linfDist x y + 1))
      omega
  calc (c : ℝ) ≤ ((max r (linfDist x y + 1) : ℕ) : ℝ) := by exact_mod_cast hnat
    _ = max (r : ℝ) ((linfDist x y + 1 : ℕ) : ℝ) := by rw [Nat.cast_max]

/-- Normalization of the three region terms to a single `M(u)^{4-d}` bound. With `c = ⌊M(u)/2⌋`
(so `2c ≤ Mu ≤ 2c+1`) and `k+1 ≤ Mu` (true for `k = |x-u|_∞`, `Mu = M(u)`), each region term is
`O(Mu^{4-d})`: the floor `c` satisfies `Mu ≤ 4c` and `Mu ≤ 2(c+1)`, so `c^{-(d-4)}`, `(c+1)^{-(d-4)}`
and `(k+1)^2(c+1)^{-(d-2)}` all reduce to a constant times `Mu^{-(d-4)}`. The explicit constant is
`(4^{d-3} + 2^{2d-6} + 2^{d-2})·2d·3^{d-1}`. Pure real/nat arithmetic (no geometry). -/
theorem F_region_sum_normalize {d : ℕ} (hd : 5 ≤ d) (c k Mu : ℕ)
    (hc : 1 ≤ c) (h2c : 2 * c ≤ Mu) (hMu1 : Mu ≤ 2 * c + 1) (hk : k + 1 ≤ Mu) :
    (1 / ((c : ℝ)) ^ (d - 2)) * (2 * (d : ℝ) * 3 ^ (d - 1) * ((c : ℝ) + 1) ^ 2)
      + (2 : ℝ) ^ (d - 2)
          * (2 * (d : ℝ) * 3 ^ (d - 1) * (1 / (((d - 4 : ℕ) : ℝ) * ((c + 1 : ℕ) : ℝ) ^ (d - 4))))
      + (1 / ((c + 1 : ℕ) : ℝ) ^ (d - 2))
          * (2 * (d : ℝ) * 3 ^ (d - 1) * ((k : ℝ) + 1) ^ 2)
    ≤ (4 ^ (d - 3) + 2 ^ (2 * d - 6) + 2 ^ (d - 2)) * (2 * (d : ℝ) * 3 ^ (d - 1))
        * (1 / ((Mu : ℝ) ^ (d - 4))) := by
  have hA : (0 : ℝ) ≤ 2 * (d : ℝ) * 3 ^ (d - 1) := by positivity
  have hc1 : (1 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc
  have hcpos : (0 : ℝ) < (c : ℝ) := by linarith
  have hmpos : (0 : ℝ) < (Mu : ℝ) := by
    have : 0 < Mu := by omega
    exact_mod_cast this
  have hcc1pos : (0 : ℝ) < ((c + 1 : ℕ) : ℝ) := by positivity
  have he4 : (1 : ℝ) ≤ ((d - 4 : ℕ) : ℝ) := by
    have : 1 ≤ d - 4 := by omega
    exact_mod_cast this
  have he4pos : (0 : ℝ) < ((d - 4 : ℕ) : ℝ) := by linarith
  have hcpow : (0 : ℝ) < (c : ℝ) ^ (d - 2) := pow_pos hcpos _
  have hmpow : (0 : ℝ) < (Mu : ℝ) ^ (d - 4) := pow_pos hmpos _
  have hcc1pow : (0 : ℝ) < ((c + 1 : ℕ) : ℝ) ^ (d - 2) := pow_pos hcc1pos _
  have hden_pos : (0 : ℝ) < ((d - 4 : ℕ) : ℝ) * ((c + 1 : ℕ) : ℝ) ^ (d - 4) :=
    mul_pos he4pos (pow_pos hcc1pos _)
  have Rm4c : (Mu : ℝ) ≤ 4 * (c : ℝ) := by
    have : Mu ≤ 4 * c := by omega
    exact_mod_cast this
  have Rm2c1 : (Mu : ℝ) ≤ 2 * ((c + 1 : ℕ) : ℝ) := by
    have h : Mu ≤ 2 * (c + 1) := by omega
    calc (Mu : ℝ) ≤ ((2 * (c + 1) : ℕ) : ℝ) := by exact_mod_cast h
      _ = 2 * ((c + 1 : ℕ) : ℝ) := by push_cast; ring
  have hk1m : (k : ℝ) + 1 ≤ (Mu : ℝ) := by
    have h : ((k + 1 : ℕ) : ℝ) ≤ (Mu : ℝ) := by exact_mod_cast hk
    calc (k : ℝ) + 1 = ((k + 1 : ℕ) : ℝ) := by push_cast; ring
      _ ≤ (Mu : ℝ) := h
  have key1 : ((c : ℝ) + 1) ^ 2 * (Mu : ℝ) ^ (d - 4) ≤ 4 ^ (d - 3) * (c : ℝ) ^ (d - 2) := by
    have h1 : ((c : ℝ) + 1) ^ 2 ≤ 4 * (c : ℝ) ^ 2 := by nlinarith [sq_nonneg ((c : ℝ) - 1), hc1]
    have h2 : (Mu : ℝ) ^ (d - 4) ≤ 4 ^ (d - 4) * (c : ℝ) ^ (d - 4) := by
      calc (Mu : ℝ) ^ (d - 4) ≤ (4 * (c : ℝ)) ^ (d - 4) :=
            pow_le_pow_left₀ (le_of_lt hmpos) Rm4c _
        _ = 4 ^ (d - 4) * (c : ℝ) ^ (d - 4) := by rw [mul_pow]
    calc ((c : ℝ) + 1) ^ 2 * (Mu : ℝ) ^ (d - 4)
        ≤ (4 * (c : ℝ) ^ 2) * (4 ^ (d - 4) * (c : ℝ) ^ (d - 4)) :=
          mul_le_mul h1 h2 (by positivity) (by positivity)
      _ = 4 ^ (d - 3) * (c : ℝ) ^ (d - 2) := by
          rw [show (4 : ℝ) ^ (d - 3) = 4 * 4 ^ (d - 4) by rw [← pow_succ']; congr 1; omega,
              show (c : ℝ) ^ (d - 2) = (c : ℝ) ^ 2 * (c : ℝ) ^ (d - 4) by
                rw [← pow_add]; congr 1; omega]
          ring
  have hden : (Mu : ℝ) ^ (d - 4) ≤ 2 ^ (d - 4) * (((d - 4 : ℕ) : ℝ) * ((c + 1 : ℕ) : ℝ) ^ (d - 4)) := by
    calc (Mu : ℝ) ^ (d - 4) ≤ (2 * ((c + 1 : ℕ) : ℝ)) ^ (d - 4) :=
          pow_le_pow_left₀ (le_of_lt hmpos) Rm2c1 _
      _ = 2 ^ (d - 4) * ((c + 1 : ℕ) : ℝ) ^ (d - 4) := by rw [mul_pow]
      _ ≤ 2 ^ (d - 4) * (((d - 4 : ℕ) : ℝ) * ((c + 1 : ℕ) : ℝ) ^ (d - 4)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact le_mul_of_one_le_left (by positivity) he4
  have key3 : ((k : ℝ) + 1) ^ 2 * (Mu : ℝ) ^ (d - 4) ≤ 2 ^ (d - 2) * ((c + 1 : ℕ) : ℝ) ^ (d - 2) := by
    have hA1 : ((k : ℝ) + 1) ^ 2 * (Mu : ℝ) ^ (d - 4) ≤ (Mu : ℝ) ^ (d - 2) := by
      calc ((k : ℝ) + 1) ^ 2 * (Mu : ℝ) ^ (d - 4)
          ≤ (Mu : ℝ) ^ 2 * (Mu : ℝ) ^ (d - 4) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            exact pow_le_pow_left₀ (by positivity) hk1m 2
        _ = (Mu : ℝ) ^ (d - 2) := by rw [← pow_add]; congr 1; omega
    have hA2 : (Mu : ℝ) ^ (d - 2) ≤ 2 ^ (d - 2) * ((c + 1 : ℕ) : ℝ) ^ (d - 2) := by
      calc (Mu : ℝ) ^ (d - 2) ≤ (2 * ((c + 1 : ℕ) : ℝ)) ^ (d - 2) :=
            pow_le_pow_left₀ (le_of_lt hmpos) Rm2c1 _
        _ = 2 ^ (d - 2) * ((c + 1 : ℕ) : ℝ) ^ (d - 2) := by rw [mul_pow]
    exact le_trans hA1 hA2
  have hR1 : (1 / ((c : ℝ)) ^ (d - 2)) * (2 * (d : ℝ) * 3 ^ (d - 1) * ((c : ℝ) + 1) ^ 2)
      ≤ (4 ^ (d - 3) * (2 * (d : ℝ) * 3 ^ (d - 1))) / (Mu : ℝ) ^ (d - 4) := by
    rw [show (1 / ((c : ℝ)) ^ (d - 2)) * (2 * (d : ℝ) * 3 ^ (d - 1) * ((c : ℝ) + 1) ^ 2)
          = ((2 * (d : ℝ) * 3 ^ (d - 1)) * ((c : ℝ) + 1) ^ 2) / (c : ℝ) ^ (d - 2) by ring,
        div_le_div_iff₀ hcpow hmpow]
    calc ((2 * (d : ℝ) * 3 ^ (d - 1)) * ((c : ℝ) + 1) ^ 2) * (Mu : ℝ) ^ (d - 4)
        = (2 * (d : ℝ) * 3 ^ (d - 1)) * (((c : ℝ) + 1) ^ 2 * (Mu : ℝ) ^ (d - 4)) := by ring
      _ ≤ (2 * (d : ℝ) * 3 ^ (d - 1)) * (4 ^ (d - 3) * (c : ℝ) ^ (d - 2)) :=
          mul_le_mul_of_nonneg_left key1 hA
      _ = (4 ^ (d - 3) * (2 * (d : ℝ) * 3 ^ (d - 1))) * (c : ℝ) ^ (d - 2) := by ring
  have hR2 : (2 : ℝ) ^ (d - 2)
        * (2 * (d : ℝ) * 3 ^ (d - 1) * (1 / (((d - 4 : ℕ) : ℝ) * ((c + 1 : ℕ) : ℝ) ^ (d - 4))))
      ≤ (2 ^ (2 * d - 6) * (2 * (d : ℝ) * 3 ^ (d - 1))) / (Mu : ℝ) ^ (d - 4) := by
    rw [show (2 : ℝ) ^ (d - 2)
            * (2 * (d : ℝ) * 3 ^ (d - 1) * (1 / (((d - 4 : ℕ) : ℝ) * ((c + 1 : ℕ) : ℝ) ^ (d - 4))))
          = (2 ^ (d - 2) * (2 * (d : ℝ) * 3 ^ (d - 1)))
              / (((d - 4 : ℕ) : ℝ) * ((c + 1 : ℕ) : ℝ) ^ (d - 4)) by ring,
        div_le_div_iff₀ hden_pos hmpow]
    calc (2 ^ (d - 2) * (2 * (d : ℝ) * 3 ^ (d - 1))) * (Mu : ℝ) ^ (d - 4)
        ≤ (2 ^ (d - 2) * (2 * (d : ℝ) * 3 ^ (d - 1)))
            * (2 ^ (d - 4) * (((d - 4 : ℕ) : ℝ) * ((c + 1 : ℕ) : ℝ) ^ (d - 4))) :=
          mul_le_mul_of_nonneg_left hden (by positivity)
      _ = (2 ^ (2 * d - 6) * (2 * (d : ℝ) * 3 ^ (d - 1)))
            * (((d - 4 : ℕ) : ℝ) * ((c + 1 : ℕ) : ℝ) ^ (d - 4)) := by
          rw [show (2 : ℝ) ^ (2 * d - 6) = 2 ^ (d - 2) * 2 ^ (d - 4) by rw [← pow_add]; congr 1; omega]
          ring
  have hR3 : (1 / ((c + 1 : ℕ) : ℝ) ^ (d - 2)) * (2 * (d : ℝ) * 3 ^ (d - 1) * ((k : ℝ) + 1) ^ 2)
      ≤ (2 ^ (d - 2) * (2 * (d : ℝ) * 3 ^ (d - 1))) / (Mu : ℝ) ^ (d - 4) := by
    rw [show (1 / ((c + 1 : ℕ) : ℝ) ^ (d - 2)) * (2 * (d : ℝ) * 3 ^ (d - 1) * ((k : ℝ) + 1) ^ 2)
          = ((2 * (d : ℝ) * 3 ^ (d - 1)) * ((k : ℝ) + 1) ^ 2) / ((c + 1 : ℕ) : ℝ) ^ (d - 2) by ring,
        div_le_div_iff₀ hcc1pow hmpow]
    calc ((2 * (d : ℝ) * 3 ^ (d - 1)) * ((k : ℝ) + 1) ^ 2) * (Mu : ℝ) ^ (d - 4)
        = (2 * (d : ℝ) * 3 ^ (d - 1)) * (((k : ℝ) + 1) ^ 2 * (Mu : ℝ) ^ (d - 4)) := by ring
      _ ≤ (2 * (d : ℝ) * 3 ^ (d - 1)) * (2 ^ (d - 2) * ((c + 1 : ℕ) : ℝ) ^ (d - 2)) :=
          mul_le_mul_of_nonneg_left key3 hA
      _ = (2 ^ (d - 2) * (2 * (d : ℝ) * 3 ^ (d - 1))) * ((c + 1 : ℕ) : ℝ) ^ (d - 2) := by ring
  calc (1 / ((c : ℝ)) ^ (d - 2)) * (2 * (d : ℝ) * 3 ^ (d - 1) * ((c : ℝ) + 1) ^ 2)
          + (2 : ℝ) ^ (d - 2)
              * (2 * (d : ℝ) * 3 ^ (d - 1) * (1 / (((d - 4 : ℕ) : ℝ) * ((c + 1 : ℕ) : ℝ) ^ (d - 4))))
          + (1 / ((c + 1 : ℕ) : ℝ) ^ (d - 2)) * (2 * (d : ℝ) * 3 ^ (d - 1) * ((k : ℝ) + 1) ^ 2)
      ≤ (4 ^ (d - 3) * (2 * (d : ℝ) * 3 ^ (d - 1))) / (Mu : ℝ) ^ (d - 4)
          + (2 ^ (2 * d - 6) * (2 * (d : ℝ) * 3 ^ (d - 1))) / (Mu : ℝ) ^ (d - 4)
          + (2 ^ (d - 2) * (2 * (d : ℝ) * 3 ^ (d - 1))) / (Mu : ℝ) ^ (d - 4) :=
        add_le_add (add_le_add hR1 hR2) hR3
    _ = (4 ^ (d - 3) + 2 ^ (2 * d - 6) + 2 ^ (d - 2)) * (2 * (d : ℝ) * 3 ^ (d - 1))
          * (1 / ((Mu : ℝ) ^ (d - 4))) := by ring

/-- Clean `M(u)^{4-d}` form of the `F`-pointwise bound (`eq.F_pointwise`): over any ball `linfBall u N`
(uniformly in `N`), `∑_y M(y)^{2-d}(|u-y|_∞+1)^{2-d} ≤ C_d · M(u)^{4-d}` with `M(u)=max(r,|x-u|_∞+1)`
and the explicit constant `C_d = (4^{d-3}+2^{2d-6}+2^{d-2})·2d·3^{d-1}`. Combines `F_pointwise_bound`
(at `c=⌊M(u)/2⌋`) with `F_region_sum_normalize`. Still conditional only on the two-point bound
`τ(u,y) ≤ (|u-y|_∞+1)^{2-d}` (assumption (A)), under which the kernel is `M(·)^{2-d}τ(u,·)`. -/
theorem F_pointwise_le {d : ℕ} (hd : 5 ≤ d) (x u : Fin d → ℤ) (r N : ℕ)
    (hMu : 2 ≤ max r (linfDist x u + 1)) :
    ∑ y ∈ linfBall u (N : ℤ),
        (1 / (max (r : ℝ) ((linfDist x y + 1 : ℕ) : ℝ)) ^ (d - 2))
          * (1 / ((linfDist u y + 1 : ℕ) : ℝ) ^ (d - 2))
      ≤ (4 ^ (d - 3) + 2 ^ (2 * d - 6) + 2 ^ (d - 2)) * (2 * (d : ℝ) * 3 ^ (d - 1))
          * (1 / ((max r (linfDist x u + 1) : ℕ) : ℝ) ^ (d - 4)) := by
  have hc : 1 ≤ max r (linfDist x u + 1) / 2 := by omega
  have h2c : 2 * (max r (linfDist x u + 1) / 2) ≤ max r (linfDist x u + 1) := by omega
  refine le_trans (F_pointwise_bound hd x u r (max r (linfDist x u + 1) / 2) N hc h2c) ?_
  exact F_region_sum_normalize hd (max r (linfDist x u + 1) / 2) (linfDist x u)
    (max r (linfDist x u + 1)) hc h2c (by omega) (Nat.le_max_right _ _)

/-- Squared `F`-pointwise bound: `F(u)^2 ≤ C_d^2 · M(u)^{8-2d}`, i.e. `F(u)^2 ≤ C_d^2 /
max(r,|x-u|_∞+1)^{2d-8}`. Immediate from `F_pointwise_le` (`0 ≤ F ≤ C_d·M^{4-d}`) by squaring. This is
exactly the `F^2` input shape of `var_term_2` (at `d = e+7`, `2d-8 = 2e+6`), with `C_F = C_d^2`. -/
theorem F_sq_pointwise_le {d : ℕ} (hd : 5 ≤ d) (x u : Fin d → ℤ) (r N : ℕ)
    (hMu : 2 ≤ max r (linfDist x u + 1)) :
    (∑ y ∈ linfBall u (N : ℤ),
        (1 / (max (r : ℝ) ((linfDist x y + 1 : ℕ) : ℝ)) ^ (d - 2))
          * (1 / ((linfDist u y + 1 : ℕ) : ℝ) ^ (d - 2))) ^ 2
      ≤ ((4 ^ (d - 3) + 2 ^ (2 * d - 6) + 2 ^ (d - 2)) * (2 * (d : ℝ) * 3 ^ (d - 1))) ^ 2
          * (1 / ((max r (linfDist x u + 1) : ℕ) : ℝ) ^ (2 * d - 8)) := by
  have hF0 : 0 ≤ ∑ y ∈ linfBall u (N : ℤ),
      (1 / (max (r : ℝ) ((linfDist x y + 1 : ℕ) : ℝ)) ^ (d - 2))
        * (1 / ((linfDist u y + 1 : ℕ) : ℝ) ^ (d - 2)) :=
    Finset.sum_nonneg (fun y _ => by positivity)
  have hle := F_pointwise_le hd x u r N hMu
  calc (∑ y ∈ linfBall u (N : ℤ),
          (1 / (max (r : ℝ) ((linfDist x y + 1 : ℕ) : ℝ)) ^ (d - 2))
            * (1 / ((linfDist u y + 1 : ℕ) : ℝ) ^ (d - 2))) ^ 2
      ≤ ((4 ^ (d - 3) + 2 ^ (2 * d - 6) + 2 ^ (d - 2)) * (2 * (d : ℝ) * 3 ^ (d - 1))
            * (1 / ((max r (linfDist x u + 1) : ℕ) : ℝ) ^ (d - 4))) ^ 2 :=
        pow_le_pow_left₀ hF0 hle 2
    _ = ((4 ^ (d - 3) + 2 ^ (2 * d - 6) + 2 ^ (d - 2)) * (2 * (d : ℝ) * 3 ^ (d - 1))) ^ 2
          * (1 / ((max r (linfDist x u + 1) : ℕ) : ℝ) ^ (2 * d - 8)) := by
        rw [mul_pow, div_pow, one_pow, ← pow_mul, show (d - 4) * 2 = 2 * d - 8 from by omega]

end NearCritical.AppendixVariance
