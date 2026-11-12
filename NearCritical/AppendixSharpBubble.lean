module

public import NearCritical.AppendixShellCount

/-! Sharp lattice bubble (convolution of two power laws), `d = e + 7`:
`∑_{y∈T} (|x-y|+1)^{2-d}(|u-y|+1)^{2-d} ≤ C_bub·(|x-u|+1)^{4-d}`, uniformly over every finite
`T ⊆ ball(u,K)` (the bound does not depend on `K`). This is the "standard bubble estimate" used in
the source's proof of prop.var_term_2, Case 1.

The existing `bubble_bound` has the weaker `|x-u|^{2-d}·K²` form. This lemma removes the
`K`-dependence. With `D = |x-u|_∞`, split `y` into three regions:
* `2|u-y| < D`: here `|x-y| ≥ D/2`, and `ball_inv_pow_sum` over `ball(u,D)` applies;
* `2|u-y| ≥ D`, `2|x-y| < D`: symmetric, over `ball(x,D)`;
* both `≥ D/2`: here `|u-y|+1 ≤ 3(|x-y|+1)`, so the summand is `≤ 3^{d-2}(|u-y|+1)^{4-2d}`, and
  `radial_power_sum_le` applies with floor `R = ⌊D/2⌋+1` and tail `t = d-4`.
Deterministic. -/
@[expose] public section
namespace NearCritical.AppendixVariance
open scoped BigOperators

/-- `1/Q^m ≤ c^m/a^m` when `a ≤ c·Q` (local copy, to keep this file's imports minimal). -/
theorem one_div_pow_le_of_le_mul_aux {a Q c : ℝ} (ha : 0 < a) (hQ : 0 < Q) (hc : 0 ≤ c)
    (h : a ≤ c * Q) (m : ℕ) : 1 / Q ^ m ≤ c ^ m / a ^ m := by
  rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul, ← mul_pow]
  exact pow_le_pow_left₀ ha.le h m

theorem sharp_bubble {e : ℕ} (x u : Fin (e + 7) → ℤ) (K : ℕ)
    (T : Finset (Fin (e + 7) → ℤ)) (hTu : T ⊆ linfBall u (K : ℤ)) :
    ∑ y ∈ T, (1 / ((linfDist x y + 1 : ℕ) : ℝ) ^ (e + 5)) *
        (1 / ((linfDist u y + 1 : ℕ) : ℝ) ^ (e + 5))
      ≤ 2 * ((e + 7 : ℕ) : ℝ) * 3 ^ (e + 6) *
          (2 * 2 ^ (e + 5) + 3 ^ (e + 5) * (((((e + 3 : ℕ) : ℝ) + 1) /
            ((e + 3 : ℕ) : ℝ)) * 2 ^ (e + 3))) /
        ((linfDist x u + 1 : ℕ) : ℝ) ^ (e + 3) := by
  set D := linfDist x u with hDdef
  set B : ℝ := 2 * ((e + 7 : ℕ) : ℝ) * 3 ^ (e + 6) with hB
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  set D1 : ℝ := ((D + 1 : ℕ) : ℝ) with hD1
  have hD1pos : 0 < D1 := by rw [hD1]; positivity
  have hD10 : D1 ≠ 0 := ne_of_gt hD1pos
  have hball := ball_inv_pow_sum (show 2 ≤ e + 7 by omega)
  -- region split
  rw [← Finset.sum_filter_add_sum_filter_not T (fun y => 2 * linfDist u y < D)]
  rw [← Finset.sum_filter_add_sum_filter_not (T.filter (fun y => ¬ 2 * linfDist u y < D))
    (fun y => 2 * linfDist x y < D)]
  -- R1: y near u
  have hR1 : ∑ y ∈ T.filter (fun y => 2 * linfDist u y < D),
      (1 / ((linfDist x y + 1 : ℕ) : ℝ) ^ (e + 5)) * (1 / ((linfDist u y + 1 : ℕ) : ℝ) ^ (e + 5))
      ≤ 2 ^ (e + 5) * B / D1 ^ (e + 3) := by
    have hpt : ∀ y ∈ T.filter (fun y => 2 * linfDist u y < D),
        (1 / ((linfDist x y + 1 : ℕ) : ℝ) ^ (e + 5)) * (1 / ((linfDist u y + 1 : ℕ) : ℝ) ^ (e + 5))
        ≤ 2 ^ (e + 5) / D1 ^ (e + 5) * (1 / ((linfDist u y + 1 : ℕ) : ℝ) ^ (e + 5)) := by
      intro y hy
      rw [Finset.mem_filter] at hy
      have htri := linfDist_triangle x y u
      rw [linfDist_comm y u] at htri
      have hle : D1 ≤ 2 * ((linfDist x y + 1 : ℕ) : ℝ) := by
        rw [hD1]; exact_mod_cast (show D + 1 ≤ 2 * (linfDist x y + 1) by omega)
      exact mul_le_mul_of_nonneg_right
        (one_div_pow_le_of_le_mul_aux hD1pos (by positivity) (by norm_num) hle _) (by positivity)
    have hsub : T.filter (fun y => 2 * linfDist u y < D) ⊆ linfBall u (D : ℤ) := by
      intro y hy
      rw [Finset.mem_filter] at hy
      rw [mem_linfBall_iff_dist u y (by positivity)]
      simp only [Int.toNat_natCast]; omega
    have hb := hball u D
    rw [show e + 7 - 2 = e + 5 by omega, show e + 7 - 1 = e + 6 by omega] at hb
    calc _ ≤ ∑ y ∈ T.filter (fun y => 2 * linfDist u y < D),
          2 ^ (e + 5) / D1 ^ (e + 5) * (1 / ((linfDist u y + 1 : ℕ) : ℝ) ^ (e + 5)) :=
          Finset.sum_le_sum hpt
      _ = 2 ^ (e + 5) / D1 ^ (e + 5) * ∑ y ∈ T.filter (fun y => 2 * linfDist u y < D),
          (1 / ((linfDist u y + 1 : ℕ) : ℝ) ^ (e + 5)) := by rw [Finset.mul_sum]
      _ ≤ 2 ^ (e + 5) / D1 ^ (e + 5) * ∑ y ∈ linfBall u (D : ℤ),
          (1 / ((linfDist u y + 1 : ℕ) : ℝ) ^ (e + 5)) :=
          mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity))
            (by positivity)
      _ ≤ 2 ^ (e + 5) / D1 ^ (e + 5) * (B * D1 ^ 2) := by
          refine mul_le_mul_of_nonneg_left (hb.trans (le_of_eq ?_)) (by positivity)
          rw [hB, hD1]; push_cast; ring
      _ = _ := by field_simp <;> ring
  -- R2: y near x
  have hR2 : ∑ y ∈ (T.filter (fun y => ¬ 2 * linfDist u y < D)).filter
        (fun y => 2 * linfDist x y < D),
      (1 / ((linfDist x y + 1 : ℕ) : ℝ) ^ (e + 5)) * (1 / ((linfDist u y + 1 : ℕ) : ℝ) ^ (e + 5))
      ≤ 2 ^ (e + 5) * B / D1 ^ (e + 3) := by
    have hpt : ∀ y ∈ (T.filter (fun y => ¬ 2 * linfDist u y < D)).filter
          (fun y => 2 * linfDist x y < D),
        (1 / ((linfDist x y + 1 : ℕ) : ℝ) ^ (e + 5)) * (1 / ((linfDist u y + 1 : ℕ) : ℝ) ^ (e + 5))
        ≤ 2 ^ (e + 5) / D1 ^ (e + 5) * (1 / ((linfDist x y + 1 : ℕ) : ℝ) ^ (e + 5)) := by
      intro y hy
      simp only [Finset.mem_filter] at hy
      obtain ⟨⟨_, hu⟩, _⟩ := hy
      have hle : D1 ≤ 2 * ((linfDist u y + 1 : ℕ) : ℝ) := by
        rw [hD1]; exact_mod_cast (show D + 1 ≤ 2 * (linfDist u y + 1) by omega)
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_right
        (one_div_pow_le_of_le_mul_aux hD1pos (by positivity) (by norm_num) hle _) (by positivity)
    have hsub : (T.filter (fun y => ¬ 2 * linfDist u y < D)).filter
        (fun y => 2 * linfDist x y < D) ⊆ linfBall x (D : ℤ) := by
      intro y hy
      simp only [Finset.mem_filter] at hy
      rw [mem_linfBall_iff_dist x y (by positivity)]
      simp only [Int.toNat_natCast]; omega
    have hb := hball x D
    rw [show e + 7 - 2 = e + 5 by omega, show e + 7 - 1 = e + 6 by omega] at hb
    calc _ ≤ ∑ y ∈ (T.filter (fun y => ¬ 2 * linfDist u y < D)).filter
            (fun y => 2 * linfDist x y < D),
          2 ^ (e + 5) / D1 ^ (e + 5) * (1 / ((linfDist x y + 1 : ℕ) : ℝ) ^ (e + 5)) :=
          Finset.sum_le_sum hpt
      _ = 2 ^ (e + 5) / D1 ^ (e + 5) * ∑ y ∈ (T.filter (fun y => ¬ 2 * linfDist u y < D)).filter
            (fun y => 2 * linfDist x y < D),
          (1 / ((linfDist x y + 1 : ℕ) : ℝ) ^ (e + 5)) := by rw [Finset.mul_sum]
      _ ≤ 2 ^ (e + 5) / D1 ^ (e + 5) * ∑ y ∈ linfBall x (D : ℤ),
          (1 / ((linfDist x y + 1 : ℕ) : ℝ) ^ (e + 5)) :=
          mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity))
            (by positivity)
      _ ≤ 2 ^ (e + 5) / D1 ^ (e + 5) * (B * D1 ^ 2) := by
          refine mul_le_mul_of_nonneg_left (hb.trans (le_of_eq ?_)) (by positivity)
          rw [hB, hD1]; push_cast; ring
      _ = _ := by field_simp <;> ring
  -- R3: both far
  have hR3 : ∑ y ∈ (T.filter (fun y => ¬ 2 * linfDist u y < D)).filter
        (fun y => ¬ 2 * linfDist x y < D),
      (1 / ((linfDist x y + 1 : ℕ) : ℝ) ^ (e + 5)) * (1 / ((linfDist u y + 1 : ℕ) : ℝ) ^ (e + 5))
      ≤ 3 ^ (e + 5) * (B * ((((e + 3 : ℕ) : ℝ) + 1) / ((e + 3 : ℕ) : ℝ)) * 2 ^ (e + 3)) /
          D1 ^ (e + 3) := by
    set R : ℕ := D / 2 + 1 with hR
    have hR1 : 1 ≤ R := by omega
    have hpt : ∀ y ∈ (T.filter (fun y => ¬ 2 * linfDist u y < D)).filter
          (fun y => ¬ 2 * linfDist x y < D),
        (1 / ((linfDist x y + 1 : ℕ) : ℝ) ^ (e + 5)) * (1 / ((linfDist u y + 1 : ℕ) : ℝ) ^ (e + 5))
        ≤ 3 ^ (e + 5) * (1 / (max (R : ℝ) ((linfDist u y + 1 : ℕ) : ℝ)) ^ (e + 6 + (e + 3 + 1))) := by
      intro y hy
      simp only [Finset.mem_filter] at hy
      obtain ⟨⟨_, hu⟩, hx'⟩ := hy
      have htri := linfDist_triangle u x y
      rw [linfDist_comm u x] at htri
      have hle : ((linfDist u y + 1 : ℕ) : ℝ) ≤ 3 * ((linfDist x y + 1 : ℕ) : ℝ) := by
        exact_mod_cast (show linfDist u y + 1 ≤ 3 * (linfDist x y + 1) by omega)
      have hmax : max (R : ℝ) ((linfDist u y + 1 : ℕ) : ℝ) = ((linfDist u y + 1 : ℕ) : ℝ) :=
        max_eq_right (by exact_mod_cast (show R ≤ linfDist u y + 1 by omega))
      rw [hmax, show e + 6 + (e + 3 + 1) = (e + 5) + (e + 5) by omega]
      have h1 := one_div_pow_le_of_le_mul_aux (a := ((linfDist u y + 1 : ℕ) : ℝ))
        (Q := ((linfDist x y + 1 : ℕ) : ℝ)) (c := 3) (by positivity) (by positivity)
        (by norm_num) hle (e + 5)
      calc (1 / ((linfDist x y + 1 : ℕ) : ℝ) ^ (e + 5)) *
            (1 / ((linfDist u y + 1 : ℕ) : ℝ) ^ (e + 5))
          ≤ (3 ^ (e + 5) / ((linfDist u y + 1 : ℕ) : ℝ) ^ (e + 5)) *
            (1 / ((linfDist u y + 1 : ℕ) : ℝ) ^ (e + 5)) :=
            mul_le_mul_of_nonneg_right h1 (by positivity)
        _ = _ := by ring
    have hsub : (T.filter (fun y => ¬ 2 * linfDist u y < D)).filter
        (fun y => ¬ 2 * linfDist x y < D) ⊆ linfBall u (K : ℤ) :=
      ((Finset.filter_subset _ _).trans (Finset.filter_subset _ _)).trans hTu
    have hrad := radial_power_sum_le (show 1 ≤ e + 7 by omega) u
      (show 1 ≤ e + 3 by omega) hR1 K
    rw [show e + 7 - 1 = e + 6 by omega] at hrad
    have hRD : D1 ≤ 2 * (R : ℝ) := by
      rw [hD1, hR]; exact_mod_cast (show D + 1 ≤ 2 * (D / 2 + 1) by omega)
    have hRpos : (0 : ℝ) < R := by exact_mod_cast hR1
    have hRinv := one_div_pow_le_of_le_mul_aux hD1pos hRpos (by norm_num) hRD (e + 3)
    have he3 : (0 : ℝ) < ((e + 3 : ℕ) : ℝ) := by positivity
    calc _ ≤ ∑ y ∈ (T.filter (fun y => ¬ 2 * linfDist u y < D)).filter
            (fun y => ¬ 2 * linfDist x y < D),
          3 ^ (e + 5) * (1 / (max (R : ℝ) ((linfDist u y + 1 : ℕ) : ℝ)) ^ (e + 6 + (e + 3 + 1))) :=
          Finset.sum_le_sum hpt
      _ = 3 ^ (e + 5) * ∑ y ∈ (T.filter (fun y => ¬ 2 * linfDist u y < D)).filter
            (fun y => ¬ 2 * linfDist x y < D),
          (1 / (max (R : ℝ) ((linfDist u y + 1 : ℕ) : ℝ)) ^ (e + 6 + (e + 3 + 1))) := by
          rw [Finset.mul_sum]
      _ ≤ 3 ^ (e + 5) * ∑ y ∈ linfBall u (K : ℤ),
          (1 / (max (R : ℝ) ((linfDist u y + 1 : ℕ) : ℝ)) ^ (e + 6 + (e + 3 + 1))) :=
          mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity))
            (by positivity)
      _ ≤ 3 ^ (e + 5) * (B * ((((e + 3 : ℕ) : ℝ) + 1) /
            (((e + 3 : ℕ) : ℝ) * (R : ℝ) ^ (e + 3)))) :=
          mul_le_mul_of_nonneg_left (by rw [hB]; exact hrad) (by positivity)
      _ = 3 ^ (e + 5) * (B * ((((e + 3 : ℕ) : ℝ) + 1) / ((e + 3 : ℕ) : ℝ))) *
            (1 / (R : ℝ) ^ (e + 3)) := by field_simp <;> ring
      _ ≤ 3 ^ (e + 5) * (B * ((((e + 3 : ℕ) : ℝ) + 1) / ((e + 3 : ℕ) : ℝ))) *
            (2 ^ (e + 3) / D1 ^ (e + 3)) :=
          mul_le_mul_of_nonneg_left hRinv (by positivity)
      _ = _ := by ring
  have htot : B *
      (2 * 2 ^ (e + 5) + 3 ^ (e + 5) * (((((e + 3 : ℕ) : ℝ) + 1) /
        ((e + 3 : ℕ) : ℝ)) * 2 ^ (e + 3))) / D1 ^ (e + 3) =
      2 ^ (e + 5) * B / D1 ^ (e + 3) +
        (2 ^ (e + 5) * B / D1 ^ (e + 3) +
          3 ^ (e + 5) * (B * ((((e + 3 : ℕ) : ℝ) + 1) / ((e + 3 : ℕ) : ℝ)) * 2 ^ (e + 3)) /
            D1 ^ (e + 3)) := by
    ring
  rw [htot]
  exact add_le_add hR1 (add_le_add hR2 hR3)

end NearCritical.AppendixVariance
