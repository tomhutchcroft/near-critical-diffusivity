module

public import NearCritical.AppendixVarTerm1Case2

/-! Source prop.var_term_1, Case 1: the `Φ`-estimate `eq.Phi_bound`, the discharge of
`var_term_1`'s outer hypothesis `hphi`, and the fully assembled `var_term_1_full`.

Dimension `d = e + 7`. Write `m = |x-w|_∞`, `p = |w-u|_∞`, `k = |x-u|_∞`,
`M = max(r, k+1)`.

* `phi_bound`: if `f(w) ≤ A·(m+1)/((p+1)^{d-1} max(r,m+1)^{d-4})` on `W ⊆ ball(x,2n)`, then
  `∑_W f ≤ A·C_Φ·M^{6-d}`. The proof uses the source's three regions:
  - `2(m+1) ≤ k+1`: here `p+1 ≥ (k+1)/2`. The shell sum is controlled by monotonicity of
    `t^d/max(r,t)^{d-4}`.
  - `k+1 < 2(m+1) ≤ 4(k+1)`: here `m+1 ≲ M` and `max(r,m+1) ≳ M`, with a flat shell sum
    over `ball(u,3k+2)`.
  - `2(k+1) < m+1`: here `p+1 ≥ (m+1)/2`, then `radial_div_sum_le` with floor
    `M' = max(r,2k+3) ≥ M`.
* `var_term_1_hphi`: discharges `hphi` from these pointwise inputs:
  `n³g(w) ≤ C_g(|x-w|+1)` on `outer` [eq.g_outer with `l_w ≤ |x-w|`],
  `τ(w,u) ≤ C_a(1+l_u)(|w-u|+1)^{1-d}` [lem.box_twopoint_onesided],
  `τ(u,x) ≤ C_b(1+l_u)(|x-u|+1)^{-d}` [lem.box_twopoint_twosided],
  `F ≤ C_F max(r,·+1)^{4-d}` [eq.F_pointwise], and `0 ≤ l_u ≤ |x-u|`.
* `var_term_1_full`: prop.var_term_1 from pointwise inputs only (no `hphi`, no `hcase2`,
  no regime hypothesis).

 -/
@[expose] public section
namespace NearCritical.AppendixVariance
open scoped BigOperators

/-- `1/Q^m ≤ c^m/a^m` when `a ≤ c·Q`. -/
theorem one_div_pow_le_of_le_mul {a Q c : ℝ} (ha : 0 < a) (hQ : 0 < Q) (hc : 0 ≤ c)
    (h : a ≤ c * Q) (m : ℕ) : 1 / Q ^ m ≤ c ^ m / a ^ m := by
  rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul, ← mul_pow]
  exact pow_le_pow_left₀ ha.le h m

/-- Monotonicity of `t^{e+7}/max(r,t)^{e+3}` on `[1, T]`. -/
theorem pow_div_max_mono {e : ℕ} {r t T : ℝ} (hr : 0 ≤ r) (ht : 1 ≤ t) (htT : t ≤ T) :
    t ^ (e + 7) / (max r t) ^ (e + 3) ≤ T ^ (e + 7) / (max r T) ^ (e + 3) := by
  have htpos : 0 < t := by linarith
  have hTpos : 0 < T := by linarith
  have hmt : 0 < max r t := lt_of_lt_of_le htpos (le_max_right _ _)
  have hmT : 0 < max r T := lt_of_lt_of_le hTpos (le_max_right _ _)
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have h4 : t ^ 4 ≤ T ^ 4 := pow_le_pow_left₀ htpos.le htT 4
  rcases le_total r t with hrt | htr
  · rw [max_eq_right hrt, max_eq_right (hrt.trans htT)]
    calc t ^ (e + 7) * T ^ (e + 3) = t ^ 4 * (t ^ (e + 3) * T ^ (e + 3)) := by ring
      _ ≤ T ^ 4 * (t ^ (e + 3) * T ^ (e + 3)) :=
          mul_le_mul_of_nonneg_right h4 (by positivity)
      _ = T ^ (e + 7) * t ^ (e + 3) := by ring
  · rw [max_eq_left htr]
    rcases le_total r T with hrT | hTr
    · rw [max_eq_right hrT]
      have h3 : t ^ (e + 3) ≤ r ^ (e + 3) := pow_le_pow_left₀ htpos.le htr _
      calc t ^ (e + 7) * T ^ (e + 3) = t ^ 4 * t ^ (e + 3) * T ^ (e + 3) := by ring
        _ ≤ T ^ 4 * r ^ (e + 3) * T ^ (e + 3) :=
            mul_le_mul_of_nonneg_right (mul_le_mul h4 h3 (by positivity) (by positivity))
              (by positivity)
        _ = T ^ (e + 7) * r ^ (e + 3) := by ring
    · rw [max_eq_left hTr]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ htpos.le htT _) (by positivity)

/-- Flat shell sum: `∑_{y∈ball(x,K)} 1/(|x-y|+1)^{d-1} ≤ 2d·3^{d-1}(K+1)`, `d = e+7`. -/
theorem ball_flat_sum {e : ℕ} (x : Fin (e + 7) → ℤ) (K : ℕ) :
    ∑ y ∈ linfBall x (K : ℤ), (1 : ℝ) / ((linfDist x y + 1 : ℕ) : ℝ) ^ (e + 6)
      ≤ 2 * ((e + 7 : ℕ) : ℝ) * 3 ^ (e + 6) * ((K : ℝ) + 1) := by
  refine (radial_sum_shell_bound (by omega) x K
    (fun j => (1 : ℝ) / ((j + 1 : ℕ) : ℝ) ^ (e + 6)) (fun j => by positivity)).trans ?_
  have hterm : ∀ j ∈ Finset.range (K + 1),
      2 * ((e + 7 : ℕ) : ℝ) * 3 ^ (e + 7 - 1) * ((j + 1 : ℕ) : ℝ) ^ (e + 7 - 1) *
        ((1 : ℝ) / ((j + 1 : ℕ) : ℝ) ^ (e + 6)) = 2 * ((e + 7 : ℕ) : ℝ) * 3 ^ (e + 6) := by
    intro j _
    rw [show e + 7 - 1 = e + 6 by omega]
    have hpos : (0 : ℝ) < ((j + 1 : ℕ) : ℝ) ^ (e + 6) := by positivity
    field_simp <;> ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  apply le_of_eq; push_cast; ring

/-- The source `Φ`-estimate (eq.Phi_bound), in kernel form with an arbitrary prefactor `A`. -/
theorem phi_bound {e : ℕ} {x u : Fin (e + 7) → ℤ} {n r : ℕ} (hr : 1 ≤ r)
    (W : Finset (Fin (e + 7) → ℤ)) (hW : W ⊆ linfBall x ((2 * n : ℕ) : ℤ))
    (f : (Fin (e + 7) → ℤ) → ℝ) {A : ℝ} (hA : 0 ≤ A) (hf0 : ∀ w ∈ W, 0 ≤ f w)
    (hf : ∀ w ∈ W, f w ≤ A * (((linfDist x w + 1 : ℕ) : ℝ) /
      (((linfDist w u + 1 : ℕ) : ℝ) ^ (e + 6) *
        (max (r : ℝ) ((linfDist x w + 1 : ℕ) : ℝ)) ^ (e + 3)))) :
    ∑ w ∈ W, f w ≤ A * (2 * ((e + 7 : ℕ) : ℝ) * 3 ^ (e + 6) *
      (2 ^ (e + 6) + 3 * 2 ^ (e + 4) +
        2 ^ (e + 6) * ((((e + 1 : ℕ) : ℝ) + 1) / ((e + 1 : ℕ) : ℝ)))) /
      (max (r : ℝ) ((linfDist x u + 1 : ℕ) : ℝ)) ^ (e + 1) := by
  set k := linfDist x u with hkdef
  set B : ℝ := 2 * ((e + 7 : ℕ) : ℝ) * 3 ^ (e + 6) with hB
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  set M : ℝ := max (r : ℝ) ((k + 1 : ℕ) : ℝ) with hM
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hk1 : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ k + 1 by omega)
  have hkM : ((k + 1 : ℕ) : ℝ) ≤ M := le_max_right _ _
  have hrM : (r : ℝ) ≤ M := le_max_left _ _
  have hMpos : 0 < M := by linarith
  have hM0 : M ≠ 0 := ne_of_gt hMpos
  -- split W into regions A (near x), C (far), and B (middle)
  rw [← Finset.sum_filter_add_sum_filter_not W (fun w => 2 * (linfDist x w + 1) ≤ k + 1)]
  rw [← Finset.sum_filter_add_sum_filter_not (W.filter (fun w => ¬ 2 * (linfDist x w + 1) ≤ k + 1))
    (fun w => 2 * (k + 1) < linfDist x w + 1)]
  -- Region A
  have hRA : ∑ w ∈ W.filter (fun w => 2 * (linfDist x w + 1) ≤ k + 1), f w ≤
      A * (2 ^ (e + 6) * B) / M ^ (e + 1) := by
    have hpt : ∀ w ∈ W.filter (fun w => 2 * (linfDist x w + 1) ≤ k + 1), f w ≤
        A * (2 ^ (e + 6) / ((k + 1 : ℕ) : ℝ) ^ (e + 6)) *
          (((linfDist x w + 1 : ℕ) : ℝ) / (max (r : ℝ) ((linfDist x w + 1 : ℕ) : ℝ)) ^ (e + 3)) := by
      intro w hw
      rw [Finset.mem_filter] at hw
      obtain ⟨hwW, hA'⟩ := hw
      have htri := linfDist_triangle x w u
      have hp : k + 1 ≤ 2 * (linfDist w u + 1) := by omega
      have hinv := one_div_pow_le_of_le_mul (a := ((k + 1 : ℕ) : ℝ))
        (Q := ((linfDist w u + 1 : ℕ) : ℝ)) (c := 2) (by positivity) (by positivity)
        (by norm_num) (by exact_mod_cast hp) (e + 6)
      have hmax : 0 < max (r : ℝ) ((linfDist x w + 1 : ℕ) : ℝ) :=
        lt_of_lt_of_le (by positivity) (le_max_right _ _)
      calc f w ≤ _ := hf w hwW
        _ = A * (1 / ((linfDist w u + 1 : ℕ) : ℝ) ^ (e + 6)) *
            (((linfDist x w + 1 : ℕ) : ℝ) / (max (r : ℝ) ((linfDist x w + 1 : ℕ) : ℝ)) ^ (e + 3)) := by
            field_simp <;> ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hinv hA) (by positivity)
    have hsub : W.filter (fun w => 2 * (linfDist x w + 1) ≤ k + 1) ⊆ linfBall x (k : ℤ) := by
      intro w hw
      rw [Finset.mem_filter] at hw
      rw [mem_linfBall_iff_dist x w (by positivity)]
      simp only [Int.toNat_natCast]; omega
    have hshell := radial_sum_shell_bound (show 1 ≤ e + 7 by omega) x k
      (fun j => ((j + 1 : ℕ) : ℝ) / (max (r : ℝ) ((j + 1 : ℕ) : ℝ)) ^ (e + 3))
      (fun j => by positivity)
    have hterm : ∀ j ∈ Finset.range (k + 1),
        2 * ((e + 7 : ℕ) : ℝ) * 3 ^ (e + 7 - 1) * ((j + 1 : ℕ) : ℝ) ^ (e + 7 - 1) *
          (((j + 1 : ℕ) : ℝ) / (max (r : ℝ) ((j + 1 : ℕ) : ℝ)) ^ (e + 3)) ≤
        B * (((k + 1 : ℕ) : ℝ) ^ (e + 7) / M ^ (e + 3)) := by
      intro j hj
      rw [show e + 7 - 1 = e + 6 by omega]
      have hjk : ((j + 1 : ℕ) : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by
        have := Finset.mem_range.mp hj; exact_mod_cast (show j + 1 ≤ k + 1 by omega)
      have hmono := pow_div_max_mono (e := e) (r := (r : ℝ)) (by positivity)
        (show (1 : ℝ) ≤ ((j + 1 : ℕ) : ℝ) by exact_mod_cast (show 1 ≤ j + 1 by omega)) hjk
      calc _ = B * (((j + 1 : ℕ) : ℝ) ^ (e + 7) / (max (r : ℝ) ((j + 1 : ℕ) : ℝ)) ^ (e + 3)) := by
            rw [hB]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hmono hB0
    have hsum : ∑ w ∈ W.filter (fun w => 2 * (linfDist x w + 1) ≤ k + 1),
        ((linfDist x w + 1 : ℕ) : ℝ) / (max (r : ℝ) ((linfDist x w + 1 : ℕ) : ℝ)) ^ (e + 3) ≤
        ((k + 1 : ℕ) : ℝ) * (B * (((k + 1 : ℕ) : ℝ) ^ (e + 7) / M ^ (e + 3))) := by
      calc _ ≤ ∑ w ∈ linfBall x (k : ℤ),
            ((linfDist x w + 1 : ℕ) : ℝ) / (max (r : ℝ) ((linfDist x w + 1 : ℕ) : ℝ)) ^ (e + 3) :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
        _ ≤ _ := hshell
        _ ≤ ∑ j ∈ Finset.range (k + 1), B * (((k + 1 : ℕ) : ℝ) ^ (e + 7) / M ^ (e + 3)) :=
            Finset.sum_le_sum hterm
        _ = _ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hK0 : 0 ≤ A * (2 ^ (e + 6) / ((k + 1 : ℕ) : ℝ) ^ (e + 6)) := by positivity
    have hk2 : ((k + 1 : ℕ) : ℝ) ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ (by positivity) hkM 2
    calc _ ≤ ∑ w ∈ W.filter (fun w => 2 * (linfDist x w + 1) ≤ k + 1),
          A * (2 ^ (e + 6) / ((k + 1 : ℕ) : ℝ) ^ (e + 6)) *
            (((linfDist x w + 1 : ℕ) : ℝ) / (max (r : ℝ) ((linfDist x w + 1 : ℕ) : ℝ)) ^ (e + 3)) :=
          Finset.sum_le_sum hpt
      _ = A * (2 ^ (e + 6) / ((k + 1 : ℕ) : ℝ) ^ (e + 6)) *
          ∑ w ∈ W.filter (fun w => 2 * (linfDist x w + 1) ≤ k + 1),
            ((linfDist x w + 1 : ℕ) : ℝ) / (max (r : ℝ) ((linfDist x w + 1 : ℕ) : ℝ)) ^ (e + 3) := by
          rw [Finset.mul_sum]
      _ ≤ A * (2 ^ (e + 6) / ((k + 1 : ℕ) : ℝ) ^ (e + 6)) *
          (((k + 1 : ℕ) : ℝ) * (B * (((k + 1 : ℕ) : ℝ) ^ (e + 7) / M ^ (e + 3)))) :=
          mul_le_mul_of_nonneg_left hsum hK0
      _ = A * (2 ^ (e + 6) * B) * (((k + 1 : ℕ) : ℝ) ^ 2 / M ^ (e + 3)) := by
          field_simp <;> ring
      _ ≤ A * (2 ^ (e + 6) * B) * (M ^ 2 / M ^ (e + 3)) :=
          mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hk2 (by positivity))
            (mul_nonneg hA (by positivity))
      _ = _ := by field_simp <;> ring
  -- Region C (far: 2(k+1) < m+1)
  have hRC : ∑ w ∈ (W.filter (fun w => ¬ 2 * (linfDist x w + 1) ≤ k + 1)).filter
        (fun w => 2 * (k + 1) < linfDist x w + 1), f w ≤
      A * (2 ^ (e + 6) * (B * ((((e + 1 : ℕ) : ℝ) + 1) / ((e + 1 : ℕ) : ℝ)))) / M ^ (e + 1) := by
    set M' : ℕ := max r (2 * k + 3) with hM'
    have hM'1 : 1 ≤ M' := le_trans hr (le_max_left _ _)
    have hMM' : M ≤ (M' : ℝ) := by
      rw [hM, hM', Nat.cast_max]
      exact max_le_max le_rfl (by exact_mod_cast (show k + 1 ≤ 2 * k + 3 by omega))
    have hpt : ∀ w ∈ (W.filter (fun w => ¬ 2 * (linfDist x w + 1) ≤ k + 1)).filter
          (fun w => 2 * (k + 1) < linfDist x w + 1), f w ≤
        A * 2 ^ (e + 6) * (1 / (((linfDist x w + 1 : ℕ) : ℝ) ^ (e + 5) *
          (max (M' : ℝ) ((linfDist x w + 1 : ℕ) : ℝ)) ^ (e + 3))) := by
      intro w hw
      simp only [Finset.mem_filter] at hw
      obtain ⟨⟨hwW, _⟩, hC⟩ := hw
      have htri := linfDist_triangle x u w
      have hp : linfDist x w + 1 ≤ 2 * (linfDist w u + 1) := by
        rw [linfDist_comm u w] at htri; omega
      set m1 : ℝ := ((linfDist x w + 1 : ℕ) : ℝ) with hm1
      have hm1pos : 0 < m1 := by rw [hm1]; positivity
      have hinv := one_div_pow_le_of_le_mul (a := m1) (Q := ((linfDist w u + 1 : ℕ) : ℝ))
        (c := 2) hm1pos (by positivity) (by norm_num) (by rw [hm1]; exact_mod_cast hp) (e + 6)
      have hmaxle : max (M' : ℝ) m1 ≤ max (r : ℝ) m1 := by
        rw [hM', Nat.cast_max]
        refine max_le (max_le (le_max_left _ _) ?_) (le_max_right _ _)
        refine le_trans ?_ (le_max_right _ _)
        rw [hm1]; exact_mod_cast (show 2 * k + 3 ≤ linfDist x w + 1 by omega)
      have hmaxpos : 0 < max (M' : ℝ) m1 := lt_of_lt_of_le hm1pos (le_max_right _ _)
      have hden : (max (M' : ℝ) m1) ^ (e + 3) ≤ (max (r : ℝ) m1) ^ (e + 3) :=
        pow_le_pow_left₀ hmaxpos.le hmaxle _
      calc f w ≤ _ := hf w hwW
        _ = A * m1 * (1 / ((linfDist w u + 1 : ℕ) : ℝ) ^ (e + 6)) *
            (1 / (max (r : ℝ) m1) ^ (e + 3)) := by rw [hm1]; field_simp <;> ring
        _ ≤ A * m1 * (2 ^ (e + 6) / m1 ^ (e + 6)) * (1 / (max (M' : ℝ) m1) ^ (e + 3)) :=
            mul_le_mul (mul_le_mul_of_nonneg_left hinv (mul_nonneg hA hm1pos.le))
              (one_div_le_one_div_of_le (by positivity) hden) (by positivity)
              (mul_nonneg (mul_nonneg hA hm1pos.le) (by positivity))
        _ = _ := by field_simp <;> ring
    have hsub : (W.filter (fun w => ¬ 2 * (linfDist x w + 1) ≤ k + 1)).filter
        (fun w => 2 * (k + 1) < linfDist x w + 1) ⊆ linfBall x ((2 * n : ℕ) : ℤ) :=
      ((Finset.filter_subset _ _).trans (Finset.filter_subset _ _)).trans hW
    have hrad := radial_div_sum_le (show 1 ≤ e + 7 by omega) x (e + 5) (by omega)
      (show 1 ≤ e + 1 by omega) hM'1 (2 * n)
    rw [show e + 7 - 1 - (e + 5) + (e + 1 + 1) = e + 3 by omega,
      show e + 7 - 1 = e + 6 by omega] at hrad
    have hMt : M ^ (e + 1) ≤ (M' : ℝ) ^ (e + 1) := pow_le_pow_left₀ hMpos.le hMM' _
    have he1 : (0 : ℝ) < ((e + 1 : ℕ) : ℝ) := by positivity
    have hK0 : 0 ≤ A * 2 ^ (e + 6) := mul_nonneg hA (by positivity)
    calc _ ≤ ∑ w ∈ (W.filter (fun w => ¬ 2 * (linfDist x w + 1) ≤ k + 1)).filter
            (fun w => 2 * (k + 1) < linfDist x w + 1),
          A * 2 ^ (e + 6) * (1 / (((linfDist x w + 1 : ℕ) : ℝ) ^ (e + 5) *
            (max (M' : ℝ) ((linfDist x w + 1 : ℕ) : ℝ)) ^ (e + 3))) := Finset.sum_le_sum hpt
      _ = A * 2 ^ (e + 6) * ∑ w ∈ (W.filter (fun w => ¬ 2 * (linfDist x w + 1) ≤ k + 1)).filter
            (fun w => 2 * (k + 1) < linfDist x w + 1),
          (1 / (((linfDist x w + 1 : ℕ) : ℝ) ^ (e + 5) *
            (max (M' : ℝ) ((linfDist x w + 1 : ℕ) : ℝ)) ^ (e + 3))) := by rw [Finset.mul_sum]
      _ ≤ A * 2 ^ (e + 6) * ∑ w ∈ linfBall x ((2 * n : ℕ) : ℤ),
          (1 / (((linfDist x w + 1 : ℕ) : ℝ) ^ (e + 5) *
            (max (M' : ℝ) ((linfDist x w + 1 : ℕ) : ℝ)) ^ (e + 3))) :=
          mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)) hK0
      _ ≤ A * 2 ^ (e + 6) * (B * ((((e + 1 : ℕ) : ℝ) + 1) /
            (((e + 1 : ℕ) : ℝ) * (M' : ℝ) ^ (e + 1)))) :=
          mul_le_mul_of_nonneg_left (by rw [hB]; exact hrad) hK0
      _ = A * (2 ^ (e + 6) * (B * ((((e + 1 : ℕ) : ℝ) + 1) / ((e + 1 : ℕ) : ℝ)))) *
            (1 / (M' : ℝ) ^ (e + 1)) := by field_simp <;> ring
      _ ≤ A * (2 ^ (e + 6) * (B * ((((e + 1 : ℕ) : ℝ) + 1) / ((e + 1 : ℕ) : ℝ)))) *
            (1 / M ^ (e + 1)) :=
          mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le (by positivity) hMt)
            (mul_nonneg hA (by positivity))
      _ = _ := by ring
  -- Region B (middle)
  have hRB : ∑ w ∈ (W.filter (fun w => ¬ 2 * (linfDist x w + 1) ≤ k + 1)).filter
        (fun w => ¬ 2 * (k + 1) < linfDist x w + 1), f w ≤
      A * (3 * 2 ^ (e + 4) * B) / M ^ (e + 1) := by
    have hpt : ∀ w ∈ (W.filter (fun w => ¬ 2 * (linfDist x w + 1) ≤ k + 1)).filter
          (fun w => ¬ 2 * (k + 1) < linfDist x w + 1), f w ≤
        A * (2 * M * (2 ^ (e + 3) / M ^ (e + 3))) *
          (1 / ((linfDist w u + 1 : ℕ) : ℝ) ^ (e + 6)) := by
      intro w hw
      simp only [Finset.mem_filter] at hw
      obtain ⟨⟨hwW, hA'⟩, hC⟩ := hw
      set m1 : ℝ := ((linfDist x w + 1 : ℕ) : ℝ) with hm1
      have hm1pos : 0 < m1 := by rw [hm1]; positivity
      have hm1M : m1 ≤ 2 * M := by
        have : m1 ≤ 2 * ((k + 1 : ℕ) : ℝ) := by
          rw [hm1]; exact_mod_cast (show linfDist x w + 1 ≤ 2 * (k + 1) by omega)
        linarith
      have hMmax : M ≤ 2 * max (r : ℝ) m1 := by
        rw [hM]
        refine max_le ?_ ?_
        · have := le_max_left (r : ℝ) m1; linarith
        · have h1 : ((k + 1 : ℕ) : ℝ) ≤ 2 * m1 := by
            rw [hm1]; exact_mod_cast (show k + 1 ≤ 2 * (linfDist x w + 1) by omega)
          have := le_max_right (r : ℝ) m1; linarith
      have hmaxpos : 0 < max (r : ℝ) m1 := lt_of_lt_of_le hm1pos (le_max_right _ _)
      have hinv := one_div_pow_le_of_le_mul (a := M) (Q := max (r : ℝ) m1) (c := 2)
        hMpos hmaxpos (by norm_num) hMmax (e + 3)
      calc f w ≤ _ := hf w hwW
        _ = A * (m1 * (1 / (max (r : ℝ) m1) ^ (e + 3))) *
            (1 / ((linfDist w u + 1 : ℕ) : ℝ) ^ (e + 6)) := by rw [hm1]; field_simp <;> ring
        _ ≤ A * (2 * M * (2 ^ (e + 3) / M ^ (e + 3))) *
            (1 / ((linfDist w u + 1 : ℕ) : ℝ) ^ (e + 6)) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
              (mul_le_mul hm1M hinv (by positivity) (by positivity)) hA) (by positivity)
    have hsub : (W.filter (fun w => ¬ 2 * (linfDist x w + 1) ≤ k + 1)).filter
        (fun w => ¬ 2 * (k + 1) < linfDist x w + 1) ⊆ linfBall u ((3 * k + 2 : ℕ) : ℤ) := by
      intro w hw
      simp only [Finset.mem_filter] at hw
      obtain ⟨⟨_, _⟩, hC⟩ := hw
      rw [mem_linfBall_iff_dist u w (by positivity)]
      have htri := linfDist_triangle u x w
      rw [linfDist_comm u x] at htri
      simp only [Int.toNat_natCast]; omega
    have hflat := ball_flat_sum u (3 * k + 2)
    have hK0 : 0 ≤ A * (2 * M * (2 ^ (e + 3) / M ^ (e + 3))) := by positivity
    have hk3 : ((3 * k + 2 : ℕ) : ℝ) + 1 ≤ 3 * M := by
      have : ((3 * k + 2 : ℕ) : ℝ) + 1 = 3 * ((k + 1 : ℕ) : ℝ) := by push_cast; ring
      rw [this]; linarith
    have hflat' : ∑ w ∈ linfBall u ((3 * k + 2 : ℕ) : ℤ),
        (1 / ((linfDist u w + 1 : ℕ) : ℝ) ^ (e + 6)) ≤ B * (3 * M) := by
      refine hflat.trans ?_
      rw [hB]
      exact mul_le_mul_of_nonneg_left hk3 (by positivity)
    calc _ ≤ ∑ w ∈ (W.filter (fun w => ¬ 2 * (linfDist x w + 1) ≤ k + 1)).filter
            (fun w => ¬ 2 * (k + 1) < linfDist x w + 1),
          A * (2 * M * (2 ^ (e + 3) / M ^ (e + 3))) *
            (1 / ((linfDist w u + 1 : ℕ) : ℝ) ^ (e + 6)) := Finset.sum_le_sum hpt
      _ = A * (2 * M * (2 ^ (e + 3) / M ^ (e + 3))) *
          ∑ w ∈ (W.filter (fun w => ¬ 2 * (linfDist x w + 1) ≤ k + 1)).filter
            (fun w => ¬ 2 * (k + 1) < linfDist x w + 1),
          (1 / ((linfDist w u + 1 : ℕ) : ℝ) ^ (e + 6)) := by rw [Finset.mul_sum]
      _ ≤ A * (2 * M * (2 ^ (e + 3) / M ^ (e + 3))) *
          ∑ w ∈ linfBall u ((3 * k + 2 : ℕ) : ℤ), (1 / ((linfDist u w + 1 : ℕ) : ℝ) ^ (e + 6)) := by
          refine mul_le_mul_of_nonneg_left ?_ hK0
          refine (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)).trans
            (le_of_eq (Finset.sum_congr rfl (fun w _ => by rw [linfDist_comm w u])))
      _ ≤ A * (2 * M * (2 ^ (e + 3) / M ^ (e + 3))) * (B * (3 * M)) :=
          mul_le_mul_of_nonneg_left hflat' hK0
      _ = _ := by field_simp <;> ring
  have hsplit : A * (B *
      (2 ^ (e + 6) + 3 * 2 ^ (e + 4) +
        2 ^ (e + 6) * ((((e + 1 : ℕ) : ℝ) + 1) / ((e + 1 : ℕ) : ℝ)))) / M ^ (e + 1) =
      A * (2 ^ (e + 6) * B) / M ^ (e + 1) +
      (A * (2 ^ (e + 6) * (B * ((((e + 1 : ℕ) : ℝ) + 1) / ((e + 1 : ℕ) : ℝ)))) / M ^ (e + 1) +
        A * (3 * 2 ^ (e + 4) * B) / M ^ (e + 1)) := by
    ring
  rw [hsplit]
  exact add_le_add hRA (add_le_add hRC hRB)

/-- Pointwise outer coefficient for the first diagram. -/
noncomputable def varTermOnePhiConstant (e : ℕ) (Cg Ca Cb CF : ℝ) : ℝ :=
  Cb * CF * (Cg * Ca * CF) * (2 * ((e + 7 : ℕ) : ℝ) * 3 ^ (e + 6) *
    (2 ^ (e + 6) + 3 * 2 ^ (e + 4) +
      2 ^ (e + 6) * ((((e + 1 : ℕ) : ℝ) + 1) / ((e + 1 : ℕ) : ℝ))))

/-- Discharge of `var_term_1`'s outer hypothesis `hphi` from pointwise inputs. -/
theorem var_term_1_hphi {e : ℕ} (x : Fin (e + 7) → ℤ) {n r : ℕ} (hr : 1 ≤ r)
    (Ann outer : Finset (Fin (e + 7) → ℤ)) (houter_sub : outer ⊆ Ann)
    (hAnn_ball : Ann ⊆ linfBall x ((2 * n : ℕ) : ℤ))
    (g F l : (Fin (e + 7) → ℤ) → ℝ) (tau : (Fin (e + 7) → ℤ) → (Fin (e + 7) → ℤ) → ℝ)
    {Cg Ca Cb CF : ℝ} (hCg : 0 ≤ Cg) (hCa : 0 ≤ Ca) (hCb : 0 ≤ Cb) (hCF : 0 ≤ CF)
    (hg0 : ∀ w ∈ outer, 0 ≤ g w) (hF0 : ∀ u ∈ Ann, 0 ≤ F u)
    (htw0 : ∀ w ∈ outer, ∀ u ∈ Ann, 0 ≤ tau w u) (htx0 : ∀ u ∈ Ann, 0 ≤ tau u x)
    (hl0 : ∀ u ∈ Ann, 0 ≤ l u) (hl : ∀ u ∈ Ann, l u ≤ (linfDist x u : ℝ))
    (hgo : ∀ w ∈ outer, (n : ℝ) ^ 3 * g w ≤ Cg * ((linfDist x w + 1 : ℕ) : ℝ))
    (hF : ∀ u ∈ Ann, F u ≤ CF / (max (r : ℝ) ((linfDist x u + 1 : ℕ) : ℝ)) ^ (e + 3))
    (htwu : ∀ w ∈ outer, ∀ u ∈ Ann,
      tau w u ≤ Ca * (1 + l u) / ((linfDist w u + 1 : ℕ) : ℝ) ^ (e + 6))
    (htx : ∀ u ∈ Ann, tau u x ≤ Cb * (1 + l u) / ((linfDist x u + 1 : ℕ) : ℝ) ^ (e + 7)) :
    ∀ u ∈ Ann,
      (n : ℝ) ^ 3 * (∑ w ∈ outer, g w * tau w u * tau u x * F w * F u)
        ≤ (Cb * CF * (Cg * Ca * CF) * (2 * ((e + 7 : ℕ) : ℝ) * 3 ^ (e + 6) *
            (2 ^ (e + 6) + 3 * 2 ^ (e + 4) +
              2 ^ (e + 6) * ((((e + 1 : ℕ) : ℝ) + 1) / ((e + 1 : ℕ) : ℝ))))) *
          (1 / (((linfDist x u + 1 : ℕ) : ℝ) ^ (e + 7 - 2)
            * (max (r : ℝ) ((linfDist x u + 1 : ℕ) : ℝ)) ^ (2 * (e + 7) - 10))) := by
  intro u hu
  rw [show e + 7 - 2 = e + 5 by omega, show 2 * (e + 7) - 10 = 2 * e + 4 by omega]
  set CΦ : ℝ := 2 * ((e + 7 : ℕ) : ℝ) * 3 ^ (e + 6) *
    (2 ^ (e + 6) + 3 * 2 ^ (e + 4) +
      2 ^ (e + 6) * ((((e + 1 : ℕ) : ℝ) + 1) / ((e + 1 : ℕ) : ℝ))) with hCΦ
  have hCΦ0 : 0 ≤ CΦ := by rw [hCΦ]; positivity
  set k1 : ℝ := ((linfDist x u + 1 : ℕ) : ℝ) with hk1
  have hk1pos : 0 < k1 := by rw [hk1]; positivity
  set M : ℝ := max (r : ℝ) k1 with hM
  have hMpos : 0 < M := lt_of_lt_of_le hk1pos (le_max_right _ _)
  have hl1 : 0 ≤ 1 + l u := by linarith [hl0 u hu]
  have hlk : 1 + l u ≤ k1 := by rw [hk1]; push_cast; linarith [hl u hu]
  have hA0 : 0 ≤ Cg * Ca * CF * (1 + l u) :=
    mul_nonneg (mul_nonneg (mul_nonneg hCg hCa) hCF) hl1
  -- the Φ sum
  have hΦ := phi_bound (n := n) (u := u) hr outer (houter_sub.trans hAnn_ball)
    (fun w => (n : ℝ) ^ 3 * g w * tau w u * F w) hA0
    (fun w hw => mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (hg0 w hw))
      (htw0 w hw u hu)) (hF0 w (houter_sub hw)))
    (fun w hw => by
      have hmax : 0 < max (r : ℝ) ((linfDist x w + 1 : ℕ) : ℝ) :=
        lt_of_lt_of_le (by positivity) (le_max_right _ _)
      have hb1 : 0 ≤ Cg * ((linfDist x w + 1 : ℕ) : ℝ) := mul_nonneg hCg (by positivity)
      have hb2 : 0 ≤ Ca * (1 + l u) / ((linfDist w u + 1 : ℕ) : ℝ) ^ (e + 6) :=
        div_nonneg (mul_nonneg hCa hl1) (by positivity)
      calc (n : ℝ) ^ 3 * g w * tau w u * F w
          ≤ (Cg * ((linfDist x w + 1 : ℕ) : ℝ)) *
              (Ca * (1 + l u) / ((linfDist w u + 1 : ℕ) : ℝ) ^ (e + 6)) *
              (CF / (max (r : ℝ) ((linfDist x w + 1 : ℕ) : ℝ)) ^ (e + 3)) :=
            mul_le_mul (mul_le_mul (hgo w hw) (htwu w hw u hu) (htw0 w hw u hu) hb1)
              (hF w (houter_sub hw)) (hF0 w (houter_sub hw)) (mul_nonneg hb1 hb2)
        _ = _ := by field_simp <;> ring)
  rw [← hCΦ, ← hk1, ← hM] at hΦ
  have hfactor : (n : ℝ) ^ 3 * (∑ w ∈ outer, g w * tau w u * tau u x * F w * F u) =
      tau u x * F u * ∑ w ∈ outer, (n : ℝ) ^ 3 * g w * tau w u * F w := by
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun w _ => by ring)
  rw [hfactor]
  have hΦ0 : 0 ≤ ∑ w ∈ outer, (n : ℝ) ^ 3 * g w * tau w u * F w :=
    Finset.sum_nonneg (fun w hw => mul_nonneg (mul_nonneg (mul_nonneg (by positivity)
      (hg0 w hw)) (htw0 w hw u hu)) (hF0 w (houter_sub hw)))
  have htxB0 : 0 ≤ Cb * (1 + l u) / k1 ^ (e + 7) := div_nonneg (mul_nonneg hCb hl1) (by positivity)
  have hfrac : (1 + l u) ^ 2 / k1 ^ 2 ≤ 1 := by
    rw [div_le_one (by positivity)]; exact pow_le_pow_left₀ hl1 hlk 2
  have hC0 : 0 ≤ Cb * CF * (Cg * Ca * CF) * CΦ :=
    mul_nonneg (mul_nonneg (mul_nonneg hCb hCF) (mul_nonneg (mul_nonneg hCg hCa) hCF)) hCΦ0
  calc tau u x * F u * ∑ w ∈ outer, (n : ℝ) ^ 3 * g w * tau w u * F w
      ≤ (Cb * (1 + l u) / k1 ^ (e + 7)) * (CF / M ^ (e + 3)) *
          (Cg * Ca * CF * (1 + l u) * CΦ / M ^ (e + 1)) :=
        mul_le_mul (mul_le_mul (htx u hu) (hF u hu) (hF0 u hu) htxB0) hΦ hΦ0
          (mul_nonneg htxB0 (div_nonneg hCF (by positivity)))
    _ = Cb * CF * (Cg * Ca * CF) * CΦ * ((1 + l u) ^ 2 / k1 ^ 2) *
          (1 / (k1 ^ (e + 5) * M ^ (2 * e + 4))) := by
        field_simp <;> ring
    _ ≤ Cb * CF * (Cg * Ca * CF) * CΦ * 1 * (1 / (k1 ^ (e + 5) * M ^ (2 * e + 4))) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hfrac hC0) (by positivity)
    _ = _ := by ring

/-- prop.var_term_1 (`d = e+7`) from pointwise inputs only: both `hphi` (Case 1, via
`phi_bound`) and `hcase2` (Case 2, via `psi_bound`) are discharged. No regime hypothesis. -/
theorem var_term_1_full_bound {e : ℕ} (x : Fin (e + 7) → ℤ) {n r q c : ℕ} (hn : 1 ≤ n)
    (hr : 1 ≤ r) (hrn : r ≤ n) (hq : n ≤ 4 * (q + 1))
    (Ann outer : Finset (Fin (e + 7) → ℤ)) (houter_sub : outer ⊆ Ann)
    (hAnn_ball : Ann ⊆ linfBall x ((2 * n : ℕ) : ℤ))
    (hAnn0 : Ann ⊆ linfBall (0 : Fin (e + 7) → ℤ) (n : ℤ))
    (hfar : ∀ w ∈ Ann \ outer, 2 * q ≤ linfDist x w)
    (g F l : (Fin (e + 7) → ℤ) → ℝ) (tau : (Fin (e + 7) → ℤ) → (Fin (e + 7) → ℤ) → ℝ)
    {Cg Cgo Ca Cb Cc Cτ CF : ℝ} (hCg : 0 ≤ Cg) (hCgo : 0 ≤ Cgo) (hCa : 0 ≤ Ca)
    (hCb : 0 ≤ Cb) (hCc : 0 ≤ Cc) (hCτ : 0 ≤ Cτ) (hCF : 0 ≤ CF)
    (hg0 : ∀ w ∈ Ann, 0 ≤ g w) (hF0 : ∀ u ∈ Ann, 0 ≤ F u)
    (htw0 : ∀ w ∈ Ann, ∀ u ∈ Ann, 0 ≤ tau w u) (htx0 : ∀ u ∈ Ann, 0 ≤ tau u x)
    (hl0 : ∀ u ∈ Ann, 0 ≤ l u) (hl : ∀ u ∈ Ann, l u ≤ (linfDist x u : ℝ))
    (hgo : ∀ w ∈ outer, (n : ℝ) ^ 3 * g w ≤ Cgo * ((linfDist x w + 1 : ℕ) : ℝ))
    (hg : ∀ w ∈ Ann \ outer,
      g w ≤ Cg / ((linfDist (0 : Fin (e + 7) → ℤ) w + 1 - c : ℕ) : ℝ) ^ 2)
    (hF : ∀ u ∈ Ann, F u ≤ CF / (max (r : ℝ) ((linfDist x u + 1 : ℕ) : ℝ)) ^ (e + 3))
    (htwu : ∀ w ∈ Ann, ∀ u ∈ Ann,
      tau w u ≤ Ca * (1 + l u) / ((linfDist w u + 1 : ℕ) : ℝ) ^ (e + 6))
    (htw_near : ∀ w ∈ Ann \ outer, ∀ u ∈ Ann, linfDist x u < q →
      tau w u ≤ Ca * (1 + l u) / (n : ℝ) ^ (e + 6))
    (htw : ∀ w ∈ Ann \ outer, ∀ u ∈ Ann,
      tau w u ≤ Cτ / ((linfDist w u + 1 : ℕ) : ℝ) ^ (e + 5))
    (htx : ∀ u ∈ Ann, tau u x ≤ Cb * (1 + l u) / ((linfDist x u + 1 : ℕ) : ℝ) ^ (e + 7))
    (htx_far : ∀ u ∈ Ann, q ≤ linfDist x u → tau u x ≤ Cc / (n : ℝ) ^ (e + 6)) :
    (n : ℝ) ^ 3 * ∑ u ∈ Ann, ∑ w ∈ Ann, g w * tau w u * tau u x * F w * F u
      ≤ (varTermOnePhiConstant e Cgo Ca Cb CF * varOuterRadialConstant (e + 7) +
        varTermOneInnerConstant e Cg Ca Cb Cc Cτ CF) / (r : ℝ) ^ (e + 7 - 6) := by
  have hphi := var_term_1_hphi x hr Ann outer houter_sub hAnn_ball g F l tau hCgo hCa hCb hCF
    (fun w hw => hg0 w (houter_sub hw)) hF0 (fun w hw => htw0 w (houter_sub hw)) htx0 hl0 hl
    hgo hF (fun w hw => htwu w (houter_sub hw)) htx
  exact var_term_1_source_bound x hn hr hrn hq Ann outer houter_sub hAnn_ball hAnn0 hfar g F l tau
    (by unfold varTermOnePhiConstant; positivity) hCg hCa hCb hCc hCτ hCF hphi
    (fun w hw => hg0 w (Finset.mem_sdiff.mp hw).1) hF0
    (fun w hw => htw0 w (Finset.mem_sdiff.mp hw).1) htx0 hl0 hl hg hF htw_near htw
    (fun u hu _ => htx u hu) htx_far

/-- Existential form of the full first diagram bound. -/
theorem var_term_1_full {e : ℕ} (x : Fin (e + 7) → ℤ) {n r q c : ℕ} (hn : 1 ≤ n)
    (hr : 1 ≤ r) (hrn : r ≤ n) (hq : n ≤ 4 * (q + 1))
    (Ann outer : Finset (Fin (e + 7) → ℤ)) (houter_sub : outer ⊆ Ann)
    (hAnn_ball : Ann ⊆ linfBall x ((2 * n : ℕ) : ℤ))
    (hAnn0 : Ann ⊆ linfBall (0 : Fin (e + 7) → ℤ) (n : ℤ))
    (hfar : ∀ w ∈ Ann \ outer, 2 * q ≤ linfDist x w)
    (g F l : (Fin (e + 7) → ℤ) → ℝ) (tau : (Fin (e + 7) → ℤ) → (Fin (e + 7) → ℤ) → ℝ)
    {Cg Cgo Ca Cb Cc Cτ CF : ℝ} (hCg : 0 ≤ Cg) (hCgo : 0 ≤ Cgo) (hCa : 0 ≤ Ca)
    (hCb : 0 ≤ Cb) (hCc : 0 ≤ Cc) (hCτ : 0 ≤ Cτ) (hCF : 0 ≤ CF)
    (hg0 : ∀ w ∈ Ann, 0 ≤ g w) (hF0 : ∀ u ∈ Ann, 0 ≤ F u)
    (htw0 : ∀ w ∈ Ann, ∀ u ∈ Ann, 0 ≤ tau w u) (htx0 : ∀ u ∈ Ann, 0 ≤ tau u x)
    (hl0 : ∀ u ∈ Ann, 0 ≤ l u) (hl : ∀ u ∈ Ann, l u ≤ (linfDist x u : ℝ))
    (hgo : ∀ w ∈ outer, (n : ℝ) ^ 3 * g w ≤ Cgo * ((linfDist x w + 1 : ℕ) : ℝ))
    (hg : ∀ w ∈ Ann \ outer,
      g w ≤ Cg / ((linfDist (0 : Fin (e + 7) → ℤ) w + 1 - c : ℕ) : ℝ) ^ 2)
    (hF : ∀ u ∈ Ann, F u ≤ CF / (max (r : ℝ) ((linfDist x u + 1 : ℕ) : ℝ)) ^ (e + 3))
    (htwu : ∀ w ∈ Ann, ∀ u ∈ Ann,
      tau w u ≤ Ca * (1 + l u) / ((linfDist w u + 1 : ℕ) : ℝ) ^ (e + 6))
    (htw_near : ∀ w ∈ Ann \ outer, ∀ u ∈ Ann, linfDist x u < q →
      tau w u ≤ Ca * (1 + l u) / (n : ℝ) ^ (e + 6))
    (htw : ∀ w ∈ Ann \ outer, ∀ u ∈ Ann,
      tau w u ≤ Cτ / ((linfDist w u + 1 : ℕ) : ℝ) ^ (e + 5))
    (htx : ∀ u ∈ Ann, tau u x ≤ Cb * (1 + l u) / ((linfDist x u + 1 : ℕ) : ℝ) ^ (e + 7))
    (htx_far : ∀ u ∈ Ann, q ≤ linfDist x u → tau u x ≤ Cc / (n : ℝ) ^ (e + 6)) :
    ∃ C : ℝ, 0 ≤ C ∧
      (n : ℝ) ^ 3 * ∑ u ∈ Ann, ∑ w ∈ Ann, g w * tau w u * tau u x * F w * F u
        ≤ C / (r : ℝ) ^ (e + 7 - 6) := by
  have hA : 0 ≤ varOuterRadialConstant (e + 7) := by unfold varOuterRadialConstant; positivity
  have houter : 0 ≤ varTermOnePhiConstant e Cgo Ca Cb CF := by
    unfold varTermOnePhiConstant
    positivity
  have hinner : 0 ≤ varTermOneInnerConstant e Cg Ca Cb Cc Cτ CF := by
    unfold varTermOneInnerConstant
    positivity
  exact ⟨varTermOnePhiConstant e Cgo Ca Cb CF * varOuterRadialConstant (e + 7) +
    varTermOneInnerConstant e Cg Ca Cb Cc Cτ CF, by positivity,
    var_term_1_full_bound x hn hr hrn hq Ann outer houter_sub hAnn_ball hAnn0 hfar g F l tau
      hCg hCgo hCa hCb hCc hCτ hCF hg0 hF0 htw0 htx0 hl0 hl hgo hg hF htwu htw_near htw htx htx_far⟩

end NearCritical.AppendixVariance
