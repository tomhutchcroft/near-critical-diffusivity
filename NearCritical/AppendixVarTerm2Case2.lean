module

public import NearCritical.AppendixVarTerm2

/-! Source prop.var_term_2, Case 2 (`u ∈ Ann_{c₁n} ∩ Λ_{n/2}`): the `Θ`-estimate and the
`hcase2` discharge of `var_term_2`.

Dimension `d = e + 7` (`d ≥ 7`).

* `theta_bound`: for `u` with `|x-u|_∞ ≥ 2q` (source: `|x-u| ≥ n/2`, `q ≈ n/4`, `n ≤ 4(q+1)`),
  `Θ(u) = ∑_{w∈Ann} τ(u,w) F(w)² ≲ n^{3-d}`. The inputs are pointwise
  `τ(u,w) ≤ C_τ(|u-w|+1)^{2-d}` and `F(w)² ≤ C_F max(r,|x-w|+1)^{8-2d}`, and `Ann ⊆ ball(x,2n)`.
  Proof as in the source: split at `|u-w| ≤ q`. Near `u`, `|x-w| ≥ q`, then `ball_inv_pow_sum`.
  Far from `u`, `τ ≤ C_τ(q+1)^{2-d}`, then a radial sum with shell weight `(j+1)^{d-1-(2d-8)} ≤ 1`.
* `var_term_2_case2`: `n³∑_{u∈Ann\outer}∑_{w∈Ann} gτ(u,w)τ(u,x)F(w)² ≤ C/r^{d-6}`, from pointwise
  `g ≤ C_g(1+r_u)^{-2}` [eq.g_inner], `τ(u,x) ≤ C_t n^{1-d}` [lem.box_twopoint_onesided], the
  `Θ` inputs above, and `eq.inner_sum` (the verified `inner_sum_count`). The final
  `n^{6-d} ≤ r^{6-d}` uses only `r ≤ n`, so NO regime hypothesis is needed here (unlike var_term_3).
* `var_term_2_source`: `var_term_2` with this `hcase2` discharged.

All τ/F/g bounds are explicit pointwise hypotheses (assumption (A) / Appendix A). -/
@[expose] public section
namespace NearCritical.AppendixVariance
open scoped BigOperators

/-- `∑_{y∈ball(x,K)} 1/(|x-y|+1)^{2d-8} ≤ 2d·3^{d-1}(K+1)` for `d = e+7`. -/
theorem ball_inv_pow_far_sum {e : ℕ} (x : Fin (e + 7) → ℤ) (K : ℕ) :
    ∑ y ∈ linfBall x (K : ℤ), (1 : ℝ) / ((linfDist x y + 1 : ℕ) : ℝ) ^ (2 * e + 6)
      ≤ 2 * ((e + 7 : ℕ) : ℝ) * 3 ^ (e + 6) * ((K : ℝ) + 1) := by
  refine (radial_sum_shell_bound (by omega) x K
    (fun j => (1 : ℝ) / ((j + 1 : ℕ) : ℝ) ^ (2 * e + 6)) (fun j => by positivity)).trans ?_
  have hterm : ∀ j ∈ Finset.range (K + 1),
      2 * ((e + 7 : ℕ) : ℝ) * 3 ^ (e + 7 - 1) * ((j + 1 : ℕ) : ℝ) ^ (e + 7 - 1) *
        ((1 : ℝ) / ((j + 1 : ℕ) : ℝ) ^ (2 * e + 6)) ≤ 2 * ((e + 7 : ℕ) : ℝ) * 3 ^ (e + 6) := by
    intro j _
    rw [show e + 7 - 1 = e + 6 by omega]
    have ht1 : (1 : ℝ) ≤ ((j + 1 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ j + 1 by omega)
    have hpos : (0 : ℝ) < ((j + 1 : ℕ) : ℝ) ^ (2 * e + 6) := by positivity
    have hle : ((j + 1 : ℕ) : ℝ) ^ (e + 6) ≤ ((j + 1 : ℕ) : ℝ) ^ (2 * e + 6) :=
      pow_le_pow_right₀ ht1 (by omega)
    have hfrac : ((j + 1 : ℕ) : ℝ) ^ (e + 6) * ((1 : ℝ) / ((j + 1 : ℕ) : ℝ) ^ (2 * e + 6)) ≤ 1 := by
      rw [mul_one_div, div_le_one hpos]; exact hle
    calc _ = 2 * ((e + 7 : ℕ) : ℝ) * 3 ^ (e + 6) * (((j + 1 : ℕ) : ℝ) ^ (e + 6) *
            ((1 : ℝ) / ((j + 1 : ℕ) : ℝ) ^ (2 * e + 6))) := by ring
      _ ≤ 2 * ((e + 7 : ℕ) : ℝ) * 3 ^ (e + 6) * 1 :=
          mul_le_mul_of_nonneg_left hfrac (by positivity)
      _ = _ := by ring
  refine (Finset.sum_le_sum hterm).trans (le_of_eq ?_)
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  push_cast; ring

/-- The source `Θ`-estimate: `Θ(u) ≤ C_τC_F·2d·3^{d-1}(4^{2d-10} + 3·4^{d-2})/n^{d-3}`. -/
theorem theta_bound {e : ℕ} {x u : Fin (e + 7) → ℤ} {n r q : ℕ} (hn : 1 ≤ n)
    (hq : n ≤ 4 * (q + 1)) (Ann : Finset (Fin (e + 7) → ℤ))
    (hAnn : Ann ⊆ linfBall x ((2 * n : ℕ) : ℤ)) (hfar : 2 * q ≤ linfDist x u)
    (tu F : (Fin (e + 7) → ℤ) → ℝ) {Cτ CF : ℝ} (hCτ : 0 ≤ Cτ) (hCF : 0 ≤ CF)
    (ht0 : ∀ w ∈ Ann, 0 ≤ tu w)
    (ht : ∀ w ∈ Ann, tu w ≤ Cτ / ((linfDist u w + 1 : ℕ) : ℝ) ^ (e + 5))
    (hF : ∀ w ∈ Ann,
      F w ^ 2 ≤ CF / (max (r : ℝ) ((linfDist x w + 1 : ℕ) : ℝ)) ^ (2 * e + 6)) :
    ∑ w ∈ Ann, tu w * F w ^ 2 ≤
      Cτ * CF * (2 * ((e + 7 : ℕ) : ℝ) * 3 ^ (e + 6)) * (4 ^ (2 * e + 4) + 3 * 4 ^ (e + 5)) /
        (n : ℝ) ^ (e + 4) := by
  set B : ℝ := 2 * ((e + 7 : ℕ) : ℝ) * 3 ^ (e + 6) with hB
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  set Q : ℝ := ((q : ℝ) + 1) with hQ
  have hQpos : 0 < Q := by rw [hQ]; positivity
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hnQ : (n : ℝ) ≤ 4 * Q := by rw [hQ]; exact_mod_cast hq
  rw [← Finset.sum_filter_add_sum_filter_not Ann (fun w => linfDist u w ≤ q)]
  -- near part: |u-w| ≤ q
  have hA : ∑ w ∈ Ann.filter (fun w => linfDist u w ≤ q), tu w * F w ^ 2 ≤
      Cτ * CF / Q ^ (2 * e + 6) * (B * Q ^ 2) := by
    have hpt : ∀ w ∈ Ann.filter (fun w => linfDist u w ≤ q), tu w * F w ^ 2 ≤
        Cτ * CF / Q ^ (2 * e + 6) * ((1 : ℝ) / ((linfDist u w + 1 : ℕ) : ℝ) ^ (e + 5)) := by
      intro w hw
      rw [Finset.mem_filter] at hw
      obtain ⟨hwA, hwq⟩ := hw
      have htri := linfDist_triangle x w u
      rw [linfDist_comm w u] at htri
      have hm : q ≤ linfDist x w := by omega
      have hQmax : Q ≤ max (r : ℝ) ((linfDist x w + 1 : ℕ) : ℝ) := by
        refine le_max_of_le_right ?_
        rw [hQ]; exact_mod_cast (show q + 1 ≤ linfDist x w + 1 by omega)
      have hF2 : F w ^ 2 ≤ CF / Q ^ (2 * e + 6) :=
        (hF w hwA).trans (div_le_div_of_nonneg_left hCF (by positivity)
          (pow_le_pow_left₀ hQpos.le hQmax _))
      calc tu w * F w ^ 2 ≤ (Cτ / ((linfDist u w + 1 : ℕ) : ℝ) ^ (e + 5)) *
            (CF / Q ^ (2 * e + 6)) :=
          mul_le_mul (ht w hwA) hF2 (sq_nonneg _) (div_nonneg hCτ (by positivity))
        _ = _ := by ring
    have hsub : Ann.filter (fun w => linfDist u w ≤ q) ⊆ linfBall u (q : ℤ) := by
      intro w hw
      rw [Finset.mem_filter] at hw
      rw [mem_linfBall_iff_dist u w (by positivity)]
      simpa using hw.2
    have hball := ball_inv_pow_sum (show 2 ≤ e + 7 by omega) u q
    rw [show e + 7 - 2 = e + 5 by omega, show e + 7 - 1 = e + 6 by omega] at hball
    calc _ ≤ ∑ w ∈ Ann.filter (fun w => linfDist u w ≤ q),
          Cτ * CF / Q ^ (2 * e + 6) * ((1 : ℝ) / ((linfDist u w + 1 : ℕ) : ℝ) ^ (e + 5)) :=
          Finset.sum_le_sum hpt
      _ = Cτ * CF / Q ^ (2 * e + 6) * ∑ w ∈ Ann.filter (fun w => linfDist u w ≤ q),
          (1 : ℝ) / ((linfDist u w + 1 : ℕ) : ℝ) ^ (e + 5) := by rw [Finset.mul_sum]
      _ ≤ Cτ * CF / Q ^ (2 * e + 6) * ∑ w ∈ linfBall u (q : ℤ),
          (1 : ℝ) / ((linfDist u w + 1 : ℕ) : ℝ) ^ (e + 5) :=
          mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity))
            (div_nonneg (mul_nonneg hCτ hCF) (by positivity))
      _ ≤ Cτ * CF / Q ^ (2 * e + 6) * (B * Q ^ 2) :=
          mul_le_mul_of_nonneg_left (by rw [hB, hQ]; exact hball)
            (div_nonneg (mul_nonneg hCτ hCF) (by positivity))
  -- far part: |u-w| > q
  have hB2 : ∑ w ∈ Ann.filter (fun w => ¬ linfDist u w ≤ q), tu w * F w ^ 2 ≤
      Cτ * CF / Q ^ (e + 5) * (B * (2 * (n : ℝ) + 1)) := by
    have hpt : ∀ w ∈ Ann.filter (fun w => ¬ linfDist u w ≤ q), tu w * F w ^ 2 ≤
        Cτ * CF / Q ^ (e + 5) * ((1 : ℝ) / ((linfDist x w + 1 : ℕ) : ℝ) ^ (2 * e + 6)) := by
      intro w hw
      rw [Finset.mem_filter] at hw
      obtain ⟨hwA, hwq⟩ := hw
      have hQp : Q ≤ ((linfDist u w + 1 : ℕ) : ℝ) := by
        rw [hQ]; exact_mod_cast (show q + 1 ≤ linfDist u w + 1 by omega)
      have ht2 : tu w ≤ Cτ / Q ^ (e + 5) :=
        (ht w hwA).trans (div_le_div_of_nonneg_left hCτ (by positivity)
          (pow_le_pow_left₀ hQpos.le hQp _))
      have hF2 : F w ^ 2 ≤ CF / ((linfDist x w + 1 : ℕ) : ℝ) ^ (2 * e + 6) :=
        (hF w hwA).trans (div_le_div_of_nonneg_left hCF (by positivity)
          (pow_le_pow_left₀ (by positivity) (le_max_right _ _) _))
      calc tu w * F w ^ 2 ≤ (Cτ / Q ^ (e + 5)) *
            (CF / ((linfDist x w + 1 : ℕ) : ℝ) ^ (2 * e + 6)) :=
          mul_le_mul ht2 hF2 (sq_nonneg _) (div_nonneg hCτ (by positivity))
        _ = _ := by ring
    have hsub : Ann.filter (fun w => ¬ linfDist u w ≤ q) ⊆ linfBall x ((2 * n : ℕ) : ℤ) :=
      (Finset.filter_subset _ _).trans hAnn
    have hrad := ball_inv_pow_far_sum x (2 * n)
    calc _ ≤ ∑ w ∈ Ann.filter (fun w => ¬ linfDist u w ≤ q),
          Cτ * CF / Q ^ (e + 5) * ((1 : ℝ) / ((linfDist x w + 1 : ℕ) : ℝ) ^ (2 * e + 6)) :=
          Finset.sum_le_sum hpt
      _ = Cτ * CF / Q ^ (e + 5) * ∑ w ∈ Ann.filter (fun w => ¬ linfDist u w ≤ q),
          (1 : ℝ) / ((linfDist x w + 1 : ℕ) : ℝ) ^ (2 * e + 6) := by rw [Finset.mul_sum]
      _ ≤ Cτ * CF / Q ^ (e + 5) * ∑ w ∈ linfBall x ((2 * n : ℕ) : ℤ),
          (1 : ℝ) / ((linfDist x w + 1 : ℕ) : ℝ) ^ (2 * e + 6) :=
          mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity))
            (div_nonneg (mul_nonneg hCτ hCF) (by positivity))
      _ ≤ Cτ * CF / Q ^ (e + 5) * (B * (2 * (n : ℝ) + 1)) := by
          refine mul_le_mul_of_nonneg_left (hrad.trans (le_of_eq ?_))
            (div_nonneg (mul_nonneg hCτ hCF) (by positivity))
          rw [hB]; push_cast; ring
  -- convert both to n^{3-d}
  have hc1 : Q ^ 2 / Q ^ (2 * e + 6) ≤ 4 ^ (2 * e + 4) / (n : ℝ) ^ (e + 4) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : (n : ℝ) ^ (e + 4) ≤ (n : ℝ) ^ (2 * e + 4) := pow_le_pow_right₀ hn1 (by omega)
    have h2 : (n : ℝ) ^ (2 * e + 4) ≤ (4 * Q) ^ (2 * e + 4) :=
      pow_le_pow_left₀ hnpos.le hnQ _
    calc Q ^ 2 * (n : ℝ) ^ (e + 4) ≤ Q ^ 2 * (4 * Q) ^ (2 * e + 4) :=
          mul_le_mul_of_nonneg_left (h1.trans h2) (by positivity)
      _ = 4 ^ (2 * e + 4) * Q ^ (2 * e + 6) := by rw [mul_pow]; ring
  have hc2 : (2 * (n : ℝ) + 1) / Q ^ (e + 5) ≤ 3 * 4 ^ (e + 5) / (n : ℝ) ^ (e + 4) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h2 : (n : ℝ) ^ (e + 5) ≤ (4 * Q) ^ (e + 5) := pow_le_pow_left₀ hnpos.le hnQ _
    calc (2 * (n : ℝ) + 1) * (n : ℝ) ^ (e + 4) ≤ 3 * (n : ℝ) * (n : ℝ) ^ (e + 4) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = 3 * (n : ℝ) ^ (e + 5) := by ring
      _ ≤ 3 * (4 * Q) ^ (e + 5) := mul_le_mul_of_nonneg_left h2 (by norm_num)
      _ = 3 * 4 ^ (e + 5) * Q ^ (e + 5) := by rw [mul_pow]; ring
  have hK0 : 0 ≤ Cτ * CF * B := mul_nonneg (mul_nonneg hCτ hCF) hB0
  calc _ ≤ Cτ * CF / Q ^ (2 * e + 6) * (B * Q ^ 2) +
        Cτ * CF / Q ^ (e + 5) * (B * (2 * (n : ℝ) + 1)) := add_le_add hA hB2
    _ = Cτ * CF * B * (Q ^ 2 / Q ^ (2 * e + 6)) +
        Cτ * CF * B * ((2 * (n : ℝ) + 1) / Q ^ (e + 5)) := by ring
    _ ≤ Cτ * CF * B * (4 ^ (2 * e + 4) / (n : ℝ) ^ (e + 4)) +
        Cτ * CF * B * (3 * 4 ^ (e + 5) / (n : ℝ) ^ (e + 4)) :=
        add_le_add (mul_le_mul_of_nonneg_left hc1 hK0) (mul_le_mul_of_nonneg_left hc2 hK0)
    _ = _ := by rw [hB]; ring

/-- Coefficient of the inner estimate for the second diagram. -/
noncomputable def varTermTwoInnerConstant (e : ℕ) (Cg Ct Cτ CF : ℝ) : ℝ :=
  Cg * Ct * (Cτ * CF * (2 * ((e + 7 : ℕ) : ℝ) * 3 ^ (e + 6)) *
    (4 ^ (2 * e + 4) + 3 * 4 ^ (e + 5))) *
    (2 * ((e + 7 : ℕ) : ℝ) * 3 ^ (e + 6) * 2 * 2 ^ (e + 6))

/-- `hcase2` of `var_term_2`: `n³∑_{u∈Ann\outer}∑_{w∈Ann} g(u)τ(u,w)τ(u,x)F(w)² ≤ C/r^{d-6}`. -/
theorem var_term_2_case2 {e : ℕ} (x : Fin (e + 7) → ℤ) {n r q c : ℕ} (hn : 1 ≤ n)
    (hr : 1 ≤ r) (hrn : r ≤ n) (hq : n ≤ 4 * (q + 1))
    (Ann outer : Finset (Fin (e + 7) → ℤ))
    (hAnn_ball : Ann ⊆ linfBall x ((2 * n : ℕ) : ℤ))
    (hAnn0 : Ann ⊆ linfBall (0 : Fin (e + 7) → ℤ) (n : ℤ))
    (hfar : ∀ u ∈ Ann \ outer, 2 * q ≤ linfDist x u)
    (g F : (Fin (e + 7) → ℤ) → ℝ) (tau : (Fin (e + 7) → ℤ) → (Fin (e + 7) → ℤ) → ℝ)
    {Cg Ct Cτ CF : ℝ} (hCg : 0 ≤ Cg) (hCt : 0 ≤ Ct) (hCτ : 0 ≤ Cτ) (hCF : 0 ≤ CF)
    (hg0 : ∀ u ∈ Ann \ outer, 0 ≤ g u) (htx0 : ∀ u ∈ Ann \ outer, 0 ≤ tau u x)
    (htw0 : ∀ u ∈ Ann \ outer, ∀ w ∈ Ann, 0 ≤ tau u w)
    (hg : ∀ u ∈ Ann \ outer,
      g u ≤ Cg / ((linfDist (0 : Fin (e + 7) → ℤ) u + 1 - c : ℕ) : ℝ) ^ 2)
    (htx : ∀ u ∈ Ann \ outer, tau u x ≤ Ct / (n : ℝ) ^ (e + 6))
    (htw : ∀ u ∈ Ann \ outer, ∀ w ∈ Ann,
      tau u w ≤ Cτ / ((linfDist u w + 1 : ℕ) : ℝ) ^ (e + 5))
    (hF : ∀ w ∈ Ann,
      F w ^ 2 ≤ CF / (max (r : ℝ) ((linfDist x w + 1 : ℕ) : ℝ)) ^ (2 * e + 6)) :
    (n : ℝ) ^ 3 * ∑ u ∈ Ann \ outer, ∑ w ∈ Ann, g u * tau u w * tau u x * F w ^ 2 ≤
      Cg * Ct * (Cτ * CF * (2 * ((e + 7 : ℕ) : ℝ) * 3 ^ (e + 6)) *
        (4 ^ (2 * e + 4) + 3 * 4 ^ (e + 5))) *
        (2 * ((e + 7 : ℕ) : ℝ) * 3 ^ (e + 6) * 2 * 2 ^ (e + 6)) / (r : ℝ) ^ (e + 1) := by
  set CΘ : ℝ := Cτ * CF * (2 * ((e + 7 : ℕ) : ℝ) * 3 ^ (e + 6)) *
    (4 ^ (2 * e + 4) + 3 * 4 ^ (e + 5)) with hCΘ
  have hCΘ0 : 0 ≤ CΘ := by
    rw [hCΘ]; exact mul_nonneg (mul_nonneg (mul_nonneg hCτ hCF) (by positivity)) (by positivity)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hrpos : (0 : ℝ) < r := by linarith
  set K : ℝ := Cg * Ct * CΘ / ((n : ℝ) ^ (e + 6) * (n : ℝ) ^ (e + 4)) with hK
  have hK0 : 0 ≤ K := by
    rw [hK]; exact div_nonneg (mul_nonneg (mul_nonneg hCg hCt) hCΘ0) (by positivity)
  have hpt : ∀ u ∈ Ann \ outer, ∑ w ∈ Ann, g u * tau u w * tau u x * F w ^ 2 ≤
      K * ((1 : ℝ) / ((linfDist (0 : Fin (e + 7) → ℤ) u + 1 - c : ℕ) : ℝ) ^ 2) := by
    intro u hu
    have hΘ := theta_bound hn hq Ann hAnn_ball (hfar u hu) (tau u) F hCτ hCF
      (htw0 u hu) (htw u hu) hF
    rw [← hCΘ] at hΘ
    have hΘ0 : 0 ≤ ∑ w ∈ Ann, tau u w * F w ^ 2 :=
      Finset.sum_nonneg (fun w hw => mul_nonneg (htw0 u hu w hw) (sq_nonneg _))
    have hsplit : ∑ w ∈ Ann, g u * tau u w * tau u x * F w ^ 2 =
        g u * tau u x * ∑ w ∈ Ann, tau u w * F w ^ 2 := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun w _ => by ring)
    rw [hsplit]
    have hgB0 : 0 ≤ Cg / ((linfDist (0 : Fin (e + 7) → ℤ) u + 1 - c : ℕ) : ℝ) ^ 2 :=
      div_nonneg hCg (by positivity)
    have htB0 : 0 ≤ Ct / (n : ℝ) ^ (e + 6) := div_nonneg hCt (by positivity)
    calc g u * tau u x * ∑ w ∈ Ann, tau u w * F w ^ 2
        ≤ (Cg / ((linfDist (0 : Fin (e + 7) → ℤ) u + 1 - c : ℕ) : ℝ) ^ 2) *
            (Ct / (n : ℝ) ^ (e + 6)) * (CΘ / (n : ℝ) ^ (e + 4)) :=
          mul_le_mul (mul_le_mul (hg u hu) (htx u hu) (htx0 u hu) hgB0) hΘ hΘ0
            (mul_nonneg hgB0 htB0)
      _ = _ := by rw [hK]; ring
  have hinner := inner_sum_count (show 1 ≤ e + 7 by omega) c n
  rw [show e + 7 - 1 = e + 6 by omega] at hinner
  have hsub : Ann \ outer ⊆ linfBall (0 : Fin (e + 7) → ℤ) (n : ℤ) :=
    Finset.sdiff_subset.trans hAnn0
  have hsum : ∑ u ∈ Ann \ outer, ∑ w ∈ Ann, g u * tau u w * tau u x * F w ^ 2 ≤
      K * (2 * ((e + 7 : ℕ) : ℝ) * 3 ^ (e + 6) * ((n : ℝ) + 1) ^ (e + 6) * 2) := by
    calc _ ≤ ∑ u ∈ Ann \ outer,
          K * ((1 : ℝ) / ((linfDist (0 : Fin (e + 7) → ℤ) u + 1 - c : ℕ) : ℝ) ^ 2) :=
          Finset.sum_le_sum hpt
      _ = K * ∑ u ∈ Ann \ outer,
          (1 : ℝ) / ((linfDist (0 : Fin (e + 7) → ℤ) u + 1 - c : ℕ) : ℝ) ^ 2 := by
          rw [Finset.mul_sum]
      _ ≤ K * ∑ u ∈ linfBall (0 : Fin (e + 7) → ℤ) (n : ℤ),
          (1 : ℝ) / ((linfDist (0 : Fin (e + 7) → ℤ) u + 1 - c : ℕ) : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)) hK0
      _ ≤ _ := mul_le_mul_of_nonneg_left hinner hK0
  have hscale : (n : ℝ) ^ 3 * ((n : ℝ) + 1) ^ (e + 6) /
      ((n : ℝ) ^ (e + 6) * (n : ℝ) ^ (e + 4)) ≤ 2 ^ (e + 6) / (r : ℝ) ^ (e + 1) := by
    have h2n : (n : ℝ) + 1 ≤ 2 * n := by linarith
    have hp : ((n : ℝ) + 1) ^ (e + 6) ≤ (2 * (n : ℝ)) ^ (e + 6) :=
      pow_le_pow_left₀ (by positivity) h2n _
    have hrn' : (r : ℝ) ^ (e + 1) ≤ (n : ℝ) ^ (e + 1) :=
      pow_le_pow_left₀ hrpos.le (by exact_mod_cast hrn) _
    calc _ ≤ (n : ℝ) ^ 3 * (2 * (n : ℝ)) ^ (e + 6) /
          ((n : ℝ) ^ (e + 6) * (n : ℝ) ^ (e + 4)) :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hp (by positivity))
            (by positivity)
      _ = 2 ^ (e + 6) / (n : ℝ) ^ (e + 1) := by
          rw [mul_pow]; field_simp; ring
      _ ≤ 2 ^ (e + 6) / (r : ℝ) ^ (e + 1) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hrn'
  have hA0 : 0 ≤ Cg * Ct * CΘ * (2 * ((e + 7 : ℕ) : ℝ) * 3 ^ (e + 6) * 2) :=
    mul_nonneg (mul_nonneg (mul_nonneg hCg hCt) hCΘ0) (by positivity)
  calc _ ≤ (n : ℝ) ^ 3 *
        (K * (2 * ((e + 7 : ℕ) : ℝ) * 3 ^ (e + 6) * ((n : ℝ) + 1) ^ (e + 6) * 2)) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = Cg * Ct * CΘ * (2 * ((e + 7 : ℕ) : ℝ) * 3 ^ (e + 6) * 2) *
        ((n : ℝ) ^ 3 * ((n : ℝ) + 1) ^ (e + 6) / ((n : ℝ) ^ (e + 6) * (n : ℝ) ^ (e + 4))) := by
        rw [hK]; ring
    _ ≤ Cg * Ct * CΘ * (2 * ((e + 7 : ℕ) : ℝ) * 3 ^ (e + 6) * 2) *
        (2 ^ (e + 6) / (r : ℝ) ^ (e + 1)) := mul_le_mul_of_nonneg_left hscale hA0
    _ = _ := by rw [hCΘ]; ring

/-- prop.var_term_2 with its inner case (`hcase2`) discharged by `var_term_2_case2`. -/
theorem var_term_2_source_bound {e : ℕ} (x : Fin (e + 7) → ℤ) {n r q c : ℕ} (hn : 1 ≤ n)
    (hr : 1 ≤ r) (hrn : r ≤ n) (hq : n ≤ 4 * (q + 1))
    (Ann outer : Finset (Fin (e + 7) → ℤ)) (houter_sub : outer ⊆ Ann)
    (hAnn_ball : Ann ⊆ linfBall x ((2 * n : ℕ) : ℤ))
    (hAnn0 : Ann ⊆ linfBall (0 : Fin (e + 7) → ℤ) (n : ℤ))
    (hfar : ∀ u ∈ Ann \ outer, 2 * q ≤ linfDist x u)
    (g F : (Fin (e + 7) → ℤ) → ℝ) (tau : (Fin (e + 7) → ℤ) → (Fin (e + 7) → ℤ) → ℝ)
    {Cbub Cg Ct Cτ CF : ℝ} (hCbub : 0 ≤ Cbub)
    (hCg : 0 ≤ Cg) (hCt : 0 ≤ Ct) (hCτ : 0 ≤ Cτ) (hCF : 0 ≤ CF)
    (hbubble : ∀ w ∈ Ann,
        (n : ℝ) ^ 3 * ((∑ u ∈ outer, g u * tau u w * tau u x) * F w ^ 2)
          ≤ Cbub * (1 / (((linfDist x w + 1 : ℕ) : ℝ) ^ (e + 7 - 4)
              * (max (r : ℝ) ((linfDist x w + 1 : ℕ) : ℝ)) ^ (2 * (e + 7) - 8))))
    (hg0 : ∀ u ∈ Ann \ outer, 0 ≤ g u) (htx0 : ∀ u ∈ Ann \ outer, 0 ≤ tau u x)
    (htw0 : ∀ u ∈ Ann \ outer, ∀ w ∈ Ann, 0 ≤ tau u w)
    (hg : ∀ u ∈ Ann \ outer,
      g u ≤ Cg / ((linfDist (0 : Fin (e + 7) → ℤ) u + 1 - c : ℕ) : ℝ) ^ 2)
    (htx : ∀ u ∈ Ann \ outer, tau u x ≤ Ct / (n : ℝ) ^ (e + 6))
    (htw : ∀ u ∈ Ann \ outer, ∀ w ∈ Ann,
      tau u w ≤ Cτ / ((linfDist u w + 1 : ℕ) : ℝ) ^ (e + 5))
    (hF : ∀ w ∈ Ann,
      F w ^ 2 ≤ CF / (max (r : ℝ) ((linfDist x w + 1 : ℕ) : ℝ)) ^ (2 * e + 6)) :
    (n : ℝ) ^ 3 * ∑ u ∈ Ann, ∑ w ∈ Ann, g u * tau u w * tau u x * F w ^ 2
      ≤ (Cbub * varOuterRadialConstant (e + 7) + varTermTwoInnerConstant e Cg Ct Cτ CF) / (r : ℝ) ^ (e + 7 - 6) := by
  have h2 := var_term_2_case2 x hn hr hrn hq Ann outer hAnn_ball hAnn0 hfar g F tau
    hCg hCt hCτ hCF hg0 htx0 htw0 hg htx htw hF
  rw [show e + 1 = e + 7 - 6 by omega] at h2
  exact var_term_2_bound (d := e + 7) (by omega) x hr hrn Ann outer g F tau Cbub
    (varTermTwoInnerConstant e Cg Ct Cτ CF) hCbub (by unfold varTermTwoInnerConstant; positivity)
    houter_sub hAnn_ball hbubble h2

/-- Existential form of the source second diagram bound. -/
theorem var_term_2_source {e : ℕ} (x : Fin (e + 7) → ℤ) {n r q c : ℕ} (hn : 1 ≤ n)
    (hr : 1 ≤ r) (hrn : r ≤ n) (hq : n ≤ 4 * (q + 1))
    (Ann outer : Finset (Fin (e + 7) → ℤ)) (houter_sub : outer ⊆ Ann)
    (hAnn_ball : Ann ⊆ linfBall x ((2 * n : ℕ) : ℤ))
    (hAnn0 : Ann ⊆ linfBall (0 : Fin (e + 7) → ℤ) (n : ℤ))
    (hfar : ∀ u ∈ Ann \ outer, 2 * q ≤ linfDist x u)
    (g F : (Fin (e + 7) → ℤ) → ℝ) (tau : (Fin (e + 7) → ℤ) → (Fin (e + 7) → ℤ) → ℝ)
    {Cbub Cg Ct Cτ CF : ℝ} (hCbub : 0 ≤ Cbub)
    (hCg : 0 ≤ Cg) (hCt : 0 ≤ Ct) (hCτ : 0 ≤ Cτ) (hCF : 0 ≤ CF)
    (hbubble : ∀ w ∈ Ann,
        (n : ℝ) ^ 3 * ((∑ u ∈ outer, g u * tau u w * tau u x) * F w ^ 2)
          ≤ Cbub * (1 / (((linfDist x w + 1 : ℕ) : ℝ) ^ (e + 7 - 4)
              * (max (r : ℝ) ((linfDist x w + 1 : ℕ) : ℝ)) ^ (2 * (e + 7) - 8))))
    (hg0 : ∀ u ∈ Ann \ outer, 0 ≤ g u) (htx0 : ∀ u ∈ Ann \ outer, 0 ≤ tau u x)
    (htw0 : ∀ u ∈ Ann \ outer, ∀ w ∈ Ann, 0 ≤ tau u w)
    (hg : ∀ u ∈ Ann \ outer,
      g u ≤ Cg / ((linfDist (0 : Fin (e + 7) → ℤ) u + 1 - c : ℕ) : ℝ) ^ 2)
    (htx : ∀ u ∈ Ann \ outer, tau u x ≤ Ct / (n : ℝ) ^ (e + 6))
    (htw : ∀ u ∈ Ann \ outer, ∀ w ∈ Ann,
      tau u w ≤ Cτ / ((linfDist u w + 1 : ℕ) : ℝ) ^ (e + 5))
    (hF : ∀ w ∈ Ann,
      F w ^ 2 ≤ CF / (max (r : ℝ) ((linfDist x w + 1 : ℕ) : ℝ)) ^ (2 * e + 6)) :
    ∃ C : ℝ, 0 ≤ C ∧
      (n : ℝ) ^ 3 * ∑ u ∈ Ann, ∑ w ∈ Ann, g u * tau u w * tau u x * F w ^ 2
        ≤ C / (r : ℝ) ^ (e + 7 - 6) := by
  have hA : 0 ≤ varOuterRadialConstant (e + 7) := by unfold varOuterRadialConstant; positivity
  have hinner : 0 ≤ varTermTwoInnerConstant e Cg Ct Cτ CF := by
    unfold varTermTwoInnerConstant
    positivity
  exact ⟨Cbub * varOuterRadialConstant (e + 7) + varTermTwoInnerConstant e Cg Ct Cτ CF, by positivity,
    var_term_2_source_bound x hn hr hrn hq Ann outer houter_sub hAnn_ball hAnn0 hfar g F tau
      hCbub hCg hCt hCτ hCF hbubble hg0 htx0 htw0 hg htx htw hF⟩

end NearCritical.AppendixVariance
