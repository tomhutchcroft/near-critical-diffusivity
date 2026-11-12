module

public import NearCritical.AppendixVarTerm13

/-! Source prop.var_term_1, Case 2 (`w ∈ Ann_{c₁n} ∩ Λ_{n/2}`): the `Ψ`-estimate and the
`hcase2` discharge of `var_term_1`.

Dimension `d = e + 7` (`d ≥ 7`). `Ψ(w) = ∑_{u∈Ann} τ(w,u) τ(u,x) F(u)`.

* `psi_bound`: for `|x-w|_∞ ≥ 2q` with `n ≤ 4(q+1)`, `Ψ(w) ≤ D/(n^{d-1} r^{d-6})`. As in the
  source, split at `|x-u| < q`:
  - near `x`: `τ(w,u) ≤ C_a(1+l_u)n^{1-d}`, `τ(u,x) ≤ C_b(1+l_u)(1+k)^{-d}`, `l_u ≤ k`,
    `F(u) ≤ C_F max(r,k+1)^{4-d}`, then `radial_div_sum_le` (`p = d-2`, `t = d-6`);
  - far from `x`: `τ(u,x) ≤ C_c n^{1-d}`, `F(u) ≤ C_F(q+1)^{4-d}`,
    `τ(w,u) ≤ C_τ(|w-u|+1)^{2-d}`, then `ball_inv_pow_sum` on `ball(w,4n)`.
  The source's `n^{1-d}r^{6-d} + n^{7-2d}` is bounded by `n^{1-d}r^{6-d}` (using `r ≤ n`).
* `var_term_1_case2`: `n³∑_u∑_{w∈Ann\outer} g(w)τ(w,u)τ(u,x)F(w)F(u) ≤ C/r^{d-6}`, via
  `g ≤ C_g(|w|+1-c)^{-2}` and the verified `inner_sum_count` (eq.inner_sum). No regime hypothesis.
* `var_term_1_source`: `var_term_1` with this `hcase2` discharged.

All τ/F/g bounds are explicit pointwise hypotheses (assumption (A) / Appendix A). -/
@[expose] public section
namespace NearCritical.AppendixVariance
open scoped BigOperators

/-- `1/Q^m ≤ 4^m/n^m` when `n ≤ 4Q`. -/
theorem inv_pow_le_of_le_four_mul {n : ℕ} {Q : ℝ} (hn : 1 ≤ n) (hQ : 0 < Q)
    (hnQ : (n : ℝ) ≤ 4 * Q) (m : ℕ) : 1 / Q ^ m ≤ 4 ^ m / (n : ℝ) ^ m := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul, ← mul_pow]
  exact pow_le_pow_left₀ hnpos.le hnQ m

/-- The source `Ψ`-estimate. -/
theorem psi_bound {e : ℕ} {x w : Fin (e + 7) → ℤ} {n r q : ℕ} (hn : 1 ≤ n) (hr : 1 ≤ r)
    (hrn : r ≤ n) (hq : n ≤ 4 * (q + 1)) (Ann : Finset (Fin (e + 7) → ℤ))
    (hAnn : Ann ⊆ linfBall x ((2 * n : ℕ) : ℤ)) (hw : w ∈ Ann)
    (hfar : 2 * q ≤ linfDist x w)
    (tw tx F l : (Fin (e + 7) → ℤ) → ℝ) {Ca Cb Cc Cτ CF : ℝ}
    (hCa : 0 ≤ Ca) (hCb : 0 ≤ Cb) (hCc : 0 ≤ Cc) (hCτ : 0 ≤ Cτ) (hCF : 0 ≤ CF)
    (htw0 : ∀ u ∈ Ann, 0 ≤ tw u) (htx0 : ∀ u ∈ Ann, 0 ≤ tx u) (hF0 : ∀ u ∈ Ann, 0 ≤ F u)
    (hl0 : ∀ u ∈ Ann, 0 ≤ l u) (hl : ∀ u ∈ Ann, l u ≤ (linfDist x u : ℝ))
    (hF : ∀ u ∈ Ann, F u ≤ CF / (max (r : ℝ) ((linfDist x u + 1 : ℕ) : ℝ)) ^ (e + 3))
    (htw_near : ∀ u ∈ Ann, linfDist x u < q → tw u ≤ Ca * (1 + l u) / (n : ℝ) ^ (e + 6))
    (htw : ∀ u ∈ Ann, tw u ≤ Cτ / ((linfDist w u + 1 : ℕ) : ℝ) ^ (e + 5))
    (htx_near : ∀ u ∈ Ann, linfDist x u < q →
      tx u ≤ Cb * (1 + l u) / ((linfDist x u + 1 : ℕ) : ℝ) ^ (e + 7))
    (htx_far : ∀ u ∈ Ann, q ≤ linfDist x u → tx u ≤ Cc / (n : ℝ) ^ (e + 6)) :
    ∑ u ∈ Ann, tw u * tx u * F u ≤
      (Ca * Cb * CF * (2 * ((e + 7 : ℕ) : ℝ) * 3 ^ (e + 6) *
          ((((e + 1 : ℕ) : ℝ) + 1) / ((e + 1 : ℕ) : ℝ))) +
        Cτ * Cc * CF * (2 * ((e + 7 : ℕ) : ℝ) * 3 ^ (e + 6)) * (25 * 4 ^ (e + 3))) /
        ((n : ℝ) ^ (e + 6) * (r : ℝ) ^ (e + 1)) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hrpos : (0 : ℝ) < r := by linarith
  have hrn' : (r : ℝ) ≤ n := by exact_mod_cast hrn
  set Q : ℝ := (q : ℝ) + 1 with hQdef
  have hQpos : 0 < Q := by rw [hQdef]; positivity
  have hnQ : (n : ℝ) ≤ 4 * Q := by rw [hQdef]; exact_mod_cast hq
  set B : ℝ := 2 * ((e + 7 : ℕ) : ℝ) * 3 ^ (e + 6) with hB
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  rw [← Finset.sum_filter_add_sum_filter_not Ann (fun u => linfDist x u < q)]
  -- near x
  have hnear : ∑ u ∈ Ann.filter (fun u => linfDist x u < q), tw u * tx u * F u ≤
      Ca * Cb * CF / (n : ℝ) ^ (e + 6) *
        (B * ((((e + 1 : ℕ) : ℝ) + 1) / (((e + 1 : ℕ) : ℝ) * (r : ℝ) ^ (e + 1)))) := by
    have hK0 : 0 ≤ Ca * Cb * CF / (n : ℝ) ^ (e + 6) :=
      div_nonneg (mul_nonneg (mul_nonneg hCa hCb) hCF) (by positivity)
    have hpt : ∀ u ∈ Ann.filter (fun u => linfDist x u < q), tw u * tx u * F u ≤
        Ca * Cb * CF / (n : ℝ) ^ (e + 6) *
          (1 / (((linfDist x u + 1 : ℕ) : ℝ) ^ (e + 5) *
            (max (r : ℝ) ((linfDist x u + 1 : ℕ) : ℝ)) ^ (e + 3))) := by
      intro u hu
      rw [Finset.mem_filter] at hu
      obtain ⟨huA, hk⟩ := hu
      set k1 : ℝ := ((linfDist x u + 1 : ℕ) : ℝ) with hk1
      have hk1pos : 0 < k1 := by rw [hk1]; positivity
      set M : ℝ := max (r : ℝ) k1 with hM
      have hMpos : 0 < M := lt_of_lt_of_le hk1pos (le_max_right _ _)
      have hlk : 1 + l u ≤ k1 := by
        rw [hk1]; push_cast; linarith [hl u huA]
      have hl1 : 0 ≤ 1 + l u := by linarith [hl0 u huA]
      have hb1 : 0 ≤ Ca * (1 + l u) / (n : ℝ) ^ (e + 6) :=
        div_nonneg (mul_nonneg hCa hl1) (by positivity)
      have hb2 : 0 ≤ Cb * (1 + l u) / k1 ^ (e + 7) :=
        div_nonneg (mul_nonneg hCb hl1) (by positivity)
      have hfrac : (1 + l u) ^ 2 / k1 ^ 2 ≤ 1 := by
        rw [div_le_one (by positivity)]
        exact pow_le_pow_left₀ hl1 hlk 2
      calc tw u * tx u * F u
          ≤ (Ca * (1 + l u) / (n : ℝ) ^ (e + 6)) * (Cb * (1 + l u) / k1 ^ (e + 7)) *
              (CF / M ^ (e + 3)) :=
            mul_le_mul (mul_le_mul (htw_near u huA hk) (htx_near u huA hk) (htx0 u huA) hb1)
              (hF u huA) (hF0 u huA) (mul_nonneg hb1 hb2)
        _ = Ca * Cb * CF / (n : ℝ) ^ (e + 6) * ((1 + l u) ^ 2 / k1 ^ 2) *
              (1 / (k1 ^ (e + 5) * M ^ (e + 3))) := by
            field_simp <;> ring
        _ ≤ Ca * Cb * CF / (n : ℝ) ^ (e + 6) * 1 * (1 / (k1 ^ (e + 5) * M ^ (e + 3))) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hfrac hK0) (by positivity)
        _ = _ := by ring
    have hsub : Ann.filter (fun u => linfDist x u < q) ⊆ linfBall x ((2 * n : ℕ) : ℤ) :=
      (Finset.filter_subset _ _).trans hAnn
    have hrad := radial_div_sum_le (show 1 ≤ e + 7 by omega) x (e + 5) (by omega)
      (show 1 ≤ e + 1 by omega) hr (2 * n)
    rw [show e + 7 - 1 - (e + 5) + (e + 1 + 1) = e + 3 by omega,
      show e + 7 - 1 = e + 6 by omega] at hrad
    calc _ ≤ ∑ u ∈ Ann.filter (fun u => linfDist x u < q),
          Ca * Cb * CF / (n : ℝ) ^ (e + 6) *
            (1 / (((linfDist x u + 1 : ℕ) : ℝ) ^ (e + 5) *
              (max (r : ℝ) ((linfDist x u + 1 : ℕ) : ℝ)) ^ (e + 3))) := Finset.sum_le_sum hpt
      _ = Ca * Cb * CF / (n : ℝ) ^ (e + 6) * ∑ u ∈ Ann.filter (fun u => linfDist x u < q),
            (1 / (((linfDist x u + 1 : ℕ) : ℝ) ^ (e + 5) *
              (max (r : ℝ) ((linfDist x u + 1 : ℕ) : ℝ)) ^ (e + 3))) := by
          rw [Finset.mul_sum]
      _ ≤ Ca * Cb * CF / (n : ℝ) ^ (e + 6) * ∑ u ∈ linfBall x ((2 * n : ℕ) : ℤ),
            (1 / (((linfDist x u + 1 : ℕ) : ℝ) ^ (e + 5) *
              (max (r : ℝ) ((linfDist x u + 1 : ℕ) : ℝ)) ^ (e + 3))) :=
          mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)) hK0
      _ ≤ _ := mul_le_mul_of_nonneg_left (by rw [hB]; exact hrad) hK0
  -- far from x
  have hfarS : ∑ u ∈ Ann.filter (fun u => ¬ linfDist x u < q), tw u * tx u * F u ≤
      Cτ * Cc * CF / ((n : ℝ) ^ (e + 6) * Q ^ (e + 3)) *
        (B * (((4 * n : ℕ) : ℝ) + 1) ^ 2) := by
    have hK0 : 0 ≤ Cτ * Cc * CF / ((n : ℝ) ^ (e + 6) * Q ^ (e + 3)) :=
      div_nonneg (mul_nonneg (mul_nonneg hCτ hCc) hCF) (by positivity)
    have hpt : ∀ u ∈ Ann.filter (fun u => ¬ linfDist x u < q), tw u * tx u * F u ≤
        Cτ * Cc * CF / ((n : ℝ) ^ (e + 6) * Q ^ (e + 3)) *
          (1 / ((linfDist w u + 1 : ℕ) : ℝ) ^ (e + 5)) := by
      intro u hu
      rw [Finset.mem_filter] at hu
      obtain ⟨huA, hk⟩ := hu
      have hQM : Q ≤ max (r : ℝ) ((linfDist x u + 1 : ℕ) : ℝ) := by
        refine le_max_of_le_right ?_
        rw [hQdef]; exact_mod_cast (show q + 1 ≤ linfDist x u + 1 by omega)
      have hF2 : F u ≤ CF / Q ^ (e + 3) :=
        (hF u huA).trans (div_le_div_of_nonneg_left hCF (by positivity)
          (pow_le_pow_left₀ hQpos.le hQM _))
      have hb1 : 0 ≤ Cτ / ((linfDist w u + 1 : ℕ) : ℝ) ^ (e + 5) :=
        div_nonneg hCτ (by positivity)
      have hb2 : 0 ≤ Cc / (n : ℝ) ^ (e + 6) := div_nonneg hCc (by positivity)
      calc tw u * tx u * F u
          ≤ (Cτ / ((linfDist w u + 1 : ℕ) : ℝ) ^ (e + 5)) * (Cc / (n : ℝ) ^ (e + 6)) *
              (CF / Q ^ (e + 3)) :=
            mul_le_mul (mul_le_mul (htw u huA) (htx_far u huA (by omega)) (htx0 u huA) hb1)
              hF2 (hF0 u huA) (mul_nonneg hb1 hb2)
        _ = _ := by field_simp <;> ring
    have hsub : Ann.filter (fun u => ¬ linfDist x u < q) ⊆ linfBall w ((4 * n : ℕ) : ℤ) := by
      intro u hu
      rw [Finset.mem_filter] at hu
      have hxu := (mem_linfBall_iff_dist x u (by positivity)).mp (hAnn hu.1)
      have hxw := (mem_linfBall_iff_dist x w (by positivity)).mp (hAnn hw)
      rw [mem_linfBall_iff_dist w u (by positivity)]
      have htri := linfDist_triangle w x u
      rw [linfDist_comm w x] at htri
      simp only [Int.toNat_natCast] at hxu hxw ⊢
      omega
    have hball := ball_inv_pow_sum (show 2 ≤ e + 7 by omega) w (4 * n)
    rw [show e + 7 - 2 = e + 5 by omega, show e + 7 - 1 = e + 6 by omega] at hball
    calc _ ≤ ∑ u ∈ Ann.filter (fun u => ¬ linfDist x u < q),
          Cτ * Cc * CF / ((n : ℝ) ^ (e + 6) * Q ^ (e + 3)) *
            (1 / ((linfDist w u + 1 : ℕ) : ℝ) ^ (e + 5)) := Finset.sum_le_sum hpt
      _ = Cτ * Cc * CF / ((n : ℝ) ^ (e + 6) * Q ^ (e + 3)) *
            ∑ u ∈ Ann.filter (fun u => ¬ linfDist x u < q),
              (1 / ((linfDist w u + 1 : ℕ) : ℝ) ^ (e + 5)) := by rw [Finset.mul_sum]
      _ ≤ Cτ * Cc * CF / ((n : ℝ) ^ (e + 6) * Q ^ (e + 3)) *
            ∑ u ∈ linfBall w ((4 * n : ℕ) : ℤ), (1 / ((linfDist w u + 1 : ℕ) : ℝ) ^ (e + 5)) :=
          mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)) hK0
      _ ≤ _ := mul_le_mul_of_nonneg_left (by rw [hB]; exact hball) hK0
  -- far-part scaling: (4n+1)²/Q^{e+3} ≤ 25·4^{e+3}/r^{e+1}
  have hscale : (((4 * n : ℕ) : ℝ) + 1) ^ 2 / Q ^ (e + 3) ≤ 25 * 4 ^ (e + 3) / (r : ℝ) ^ (e + 1) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h4 : (((4 * n : ℕ) : ℝ) + 1) ^ 2 ≤ 25 * (n : ℝ) ^ 2 := by
      push_cast; nlinarith
    have hrp : (r : ℝ) ^ (e + 1) ≤ (n : ℝ) ^ (e + 1) := pow_le_pow_left₀ hrpos.le hrn' _
    have hnp : (n : ℝ) ^ (e + 3) ≤ (4 * Q) ^ (e + 3) := pow_le_pow_left₀ hnpos.le hnQ _
    calc (((4 * n : ℕ) : ℝ) + 1) ^ 2 * (r : ℝ) ^ (e + 1)
        ≤ 25 * (n : ℝ) ^ 2 * (n : ℝ) ^ (e + 1) :=
          mul_le_mul h4 hrp (by positivity) (by positivity)
      _ = 25 * (n : ℝ) ^ (e + 3) := by ring
      _ ≤ 25 * (4 * Q) ^ (e + 3) := mul_le_mul_of_nonneg_left hnp (by norm_num)
      _ = 25 * 4 ^ (e + 3) * Q ^ (e + 3) := by rw [mul_pow]; ring
  have he1 : (0 : ℝ) < ((e + 1 : ℕ) : ℝ) := by positivity
  have hC2 : 0 ≤ Cτ * Cc * CF * B := mul_nonneg (mul_nonneg (mul_nonneg hCτ hCc) hCF) hB0
  calc _ ≤ Ca * Cb * CF / (n : ℝ) ^ (e + 6) *
          (B * ((((e + 1 : ℕ) : ℝ) + 1) / (((e + 1 : ℕ) : ℝ) * (r : ℝ) ^ (e + 1)))) +
        Cτ * Cc * CF / ((n : ℝ) ^ (e + 6) * Q ^ (e + 3)) *
          (B * (((4 * n : ℕ) : ℝ) + 1) ^ 2) := add_le_add hnear hfarS
    _ = Ca * Cb * CF * (B * ((((e + 1 : ℕ) : ℝ) + 1) / ((e + 1 : ℕ) : ℝ))) /
          ((n : ℝ) ^ (e + 6) * (r : ℝ) ^ (e + 1)) +
        Cτ * Cc * CF * B / (n : ℝ) ^ (e + 6) *
          ((((4 * n : ℕ) : ℝ) + 1) ^ 2 / Q ^ (e + 3)) := by
        field_simp <;> ring
    _ ≤ Ca * Cb * CF * (B * ((((e + 1 : ℕ) : ℝ) + 1) / ((e + 1 : ℕ) : ℝ))) /
          ((n : ℝ) ^ (e + 6) * (r : ℝ) ^ (e + 1)) +
        Cτ * Cc * CF * B / (n : ℝ) ^ (e + 6) * (25 * 4 ^ (e + 3) / (r : ℝ) ^ (e + 1)) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hscale (div_nonneg hC2 (by positivity)))
    _ = _ := by rw [hB]; field_simp <;> ring

/-- Coefficient of the inner estimate for the first diagram. -/
noncomputable def varTermOneInnerConstant (e : ℕ) (Cg Ca Cb Cc Cτ CF : ℝ) : ℝ :=
  Cg * (CF * 4 ^ (e + 3)) *
    (Ca * Cb * CF * (2 * ((e + 7 : ℕ) : ℝ) * 3 ^ (e + 6) *
        ((((e + 1 : ℕ) : ℝ) + 1) / ((e + 1 : ℕ) : ℝ))) +
      Cτ * Cc * CF * (2 * ((e + 7 : ℕ) : ℝ) * 3 ^ (e + 6)) * (25 * 4 ^ (e + 3))) *
    (2 * ((e + 7 : ℕ) : ℝ) * 3 ^ (e + 6) * 2 * 2 ^ (e + 6))

/-- `hcase2` of `var_term_1`. -/
theorem var_term_1_case2 {e : ℕ} (x : Fin (e + 7) → ℤ) {n r q c : ℕ} (hn : 1 ≤ n)
    (hr : 1 ≤ r) (hrn : r ≤ n) (hq : n ≤ 4 * (q + 1))
    (Ann outer : Finset (Fin (e + 7) → ℤ))
    (hAnn_ball : Ann ⊆ linfBall x ((2 * n : ℕ) : ℤ))
    (hAnn0 : Ann ⊆ linfBall (0 : Fin (e + 7) → ℤ) (n : ℤ))
    (hfar : ∀ w ∈ Ann \ outer, 2 * q ≤ linfDist x w)
    (g F l : (Fin (e + 7) → ℤ) → ℝ) (tau : (Fin (e + 7) → ℤ) → (Fin (e + 7) → ℤ) → ℝ)
    {Cg Ca Cb Cc Cτ CF : ℝ} (hCg : 0 ≤ Cg) (hCa : 0 ≤ Ca) (hCb : 0 ≤ Cb) (hCc : 0 ≤ Cc)
    (hCτ : 0 ≤ Cτ) (hCF : 0 ≤ CF)
    (hg0 : ∀ w ∈ Ann \ outer, 0 ≤ g w) (hF0 : ∀ u ∈ Ann, 0 ≤ F u)
    (htw0 : ∀ w ∈ Ann \ outer, ∀ u ∈ Ann, 0 ≤ tau w u) (htx0 : ∀ u ∈ Ann, 0 ≤ tau u x)
    (hl0 : ∀ u ∈ Ann, 0 ≤ l u) (hl : ∀ u ∈ Ann, l u ≤ (linfDist x u : ℝ))
    (hg : ∀ w ∈ Ann \ outer,
      g w ≤ Cg / ((linfDist (0 : Fin (e + 7) → ℤ) w + 1 - c : ℕ) : ℝ) ^ 2)
    (hF : ∀ u ∈ Ann, F u ≤ CF / (max (r : ℝ) ((linfDist x u + 1 : ℕ) : ℝ)) ^ (e + 3))
    (htw_near : ∀ w ∈ Ann \ outer, ∀ u ∈ Ann, linfDist x u < q →
      tau w u ≤ Ca * (1 + l u) / (n : ℝ) ^ (e + 6))
    (htw : ∀ w ∈ Ann \ outer, ∀ u ∈ Ann,
      tau w u ≤ Cτ / ((linfDist w u + 1 : ℕ) : ℝ) ^ (e + 5))
    (htx_near : ∀ u ∈ Ann, linfDist x u < q →
      tau u x ≤ Cb * (1 + l u) / ((linfDist x u + 1 : ℕ) : ℝ) ^ (e + 7))
    (htx_far : ∀ u ∈ Ann, q ≤ linfDist x u → tau u x ≤ Cc / (n : ℝ) ^ (e + 6)) :
    (n : ℝ) ^ 3 * ∑ u ∈ Ann, ∑ w ∈ Ann \ outer, g w * tau w u * tau u x * F w * F u ≤
      Cg * (CF * 4 ^ (e + 3)) *
        (Ca * Cb * CF * (2 * ((e + 7 : ℕ) : ℝ) * 3 ^ (e + 6) *
            ((((e + 1 : ℕ) : ℝ) + 1) / ((e + 1 : ℕ) : ℝ))) +
          Cτ * Cc * CF * (2 * ((e + 7 : ℕ) : ℝ) * 3 ^ (e + 6)) * (25 * 4 ^ (e + 3))) *
        (2 * ((e + 7 : ℕ) : ℝ) * 3 ^ (e + 6) * 2 * 2 ^ (e + 6)) / (r : ℝ) ^ (e + 1) := by
  set D : ℝ := Ca * Cb * CF * (2 * ((e + 7 : ℕ) : ℝ) * 3 ^ (e + 6) *
      ((((e + 1 : ℕ) : ℝ) + 1) / ((e + 1 : ℕ) : ℝ))) +
    Cτ * Cc * CF * (2 * ((e + 7 : ℕ) : ℝ) * 3 ^ (e + 6)) * (25 * 4 ^ (e + 3)) with hD
  have hD0 : 0 ≤ D := by
    rw [hD]
    exact add_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hCa hCb) hCF) (by positivity))
      (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hCτ hCc) hCF) (by positivity))
        (by positivity))
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hrpos : (0 : ℝ) < r := by linarith
  have hQpos : (0 : ℝ) < (q : ℝ) + 1 := by positivity
  have hnQ : (n : ℝ) ≤ 4 * ((q : ℝ) + 1) := by exact_mod_cast hq
  -- swap the sums and factor out Ψ
  have hswap : ∑ u ∈ Ann, ∑ w ∈ Ann \ outer, g w * tau w u * tau u x * F w * F u =
      ∑ w ∈ Ann \ outer, g w * F w * ∑ u ∈ Ann, tau w u * tau u x * F u := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun w _ => ?_)
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun u _ => by ring)
  set K : ℝ := Cg * (CF * 4 ^ (e + 3)) * D /
    ((n : ℝ) ^ (e + 3) * ((n : ℝ) ^ (e + 6) * (r : ℝ) ^ (e + 1))) with hK
  have hK0 : 0 ≤ K := by
    rw [hK]; exact div_nonneg (mul_nonneg (mul_nonneg hCg (by positivity)) hD0) (by positivity)
  have hpt : ∀ w ∈ Ann \ outer, g w * F w * ∑ u ∈ Ann, tau w u * tau u x * F u ≤
      K * ((1 : ℝ) / ((linfDist (0 : Fin (e + 7) → ℤ) w + 1 - c : ℕ) : ℝ) ^ 2) := by
    intro w hw
    have hwA : w ∈ Ann := (Finset.mem_sdiff.mp hw).1
    have hΨ := psi_bound hn hr hrn hq Ann hAnn_ball hwA (hfar w hw) (tau w) (fun u => tau u x)
      F l hCa hCb hCc hCτ hCF (htw0 w hw) htx0 hF0 hl0 hl hF (htw_near w hw) (htw w hw)
      htx_near htx_far
    rw [← hD] at hΨ
    have hΨ0 : 0 ≤ ∑ u ∈ Ann, tau w u * tau u x * F u :=
      Finset.sum_nonneg (fun u hu => mul_nonneg (mul_nonneg (htw0 w hw u hu) (htx0 u hu))
        (hF0 u hu))
    have hQM : (q : ℝ) + 1 ≤ max (r : ℝ) ((linfDist x w + 1 : ℕ) : ℝ) := by
      refine le_max_of_le_right ?_
      exact_mod_cast (show q + 1 ≤ linfDist x w + 1 by have := hfar w hw; omega)
    have hFw : F w ≤ CF * 4 ^ (e + 3) / (n : ℝ) ^ (e + 3) := by
      calc F w ≤ CF / (max (r : ℝ) ((linfDist x w + 1 : ℕ) : ℝ)) ^ (e + 3) := hF w hwA
        _ ≤ CF / ((q : ℝ) + 1) ^ (e + 3) :=
            div_le_div_of_nonneg_left hCF (by positivity) (pow_le_pow_left₀ hQpos.le hQM _)
        _ = CF * (1 / ((q : ℝ) + 1) ^ (e + 3)) := by ring
        _ ≤ CF * (4 ^ (e + 3) / (n : ℝ) ^ (e + 3)) :=
            mul_le_mul_of_nonneg_left (inv_pow_le_of_le_four_mul hn hQpos hnQ _) hCF
        _ = _ := by ring
    have hgB0 : 0 ≤ Cg / ((linfDist (0 : Fin (e + 7) → ℤ) w + 1 - c : ℕ) : ℝ) ^ 2 :=
      div_nonneg hCg (by positivity)
    have hFB0 : 0 ≤ CF * 4 ^ (e + 3) / (n : ℝ) ^ (e + 3) := div_nonneg (by positivity) (by positivity)
    calc g w * F w * ∑ u ∈ Ann, tau w u * tau u x * F u
        ≤ (Cg / ((linfDist (0 : Fin (e + 7) → ℤ) w + 1 - c : ℕ) : ℝ) ^ 2) *
            (CF * 4 ^ (e + 3) / (n : ℝ) ^ (e + 3)) *
            (D / ((n : ℝ) ^ (e + 6) * (r : ℝ) ^ (e + 1))) :=
          mul_le_mul (mul_le_mul (hg w hw) hFw (hF0 w hwA) hgB0) hΨ hΨ0 (mul_nonneg hgB0 hFB0)
      _ = _ := by rw [hK]; field_simp <;> ring
  have hinner := inner_sum_count (show 1 ≤ e + 7 by omega) c n
  rw [show e + 7 - 1 = e + 6 by omega] at hinner
  have hsub : Ann \ outer ⊆ linfBall (0 : Fin (e + 7) → ℤ) (n : ℤ) :=
    Finset.sdiff_subset.trans hAnn0
  have hsum : ∑ w ∈ Ann \ outer, g w * F w * ∑ u ∈ Ann, tau w u * tau u x * F u ≤
      K * (2 * ((e + 7 : ℕ) : ℝ) * 3 ^ (e + 6) * ((n : ℝ) + 1) ^ (e + 6) * 2) := by
    calc _ ≤ ∑ w ∈ Ann \ outer,
          K * ((1 : ℝ) / ((linfDist (0 : Fin (e + 7) → ℤ) w + 1 - c : ℕ) : ℝ) ^ 2) :=
          Finset.sum_le_sum hpt
      _ = K * ∑ w ∈ Ann \ outer,
          (1 : ℝ) / ((linfDist (0 : Fin (e + 7) → ℤ) w + 1 - c : ℕ) : ℝ) ^ 2 := by
          rw [Finset.mul_sum]
      _ ≤ K * ∑ w ∈ linfBall (0 : Fin (e + 7) → ℤ) (n : ℤ),
          (1 : ℝ) / ((linfDist (0 : Fin (e + 7) → ℤ) w + 1 - c : ℕ) : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)) hK0
      _ ≤ _ := mul_le_mul_of_nonneg_left hinner hK0
  have hscale : (n : ℝ) ^ 3 * ((n : ℝ) + 1) ^ (e + 6) / ((n : ℝ) ^ (e + 3) * (n : ℝ) ^ (e + 6))
      ≤ 2 ^ (e + 6) := by
    rw [div_le_iff₀ (by positivity)]
    have hp : ((n : ℝ) + 1) ^ (e + 6) ≤ (2 * (n : ℝ)) ^ (e + 6) :=
      pow_le_pow_left₀ (by positivity) (by linarith) _
    have hn3 : (n : ℝ) ^ 3 ≤ (n : ℝ) ^ (e + 3) := pow_le_pow_right₀ hn1 (by omega)
    calc (n : ℝ) ^ 3 * ((n : ℝ) + 1) ^ (e + 6) ≤ (n : ℝ) ^ (e + 3) * (2 * (n : ℝ)) ^ (e + 6) :=
          mul_le_mul hn3 hp (by positivity) (by positivity)
      _ = _ := by rw [mul_pow]; ring
  have hA0 : 0 ≤ Cg * (CF * 4 ^ (e + 3)) * D * (2 * ((e + 7 : ℕ) : ℝ) * 3 ^ (e + 6) * 2) /
      (r : ℝ) ^ (e + 1) :=
    div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hCg (by positivity)) hD0) (by positivity))
      (by positivity)
  rw [hswap]
  calc _ ≤ (n : ℝ) ^ 3 * (K * (2 * ((e + 7 : ℕ) : ℝ) * 3 ^ (e + 6) * ((n : ℝ) + 1) ^ (e + 6) * 2)) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = Cg * (CF * 4 ^ (e + 3)) * D * (2 * ((e + 7 : ℕ) : ℝ) * 3 ^ (e + 6) * 2) /
          (r : ℝ) ^ (e + 1) *
        ((n : ℝ) ^ 3 * ((n : ℝ) + 1) ^ (e + 6) / ((n : ℝ) ^ (e + 3) * (n : ℝ) ^ (e + 6))) := by
        rw [hK]; field_simp <;> ring
    _ ≤ Cg * (CF * 4 ^ (e + 3)) * D * (2 * ((e + 7 : ℕ) : ℝ) * 3 ^ (e + 6) * 2) /
          (r : ℝ) ^ (e + 1) * 2 ^ (e + 6) := mul_le_mul_of_nonneg_left hscale hA0
    _ = _ := by rw [hD]; field_simp <;> ring

/-- prop.var_term_1 with its inner case (`hcase2`) discharged by `var_term_1_case2`. -/
theorem var_term_1_source_bound {e : ℕ} (x : Fin (e + 7) → ℤ) {n r q c : ℕ} (hn : 1 ≤ n)
    (hr : 1 ≤ r) (hrn : r ≤ n) (hq : n ≤ 4 * (q + 1))
    (Ann outer : Finset (Fin (e + 7) → ℤ)) (houter_sub : outer ⊆ Ann)
    (hAnn_ball : Ann ⊆ linfBall x ((2 * n : ℕ) : ℤ))
    (hAnn0 : Ann ⊆ linfBall (0 : Fin (e + 7) → ℤ) (n : ℤ))
    (hfar : ∀ w ∈ Ann \ outer, 2 * q ≤ linfDist x w)
    (g F l : (Fin (e + 7) → ℤ) → ℝ) (tau : (Fin (e + 7) → ℤ) → (Fin (e + 7) → ℤ) → ℝ)
    {Cphi Cg Ca Cb Cc Cτ CF : ℝ} (hCphi : 0 ≤ Cphi) (hCg : 0 ≤ Cg) (hCa : 0 ≤ Ca)
    (hCb : 0 ≤ Cb) (hCc : 0 ≤ Cc) (hCτ : 0 ≤ Cτ) (hCF : 0 ≤ CF)
    (hphi : ∀ u ∈ Ann,
        (n : ℝ) ^ 3 * (∑ w ∈ outer, g w * tau w u * tau u x * F w * F u)
          ≤ Cphi * (1 / (((linfDist x u + 1 : ℕ) : ℝ) ^ (e + 7 - 2)
              * (max (r : ℝ) ((linfDist x u + 1 : ℕ) : ℝ)) ^ (2 * (e + 7) - 10))))
    (hg0 : ∀ w ∈ Ann \ outer, 0 ≤ g w) (hF0 : ∀ u ∈ Ann, 0 ≤ F u)
    (htw0 : ∀ w ∈ Ann \ outer, ∀ u ∈ Ann, 0 ≤ tau w u) (htx0 : ∀ u ∈ Ann, 0 ≤ tau u x)
    (hl0 : ∀ u ∈ Ann, 0 ≤ l u) (hl : ∀ u ∈ Ann, l u ≤ (linfDist x u : ℝ))
    (hg : ∀ w ∈ Ann \ outer,
      g w ≤ Cg / ((linfDist (0 : Fin (e + 7) → ℤ) w + 1 - c : ℕ) : ℝ) ^ 2)
    (hF : ∀ u ∈ Ann, F u ≤ CF / (max (r : ℝ) ((linfDist x u + 1 : ℕ) : ℝ)) ^ (e + 3))
    (htw_near : ∀ w ∈ Ann \ outer, ∀ u ∈ Ann, linfDist x u < q →
      tau w u ≤ Ca * (1 + l u) / (n : ℝ) ^ (e + 6))
    (htw : ∀ w ∈ Ann \ outer, ∀ u ∈ Ann,
      tau w u ≤ Cτ / ((linfDist w u + 1 : ℕ) : ℝ) ^ (e + 5))
    (htx_near : ∀ u ∈ Ann, linfDist x u < q →
      tau u x ≤ Cb * (1 + l u) / ((linfDist x u + 1 : ℕ) : ℝ) ^ (e + 7))
    (htx_far : ∀ u ∈ Ann, q ≤ linfDist x u → tau u x ≤ Cc / (n : ℝ) ^ (e + 6)) :
    (n : ℝ) ^ 3 * ∑ u ∈ Ann, ∑ w ∈ Ann, g w * tau w u * tau u x * F w * F u
      ≤ (Cphi * varOuterRadialConstant (e + 7) + varTermOneInnerConstant e Cg Ca Cb Cc Cτ CF) / (r : ℝ) ^ (e + 7 - 6) := by
  have h2 := var_term_1_case2 x hn hr hrn hq Ann outer hAnn_ball hAnn0 hfar g F l tau
    hCg hCa hCb hCc hCτ hCF hg0 hF0 htw0 htx0 hl0 hl hg hF htw_near htw htx_near htx_far
  rw [show e + 1 = e + 7 - 6 by omega] at h2
  exact var_term_1_bound (d := e + 7) (by omega) x hr hrn Ann outer g F tau Cphi
    (varTermOneInnerConstant e Cg Ca Cb Cc Cτ CF) hCphi
    (by unfold varTermOneInnerConstant; positivity) houter_sub hAnn_ball hphi h2

/-- Existential form of the source first diagram bound. -/
theorem var_term_1_source {e : ℕ} (x : Fin (e + 7) → ℤ) {n r q c : ℕ} (hn : 1 ≤ n)
    (hr : 1 ≤ r) (hrn : r ≤ n) (hq : n ≤ 4 * (q + 1))
    (Ann outer : Finset (Fin (e + 7) → ℤ)) (houter_sub : outer ⊆ Ann)
    (hAnn_ball : Ann ⊆ linfBall x ((2 * n : ℕ) : ℤ))
    (hAnn0 : Ann ⊆ linfBall (0 : Fin (e + 7) → ℤ) (n : ℤ))
    (hfar : ∀ w ∈ Ann \ outer, 2 * q ≤ linfDist x w)
    (g F l : (Fin (e + 7) → ℤ) → ℝ) (tau : (Fin (e + 7) → ℤ) → (Fin (e + 7) → ℤ) → ℝ)
    {Cphi Cg Ca Cb Cc Cτ CF : ℝ} (hCphi : 0 ≤ Cphi) (hCg : 0 ≤ Cg) (hCa : 0 ≤ Ca)
    (hCb : 0 ≤ Cb) (hCc : 0 ≤ Cc) (hCτ : 0 ≤ Cτ) (hCF : 0 ≤ CF)
    (hphi : ∀ u ∈ Ann,
        (n : ℝ) ^ 3 * (∑ w ∈ outer, g w * tau w u * tau u x * F w * F u)
          ≤ Cphi * (1 / (((linfDist x u + 1 : ℕ) : ℝ) ^ (e + 7 - 2)
              * (max (r : ℝ) ((linfDist x u + 1 : ℕ) : ℝ)) ^ (2 * (e + 7) - 10))))
    (hg0 : ∀ w ∈ Ann \ outer, 0 ≤ g w) (hF0 : ∀ u ∈ Ann, 0 ≤ F u)
    (htw0 : ∀ w ∈ Ann \ outer, ∀ u ∈ Ann, 0 ≤ tau w u) (htx0 : ∀ u ∈ Ann, 0 ≤ tau u x)
    (hl0 : ∀ u ∈ Ann, 0 ≤ l u) (hl : ∀ u ∈ Ann, l u ≤ (linfDist x u : ℝ))
    (hg : ∀ w ∈ Ann \ outer,
      g w ≤ Cg / ((linfDist (0 : Fin (e + 7) → ℤ) w + 1 - c : ℕ) : ℝ) ^ 2)
    (hF : ∀ u ∈ Ann, F u ≤ CF / (max (r : ℝ) ((linfDist x u + 1 : ℕ) : ℝ)) ^ (e + 3))
    (htw_near : ∀ w ∈ Ann \ outer, ∀ u ∈ Ann, linfDist x u < q →
      tau w u ≤ Ca * (1 + l u) / (n : ℝ) ^ (e + 6))
    (htw : ∀ w ∈ Ann \ outer, ∀ u ∈ Ann,
      tau w u ≤ Cτ / ((linfDist w u + 1 : ℕ) : ℝ) ^ (e + 5))
    (htx_near : ∀ u ∈ Ann, linfDist x u < q →
      tau u x ≤ Cb * (1 + l u) / ((linfDist x u + 1 : ℕ) : ℝ) ^ (e + 7))
    (htx_far : ∀ u ∈ Ann, q ≤ linfDist x u → tau u x ≤ Cc / (n : ℝ) ^ (e + 6)) :
    ∃ C : ℝ, 0 ≤ C ∧
      (n : ℝ) ^ 3 * ∑ u ∈ Ann, ∑ w ∈ Ann, g w * tau w u * tau u x * F w * F u
        ≤ C / (r : ℝ) ^ (e + 7 - 6) := by
  have hA : 0 ≤ varOuterRadialConstant (e + 7) := by unfold varOuterRadialConstant; positivity
  have hinner : 0 ≤ varTermOneInnerConstant e Cg Ca Cb Cc Cτ CF := by
    unfold varTermOneInnerConstant
    positivity
  exact ⟨Cphi * varOuterRadialConstant (e + 7) + varTermOneInnerConstant e Cg Ca Cb Cc Cτ CF,
    by positivity, var_term_1_source_bound x hn hr hrn hq Ann outer houter_sub hAnn_ball hAnn0
      hfar g F l tau hCphi hCg hCa hCb hCc hCτ hCF hphi hg0 hF0 htw0 htx0 hl0 hl hg hF
      htw_near htw htx_near htx_far⟩

end NearCritical.AppendixVariance
