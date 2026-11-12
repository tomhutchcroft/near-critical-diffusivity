module

public import NearCritical.AppendixShellCount

/-! Appendix B, Proposition `prop.var_term_4` (source/main.tex, statement line 6871,
proof 7073-7090): `∑_{w∈Ann_{c1n}} g(w) F_i(w)^2 ≲_{c1} r^{6-d}`.

This is a FAITHFUL conditional reduction, in the project convention of taking the
standard Appendix-A / main-text inputs as EXPLICIT hypotheses:

* the outer region `Λ_n \ Λ_{n/2}` (here `outer`) contributes, after the `g`-bound
  `g(w) ≲ (1+l_w) n^{-3} ≤ (1+|x-w|) n^{-3}` (`eq.g_outer`) and the pointwise `F`-bound
  `F_i(w) ≲ max{r,|x-w|}^{4-d}` (`eq.F_pointwise`), a per-point product bounded by the
  radial kernel `n^{-3} · (|x-w|_∞+1) · max(r,|x-w|_∞+1)^{-(2d-8)}` — hypothesis
  `hptwise`. Summing this over the ℓ∞ ball is EXACTLY the verified
  `radial_weighted_power_sum_le` (with weight `a = 1`, tail exponent `t = d-9`), giving
  `≲ n^{-3} r^{9-d} ≤ r^{6-d}` (using `n ≥ r`). This step is fully proved here.
* the inner contributions (Cases 2,3: `RD_{c1n}` and `(Ann∩Λ_{n/2})\RD`) use the
  remote-distance counting bound `eq.RD_count` (`∑ s_w^{-2} ≲ n^{d-2} log n`), which is a
  separate lattice-counting input not yet formalized; its aggregate output
  `∑_{Ann\outer} g F^2 ≲ r^{6-d}` is taken as the explicit hypothesis `hinner`.

So the ANALYTIC core of var_term_4 (the outer radial sum) is discharged against the
verified Appendix-B engine; the proposition is reduced to the two genuine standard inputs
`hptwise` (Appendix-A pointwise kernel bound) and `hinner` (the RD_count estimate). The
`∃ C, 0 ≤ C ∧ … ≤ C / r^{d-6}` conclusion is the faithful reading of `≲_{c1} r^{6-d}`
(for `d ≥ 10`, where the clean `r^{9-d}` tail converges). -/
@[expose] public section
namespace NearCritical.AppendixVariance
open scoped BigOperators

/-- Proposition `prop.var_term_4`: `∑_{w∈Ann} g(w) F(w)^2 ≲ r^{6-d}`, reduced to the
outer-region radial kernel bound (`hptwise`, discharged via `radial_weighted_power_sum_le`)
and the inner `RD_count`-based estimate (`hinner`). -/
theorem var_term_4
    {d : ℕ} (hd : 10 ≤ d) (x : Fin d → ℤ) {n r : ℕ}
    (hr : 1 ≤ r) (hrn : r ≤ n)
    (Ann outer : Finset (Fin d → ℤ)) (g F : (Fin d → ℤ) → ℝ)
    (Cin : ℝ) (hCin : 0 ≤ Cin)
    (houter_sub : outer ⊆ Ann)
    (houter_ball : outer ⊆ linfBall x ((2 * n : ℕ) : ℤ))
    (hptwise : ∀ w ∈ outer, g w * F w ^ 2
        ≤ ((n : ℝ) ^ 3)⁻¹
            * (((linfDist x w + 1 : ℕ) : ℝ)
                / (max (r : ℝ) ((linfDist x w + 1 : ℕ) : ℝ)) ^ (2 * d - 8)))
    (hinner : ∑ w ∈ Ann \ outer, g w * F w ^ 2 ≤ Cin / (r : ℝ) ^ (d - 6)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∑ w ∈ Ann, g w * F w ^ 2 ≤ C / (r : ℝ) ^ (d - 6) := by
  set t : ℕ := d - 9 with htdef
  have ht1 : 1 ≤ t := by omega
  have hr0 : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have hrne : (r : ℝ) ≠ 0 := ne_of_gt hr0
  have htne : (t : ℝ) ≠ 0 := by
    have ht0 : t ≠ 0 := by omega
    exact_mod_cast ht0
  refine ⟨2 * (d : ℝ) * 3 ^ (d - 1) * (((t : ℝ) + 1) / (t : ℝ)) + Cin, ?_, ?_⟩
  · have : (0 : ℝ) ≤ 2 * (d : ℝ) * 3 ^ (d - 1) * (((t : ℝ) + 1) / (t : ℝ)) :=
      mul_nonneg (by positivity) (div_nonneg (by positivity) (by positivity))
    linarith
  · have houter_bound : ∑ w ∈ outer, g w * F w ^ 2
        ≤ 2 * (d : ℝ) * 3 ^ (d - 1) * (((t : ℝ) + 1) / (t : ℝ)) / (r : ℝ) ^ (d - 6) := by
      have htool := radial_weighted_power_sum_le (show 1 ≤ d by omega) x 1 ht1 hr (2 * n)
      simp only [pow_one, show 1 + (d - 1) + (t + 1) = 2 * d - 8 by omega] at htool
      calc ∑ w ∈ outer, g w * F w ^ 2
          ≤ ∑ w ∈ outer, ((n : ℝ) ^ 3)⁻¹
              * (((linfDist x w + 1 : ℕ) : ℝ)
                  / (max (r : ℝ) ((linfDist x w + 1 : ℕ) : ℝ)) ^ (2 * d - 8)) :=
            Finset.sum_le_sum (fun w hw => hptwise w hw)
        _ = ((n : ℝ) ^ 3)⁻¹ * ∑ w ∈ outer,
              (((linfDist x w + 1 : ℕ) : ℝ)
                / (max (r : ℝ) ((linfDist x w + 1 : ℕ) : ℝ)) ^ (2 * d - 8)) := by
            rw [← Finset.mul_sum]
        _ ≤ ((n : ℝ) ^ 3)⁻¹ * ∑ w ∈ linfBall x ((2 * n : ℕ) : ℤ),
              (((linfDist x w + 1 : ℕ) : ℝ)
                / (max (r : ℝ) ((linfDist x w + 1 : ℕ) : ℝ)) ^ (2 * d - 8)) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact Finset.sum_le_sum_of_subset_of_nonneg houter_ball (fun w _ _ => by positivity)
        _ ≤ ((n : ℝ) ^ 3)⁻¹
              * (2 * (d : ℝ) * 3 ^ (d - 1) * (((t : ℝ) + 1) / ((t : ℝ) * (r : ℝ) ^ t))) :=
            mul_le_mul_of_nonneg_left htool (by positivity)
        _ ≤ ((r : ℝ) ^ 3)⁻¹
              * (2 * (d : ℝ) * 3 ^ (d - 1) * (((t : ℝ) + 1) / ((t : ℝ) * (r : ℝ) ^ t))) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            have h3 : (r : ℝ) ^ 3 ≤ (n : ℝ) ^ 3 :=
              pow_le_pow_left₀ hr0.le (by exact_mod_cast hrn) 3
            rw [inv_eq_one_div, inv_eq_one_div]
            exact one_div_le_one_div_of_le (pow_pos hr0 3) h3
        _ = 2 * (d : ℝ) * 3 ^ (d - 1) * (((t : ℝ) + 1) / (t : ℝ)) / (r : ℝ) ^ (d - 6) := by
            rw [show d - 6 = 3 + t by omega, pow_add]
            field_simp
    calc ∑ w ∈ Ann, g w * F w ^ 2
        = ∑ w ∈ Ann \ outer, g w * F w ^ 2 + ∑ w ∈ outer, g w * F w ^ 2 :=
          (Finset.sum_sdiff houter_sub).symm
      _ ≤ Cin / (r : ℝ) ^ (d - 6)
          + 2 * (d : ℝ) * 3 ^ (d - 1) * (((t : ℝ) + 1) / (t : ℝ)) / (r : ℝ) ^ (d - 6) :=
          add_le_add hinner houter_bound
      _ = (2 * (d : ℝ) * 3 ^ (d - 1) * (((t : ℝ) + 1) / (t : ℝ)) + Cin) / (r : ℝ) ^ (d - 6) := by
          ring

end NearCritical.AppendixVariance
