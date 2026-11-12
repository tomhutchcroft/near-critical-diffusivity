module

public import NearCritical.AppendixShellCount

/-! Appendix B, Proposition `prop.var_term_2` (source/main.tex, statement 6857, proof
7015-7040): `n^3 ∑_{u,w∈Ann_{c1n}} g(u) τ(u,w) τ(u,x) F_i(w)^2 ≲_{c1} r^{6-d}`.

FAITHFUL conditional reduction (project convention: standard inputs as explicit
hypotheses). The sum over `u` is split into the outer region `Λ_n\Λ_{n/2}` (`outer`) and
the inner region `Ann∩Λ_{n/2}` (`Ann\outer`):

* Outer (Case 1): the source combines `eq.g_outer` (`n^3 g(u) ≲ 1+|x-u|`), the two-point
  bounds `lem.box_twopoint_onesided/twosided`, and the standard bubble (convolution)
  estimate `∑_u (1+|x-u|)^{2-d}(1+|u-w|)^{2-d} ≲ (1+|x-w|)^{4-d}`, together with
  `F(w)^2 ≲ max{r,|x-w|}^{8-2d}`, into a per-`w` bound of the inner `u`-sum by the radial
  kernel `(1+|x-w|)^{4-d} max{r,|x-w|}^{8-2d} = 1/((|x-w|_∞+1)^{d-4} max(r,·)^{2d-8})`
  (hypothesis `hbubble`). Summing this over the ℓ∞ ball is EXACTLY the verified
  `radial_div_sum_le` (with `p = d-4`, tail `t = 2d-12`), giving `≲ r^{12-2d} ≤ r^{6-d}`
  (`d ≥ 6`). This outer step — the sum-swap, the shell sum, and the exponent bookkeeping —
  is FULLY PROVED here against the verified Appendix-B engine.
* Inner (Case 2): bounded by `n^{6-d} ≤ r^{6-d}` via `eq.inner_sum` + the `Θ`-estimate;
  its aggregate `n^3 ∑_{u∈Ann\outer} … ≤ Cin/r^{d-6}` is taken as hypothesis `hcase2`.

So the genuine analytic content of the outer region (reduction to the verified radial sum)
is discharged here; the proposition is reduced to the two standard inputs `hbubble`
(Appendix-A two-point/bubble + `F`-bounds) and `hcase2` (`eq.inner_sum`). The
`∃ C, 0 ≤ C ∧ … ≤ C/r^{d-6}` conclusion is the faithful reading of `≲_{c1} r^{6-d}`,
for `d ≥ 7`. -/
@[expose] public section
namespace NearCritical.AppendixVariance
open scoped BigOperators

/-- Radial coefficient for the outer regions of the first two variance sums. -/
noncomputable def varOuterRadialConstant (d : ℕ) : ℝ :=
  2 * (d : ℝ) * 3 ^ (d - 1) * (((2 * d - 12 : ℕ) : ℝ) + 1) /
    ((2 * d - 12 : ℕ) : ℝ)

/-- Proposition `prop.var_term_2`, reduced to the outer bubble/kernel bound (`hbubble`,
discharged via `radial_div_sum_le`) and the inner `eq.inner_sum` estimate (`hcase2`). -/
theorem var_term_2_bound
    {d : ℕ} (hd : 7 ≤ d) (x : Fin d → ℤ) {n r : ℕ} (hr : 1 ≤ r) (_hrn : r ≤ n)
    (Ann outer : Finset (Fin d → ℤ))
    (g F : (Fin d → ℤ) → ℝ) (tau : (Fin d → ℤ) → (Fin d → ℤ) → ℝ)
    (Cbub Cin : ℝ) (hCbub : 0 ≤ Cbub) (_hCin : 0 ≤ Cin)
    (houter_sub : outer ⊆ Ann)
    (hAnn_ball : Ann ⊆ linfBall x ((2 * n : ℕ) : ℤ))
    (hbubble : ∀ w ∈ Ann,
        (n : ℝ) ^ 3 * ((∑ u ∈ outer, g u * tau u w * tau u x) * F w ^ 2)
          ≤ Cbub * (1 / (((linfDist x w + 1 : ℕ) : ℝ) ^ (d - 4)
              * (max (r : ℝ) ((linfDist x w + 1 : ℕ) : ℝ)) ^ (2 * d - 8))))
    (hcase2 : (n : ℝ) ^ 3 * ∑ u ∈ Ann \ outer, ∑ w ∈ Ann, g u * tau u w * tau u x * F w ^ 2
          ≤ Cin / (r : ℝ) ^ (d - 6)) :
    (n : ℝ) ^ 3 * ∑ u ∈ Ann, ∑ w ∈ Ann, g u * tau u w * tau u x * F w ^ 2
      ≤ (Cbub * varOuterRadialConstant d + Cin) / (r : ℝ) ^ (d - 6) := by
  have hr0 : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have hr1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hrne : (r : ℝ) ≠ 0 := ne_of_gt hr0
  have hBne : ((2 * d - 12 : ℕ) : ℝ) ≠ 0 := by
    have : 2 * d - 12 ≠ 0 := by omega
    exact_mod_cast this
  -- abbreviation for the outer constant
  set A : ℝ := varOuterRadialConstant d with hA_def
  have hA0 : 0 ≤ A := by
    rw [hA_def, varOuterRadialConstant]; exact div_nonneg (by positivity) (by positivity)
  -- the verified radial sum over the ball, put in the form A / r^{2d-12}
  have hrad : ∑ w ∈ linfBall x ((2 * n : ℕ) : ℤ),
        1 / (((linfDist x w + 1 : ℕ) : ℝ) ^ (d - 4)
            * (max (r : ℝ) ((linfDist x w + 1 : ℕ) : ℝ)) ^ (2 * d - 8))
      ≤ A / (r : ℝ) ^ (2 * d - 12) := by
    have h := radial_div_sum_le (show 1 ≤ d by omega) x (d - 4) (by omega)
      (show 1 ≤ 2 * d - 12 by omega) hr (2 * n)
    simp only [show (d - 1) - (d - 4) + (2 * d - 12 + 1) = 2 * d - 8 by omega] at h
    refine h.trans (le_of_eq ?_)
    rw [hA_def, varOuterRadialConstant]; field_simp
  -- power conversion r^{12-2d} ≤ r^{6-d}
  have hconv : ∀ a : ℝ, 0 ≤ a → a / (r : ℝ) ^ (2 * d - 12) ≤ a / (r : ℝ) ^ (d - 6) := by
    intro a ha
    rw [div_eq_mul_inv, div_eq_mul_inv]
    apply mul_le_mul_of_nonneg_left _ ha
    rw [inv_eq_one_div, inv_eq_one_div]
    exact one_div_le_one_div_of_le (pow_pos hr0 (d - 6)) (pow_le_pow_right₀ hr1 (by omega))
  -- outer contribution
  have hS1 : (n : ℝ) ^ 3 * ∑ u ∈ outer, (∑ w ∈ Ann, g u * tau u w * tau u x * F w ^ 2)
      ≤ Cbub * A / (r : ℝ) ^ (d - 6) := by
    have hcomm : ∑ u ∈ outer, (∑ w ∈ Ann, g u * tau u w * tau u x * F w ^ 2)
        = ∑ w ∈ Ann, (∑ u ∈ outer, g u * tau u w * tau u x) * F w ^ 2 := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl (fun w _ => by rw [← Finset.sum_mul])
    have hstep : (n : ℝ) ^ 3 * ∑ u ∈ outer, (∑ w ∈ Ann, g u * tau u w * tau u x * F w ^ 2)
        ≤ Cbub * (A / (r : ℝ) ^ (2 * d - 12)) := by
      rw [hcomm, Finset.mul_sum]
      refine le_trans (Finset.sum_le_sum (fun w hw => hbubble w hw)) ?_
      rw [← Finset.mul_sum]
      refine mul_le_mul_of_nonneg_left ?_ hCbub
      exact le_trans (Finset.sum_le_sum_of_subset_of_nonneg hAnn_ball
        (fun w _ _ => by positivity)) hrad
    refine le_trans hstep ?_
    rw [show Cbub * (A / (r : ℝ) ^ (2 * d - 12)) = (Cbub * A) / (r : ℝ) ^ (2 * d - 12) by ring]
    exact hconv (Cbub * A) (mul_nonneg hCbub hA0)
  -- assemble
  calc (n : ℝ) ^ 3 * ∑ u ∈ Ann, (∑ w ∈ Ann, g u * tau u w * tau u x * F w ^ 2)
      = (n : ℝ) ^ 3 * (∑ u ∈ Ann \ outer, (∑ w ∈ Ann, g u * tau u w * tau u x * F w ^ 2)
          + ∑ u ∈ outer, (∑ w ∈ Ann, g u * tau u w * tau u x * F w ^ 2)) := by
        rw [Finset.sum_sdiff houter_sub]
    _ = (n : ℝ) ^ 3 * ∑ u ∈ Ann \ outer, (∑ w ∈ Ann, g u * tau u w * tau u x * F w ^ 2)
          + (n : ℝ) ^ 3 * ∑ u ∈ outer, (∑ w ∈ Ann, g u * tau u w * tau u x * F w ^ 2) := by
        rw [mul_add]
    _ ≤ Cin / (r : ℝ) ^ (d - 6) + Cbub * A / (r : ℝ) ^ (d - 6) := add_le_add hcase2 hS1
    _ = (Cbub * A + Cin) / (r : ℝ) ^ (d - 6) := by ring

/-- Existential form of the second diagram bound. -/
theorem var_term_2
    {d : ℕ} (hd : 7 ≤ d) (x : Fin d → ℤ) {n r : ℕ} (hr : 1 ≤ r) (_hrn : r ≤ n)
    (Ann outer : Finset (Fin d → ℤ))
    (g F : (Fin d → ℤ) → ℝ) (tau : (Fin d → ℤ) → (Fin d → ℤ) → ℝ)
    (Cbub Cin : ℝ) (hCbub : 0 ≤ Cbub) (hCin : 0 ≤ Cin)
    (houter_sub : outer ⊆ Ann)
    (hAnn_ball : Ann ⊆ linfBall x ((2 * n : ℕ) : ℤ))
    (hbubble : ∀ w ∈ Ann,
        (n : ℝ) ^ 3 * ((∑ u ∈ outer, g u * tau u w * tau u x) * F w ^ 2)
          ≤ Cbub * (1 / (((linfDist x w + 1 : ℕ) : ℝ) ^ (d - 4)
              * (max (r : ℝ) ((linfDist x w + 1 : ℕ) : ℝ)) ^ (2 * d - 8))))
    (hcase2 : (n : ℝ) ^ 3 * ∑ u ∈ Ann \ outer, ∑ w ∈ Ann, g u * tau u w * tau u x * F w ^ 2
          ≤ Cin / (r : ℝ) ^ (d - 6)) :
    ∃ C : ℝ, 0 ≤ C ∧
      (n : ℝ) ^ 3 * ∑ u ∈ Ann, ∑ w ∈ Ann, g u * tau u w * tau u x * F w ^ 2
        ≤ C / (r : ℝ) ^ (d - 6) := by
  have hA : 0 ≤ varOuterRadialConstant d := by unfold varOuterRadialConstant; positivity
  exact ⟨Cbub * varOuterRadialConstant d + Cin, by positivity,
    var_term_2_bound hd x hr _hrn Ann outer g F tau Cbub Cin hCbub hCin
      houter_sub hAnn_ball hbubble hcase2⟩

end NearCritical.AppendixVariance
