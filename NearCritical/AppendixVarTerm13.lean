module

public import NearCritical.AppendixVarTerm2

/-! Appendix B, Propositions `prop.var_term_1` and `prop.var_term_3` (source/main.tex,
statements 6850 / 6864, proofs 6944-7015 / 7041-7072), completing the four var_term
propositions as faithful conditional reductions (same convention as `var_term_2`/`var_term_4`).

* `var_term_1`: `n^3 ∑_{u,w∈Ann} g(w) τ(w,u) τ(u,x) F(w) F(u) ≲ r^{6-d}`. Split the inner
  `w`-sum into `outer = Λ_n\Λ_{n/2}` and `Ann\outer`. For the outer part, the source `Φ`-estimate
  (`eq.Phi_bound`, three sub-cases) together with the two-point bound on `τ(u,x)` and
  `F(u) ≲ M(u)^{4-d}` reduces the per-`u` inner sum to the radial kernel
  `(1+|x-u|)^{2-d} M(u)^{10-2d} = 1/((|x-u|_∞+1)^{d-2} max(r,·)^{2d-10})` (hypothesis `hphi`);
  summing over the ℓ∞ ball is the verified `radial_div_sum_le` (`p = d-2`, `t = 2d-12`),
  giving `≲ r^{12-2d} ≤ r^{6-d}`. This outer step is FULLY PROVED here. The inner part is the
  hypothesis `hcase2` (`eq.inner_sum` + the `Ψ`-estimate).

* `var_term_3`: `n^3 ρ ∑_{u∈Ann∩Λ_{n/2}} g(u) τ(u,x) F(u) ≲ r^{6-d}`. With `ρ ≲ 1`
  (`lem.rho_F_basic`), the sum splits into `RD_{c1n}` and its complement, each bounded by
  `n^{6-d}log n ≲ r^{6-d}` via `eq.RD_count` + `lem.RD_bound`/`lem.F_RD`. Both case bounds are
  taken as hypotheses (`hcase1`,`hcase2`); the proof is the elementary assembly
  (`ρ ≤ Cρ`, nonnegativity, the two-set split). This proposition has no radial content — its
  analytic weight is entirely in `eq.RD_count`, legitimately an explicit input.

HONEST SCOPE: both are CONDITIONAL REDUCTIONS. `var_term_1`'s outer radial step is genuinely
proved against the verified engine; everything else (`hphi`, `hcase2`, `hcase1`, the `RD`
inputs) is a standard Appendix-A/counting result taken as an explicit hypothesis, not yet
proved in Lean, and the regions are abstract Finsets, not the concrete `Ann_{c1n}/RD/Λn`
geometry. -/
@[expose] public section
namespace NearCritical.AppendixVariance
open scoped BigOperators

/-- Proposition `prop.var_term_1`, reduced to the outer `Φ`-estimate/kernel bound (`hphi`,
discharged via `radial_div_sum_le`) and the inner `eq.inner_sum`/`Ψ` estimate (`hcase2`). -/
theorem var_term_1_bound
    {d : ℕ} (hd : 7 ≤ d) (x : Fin d → ℤ) {n r : ℕ} (hr : 1 ≤ r) (_hrn : r ≤ n)
    (Ann outer : Finset (Fin d → ℤ))
    (g F : (Fin d → ℤ) → ℝ) (tau : (Fin d → ℤ) → (Fin d → ℤ) → ℝ)
    (Cphi Cin : ℝ) (hCphi : 0 ≤ Cphi) (_hCin : 0 ≤ Cin)
    (houter_sub : outer ⊆ Ann)
    (hAnn_ball : Ann ⊆ linfBall x ((2 * n : ℕ) : ℤ))
    (hphi : ∀ u ∈ Ann,
        (n : ℝ) ^ 3 * (∑ w ∈ outer, g w * tau w u * tau u x * F w * F u)
          ≤ Cphi * (1 / (((linfDist x u + 1 : ℕ) : ℝ) ^ (d - 2)
              * (max (r : ℝ) ((linfDist x u + 1 : ℕ) : ℝ)) ^ (2 * d - 10))))
    (hcase2 : (n : ℝ) ^ 3 * ∑ u ∈ Ann, ∑ w ∈ Ann \ outer, g w * tau w u * tau u x * F w * F u
          ≤ Cin / (r : ℝ) ^ (d - 6)) :
    (n : ℝ) ^ 3 * ∑ u ∈ Ann, ∑ w ∈ Ann, g w * tau w u * tau u x * F w * F u
      ≤ (Cphi * varOuterRadialConstant d + Cin) / (r : ℝ) ^ (d - 6) := by
  have hr0 : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have hr1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hBne : ((2 * d - 12 : ℕ) : ℝ) ≠ 0 := by
    have : 2 * d - 12 ≠ 0 := by omega
    exact_mod_cast this
  set A : ℝ := varOuterRadialConstant d with hA_def
  have hA0 : 0 ≤ A := by rw [hA_def, varOuterRadialConstant]; exact div_nonneg (by positivity) (by positivity)
  have hrad : ∑ u ∈ linfBall x ((2 * n : ℕ) : ℤ),
        1 / (((linfDist x u + 1 : ℕ) : ℝ) ^ (d - 2)
            * (max (r : ℝ) ((linfDist x u + 1 : ℕ) : ℝ)) ^ (2 * d - 10))
      ≤ A / (r : ℝ) ^ (2 * d - 12) := by
    have h := radial_div_sum_le (show 1 ≤ d by omega) x (d - 2) (by omega)
      (show 1 ≤ 2 * d - 12 by omega) hr (2 * n)
    simp only [show (d - 1) - (d - 2) + (2 * d - 12 + 1) = 2 * d - 10 by omega] at h
    refine h.trans (le_of_eq ?_)
    rw [hA_def, varOuterRadialConstant]; field_simp
  have hconv : ∀ a : ℝ, 0 ≤ a → a / (r : ℝ) ^ (2 * d - 12) ≤ a / (r : ℝ) ^ (d - 6) := by
    intro a ha
    rw [div_eq_mul_inv, div_eq_mul_inv]
    apply mul_le_mul_of_nonneg_left _ ha
    rw [inv_eq_one_div, inv_eq_one_div]
    exact one_div_le_one_div_of_le (pow_pos hr0 (d - 6)) (pow_le_pow_right₀ hr1 (by omega))
  have hS1 : (n : ℝ) ^ 3 * ∑ u ∈ Ann, (∑ w ∈ outer, g w * tau w u * tau u x * F w * F u)
      ≤ Cphi * A / (r : ℝ) ^ (d - 6) := by
    have hstep : (n : ℝ) ^ 3 * ∑ u ∈ Ann, (∑ w ∈ outer, g w * tau w u * tau u x * F w * F u)
        ≤ Cphi * (A / (r : ℝ) ^ (2 * d - 12)) := by
      rw [Finset.mul_sum]
      refine le_trans (Finset.sum_le_sum (fun u hu => hphi u hu)) ?_
      rw [← Finset.mul_sum]
      refine mul_le_mul_of_nonneg_left ?_ hCphi
      exact le_trans (Finset.sum_le_sum_of_subset_of_nonneg hAnn_ball
        (fun u _ _ => by positivity)) hrad
    refine le_trans hstep ?_
    rw [show Cphi * (A / (r : ℝ) ^ (2 * d - 12)) = (Cphi * A) / (r : ℝ) ^ (2 * d - 12) by ring]
    exact hconv (Cphi * A) (mul_nonneg hCphi hA0)
  calc (n : ℝ) ^ 3 * ∑ u ∈ Ann, (∑ w ∈ Ann, g w * tau w u * tau u x * F w * F u)
      = (n : ℝ) ^ 3 * ∑ u ∈ Ann,
          (∑ w ∈ Ann \ outer, g w * tau w u * tau u x * F w * F u
            + ∑ w ∈ outer, g w * tau w u * tau u x * F w * F u) := by
        refine congrArg _ (Finset.sum_congr rfl (fun u _ => ?_))
        rw [Finset.sum_sdiff houter_sub]
    _ = (n : ℝ) ^ 3 * ∑ u ∈ Ann, (∑ w ∈ Ann \ outer, g w * tau w u * tau u x * F w * F u)
          + (n : ℝ) ^ 3 * ∑ u ∈ Ann, (∑ w ∈ outer, g w * tau w u * tau u x * F w * F u) := by
        rw [Finset.sum_add_distrib, mul_add]
    _ ≤ Cin / (r : ℝ) ^ (d - 6) + Cphi * A / (r : ℝ) ^ (d - 6) := add_le_add hcase2 hS1
    _ = (Cphi * A + Cin) / (r : ℝ) ^ (d - 6) := by ring

/-- Existential form of the first diagram bound. -/
theorem var_term_1
    {d : ℕ} (hd : 7 ≤ d) (x : Fin d → ℤ) {n r : ℕ} (hr : 1 ≤ r) (_hrn : r ≤ n)
    (Ann outer : Finset (Fin d → ℤ))
    (g F : (Fin d → ℤ) → ℝ) (tau : (Fin d → ℤ) → (Fin d → ℤ) → ℝ)
    (Cphi Cin : ℝ) (hCphi : 0 ≤ Cphi) (hCin : 0 ≤ Cin)
    (houter_sub : outer ⊆ Ann)
    (hAnn_ball : Ann ⊆ linfBall x ((2 * n : ℕ) : ℤ))
    (hphi : ∀ u ∈ Ann,
        (n : ℝ) ^ 3 * (∑ w ∈ outer, g w * tau w u * tau u x * F w * F u)
          ≤ Cphi * (1 / (((linfDist x u + 1 : ℕ) : ℝ) ^ (d - 2)
              * (max (r : ℝ) ((linfDist x u + 1 : ℕ) : ℝ)) ^ (2 * d - 10))))
    (hcase2 : (n : ℝ) ^ 3 * ∑ u ∈ Ann, ∑ w ∈ Ann \ outer, g w * tau w u * tau u x * F w * F u
          ≤ Cin / (r : ℝ) ^ (d - 6)) :
    ∃ C : ℝ, 0 ≤ C ∧
      (n : ℝ) ^ 3 * ∑ u ∈ Ann, ∑ w ∈ Ann, g w * tau w u * tau u x * F w * F u
        ≤ C / (r : ℝ) ^ (d - 6) := by
  have hA : 0 ≤ varOuterRadialConstant d := by unfold varOuterRadialConstant; positivity
  exact ⟨Cphi * varOuterRadialConstant d + Cin, by positivity,
    var_term_1_bound hd x hr _hrn Ann outer g F tau Cphi Cin hCphi hCin
      houter_sub hAnn_ball hphi hcase2⟩

/-- Proposition `prop.var_term_3`: `n^3 ρ ∑_{u∈S} g(u) τ(u,x) F(u) ≲ r^{6-d}`, reduced to the
two `eq.RD_count`-based case bounds (`hcase1` on `RD`, `hcase2` on the complement) and
`ρ ≲ 1`. No radial content — the analytic weight is entirely in the `RD_count` inputs. -/
theorem var_term_3_bound
    {d : ℕ} (_hd : 7 ≤ d) {n r : ℕ} (_hr : 1 ≤ r) (_hrn : r ≤ n)
    (S SRD : Finset (Fin d → ℤ)) (g tau F : (Fin d → ℤ) → ℝ)
    (ρ Cρ Crd : ℝ) (hCρ : 0 ≤ Cρ) (_hCrd : 0 ≤ Crd)
    (_hρ0 : 0 ≤ ρ) (hρ : ρ ≤ Cρ)
    (hSRD : SRD ⊆ S)
    (hterm : ∀ u ∈ S, 0 ≤ g u * tau u * F u)
    (hcase1 : (n : ℝ) ^ 3 * ∑ u ∈ SRD, g u * tau u * F u ≤ Crd / (r : ℝ) ^ (d - 6))
    (hcase2 : (n : ℝ) ^ 3 * ∑ u ∈ S \ SRD, g u * tau u * F u ≤ Crd / (r : ℝ) ^ (d - 6)) :
    (n : ℝ) ^ 3 * (ρ * ∑ u ∈ S, g u * tau u * F u) ≤ Cρ * (2 * Crd) / (r : ℝ) ^ (d - 6) := by
  have hsum0 : 0 ≤ ∑ u ∈ S, g u * tau u * F u := Finset.sum_nonneg (fun u hu => hterm u hu)
  have hn3sum : (n : ℝ) ^ 3 * ∑ u ∈ S, g u * tau u * F u ≤ 2 * Crd / (r : ℝ) ^ (d - 6) := by
    rw [← Finset.sum_sdiff hSRD, mul_add]
    refine le_trans (add_le_add hcase2 hcase1) (le_of_eq ?_)
    ring
  calc (n : ℝ) ^ 3 * (ρ * ∑ u ∈ S, g u * tau u * F u)
      = ρ * ((n : ℝ) ^ 3 * ∑ u ∈ S, g u * tau u * F u) := by ring
    _ ≤ Cρ * ((n : ℝ) ^ 3 * ∑ u ∈ S, g u * tau u * F u) :=
        mul_le_mul_of_nonneg_right hρ (mul_nonneg (by positivity) hsum0)
    _ ≤ Cρ * (2 * Crd / (r : ℝ) ^ (d - 6)) := mul_le_mul_of_nonneg_left hn3sum hCρ
    _ = Cρ * (2 * Crd) / (r : ℝ) ^ (d - 6) := by ring

/-- Existential form of the third diagram bound. -/
theorem var_term_3
    {d : ℕ} (_hd : 7 ≤ d) {n r : ℕ} (_hr : 1 ≤ r) (_hrn : r ≤ n)
    (S SRD : Finset (Fin d → ℤ)) (g tau F : (Fin d → ℤ) → ℝ)
    (ρ Cρ Crd : ℝ) (hCρ : 0 ≤ Cρ) (hCrd : 0 ≤ Crd)
    (_hρ0 : 0 ≤ ρ) (hρ : ρ ≤ Cρ)
    (hSRD : SRD ⊆ S)
    (hterm : ∀ u ∈ S, 0 ≤ g u * tau u * F u)
    (hcase1 : (n : ℝ) ^ 3 * ∑ u ∈ SRD, g u * tau u * F u ≤ Crd / (r : ℝ) ^ (d - 6))
    (hcase2 : (n : ℝ) ^ 3 * ∑ u ∈ S \ SRD, g u * tau u * F u ≤ Crd / (r : ℝ) ^ (d - 6)) :
    ∃ C : ℝ, 0 ≤ C ∧
      (n : ℝ) ^ 3 * (ρ * ∑ u ∈ S, g u * tau u * F u) ≤ C / (r : ℝ) ^ (d - 6) :=
  ⟨Cρ * (2 * Crd), mul_nonneg hCρ (by positivity),
    var_term_3_bound _hd _hr _hrn S SRD g tau F ρ Cρ Crd hCρ hCrd _hρ0 hρ
      hSRD hterm hcase1 hcase2⟩

end NearCritical.AppendixVariance
