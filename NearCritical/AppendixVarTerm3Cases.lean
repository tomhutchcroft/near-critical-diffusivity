module

public import NearCritical.AppendixSourceRDComplement
public import NearCritical.AppendixVarTerm13

/-! Source prop.var_term_3: the two case estimates, on the literal geometry.

Dimension `d = e + 7` (so `d ≥ 7`), written `Fin (e+6+1)`. Here `S = Ann_{c₁n} ∩ Λ_h`
(`sourceAnnulus h c`), `RD = sourceRD n c`, and `S \ RD = sourceAnnComplRD h c`.

* `var_term_3_case1` (`u ∈ RD`): from pointwise `g ≤ C_g(1+r_u)^{-2}`,
  `τ ≤ C_τ n^{1-d}(1+r_u)s_u^{-1}` (lem.RD_bound) and `F ≤ C_F n^{4-d}(1+r_u)s_u^{-1}` (lem.F_RD),
  `n³∑_{RD} gτF ≲ n^{6-d}(1+log c)`, via `sourceRD_inv_sq_sum_le`.
* `var_term_3_case2` (`u ∉ RD`): from `g ≤ C_g(1+r_u)^{-2}`, `τ ≤ C_τ n^{1-d}`
  (lem.box_twopoint_onesided) and `F ≤ C_F n^{4-d}` (eq.F_pointwise),
  `n³∑_{S\RD} gτF ≲ n^{6-d}(1+log(h-c+1))`, via `sourceAnnComplRD_inv_sq_sum_le`.
* `var_term_3_source`: feeds both into `var_term_3`, using the EXPLICIT regime hypothesis
  `(1+log n)/n^{d-6} ≤ K/r^{d-6}`. The source's final step "`n^{6-d} log n ≲ r^{6-d}` since `n` is
  large" is not valid uniformly in `r ≤ n` (it fails at `r ≍ n`), so it is kept visible here.

The pointwise g/τ/F bounds are the genuinely probabilistic inputs (assumption (A),
Appendix A) and remain hypotheses. -/
@[expose] public section
namespace NearCritical.AppendixVariance
open scoped BigOperators

/-- `n³(2c+1)^{e+5}/(n^{e+6}n^{e+3}) ≤ 3^{e+5}/n^{e+1}` for `c ≤ n`, `n ≥ 1`. -/
theorem scale_bound_cubic {n c : ℕ} (hn : 1 ≤ n) (hcn : c ≤ n) (e : ℕ) :
    (n : ℝ) ^ 3 * (2 * (c : ℝ) + 1) ^ (e + 5) / ((n : ℝ) ^ (e + 6) * (n : ℝ) ^ (e + 3))
      ≤ 3 ^ (e + 5) / (n : ℝ) ^ (e + 1) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnpos
  have hc3 : 2 * (c : ℝ) + 1 ≤ 3 * (n : ℝ) := by
    have : (c : ℝ) ≤ n := by exact_mod_cast hcn
    linarith
  have hpow : (2 * (c : ℝ) + 1) ^ (e + 5) ≤ (3 * (n : ℝ)) ^ (e + 5) :=
    pow_le_pow_left₀ (by positivity) hc3 _
  calc _ ≤ (n : ℝ) ^ 3 * (3 * (n : ℝ)) ^ (e + 5) / ((n : ℝ) ^ (e + 6) * (n : ℝ) ^ (e + 3)) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hpow (by positivity))
          (by positivity)
    _ = _ := by
        rw [mul_pow]
        field_simp
        ring

/-- Source `RD ⊆ Λ_{2c} ⊆ Λ_h` (eq.w_bound): `sourceRD n c ⊆ sourceAnnulus h c` when `2c ≤ h`. -/
theorem sourceRD_subset_sourceAnnulus {k n h c : ℕ} (h2c : 2 * c ≤ h) :
    (sourceRD n c : Finset (Fin (k + 1) → ℤ)) ⊆ sourceAnnulus h c := by
  intro w hw
  obtain ⟨⟨_, hcA⟩, hrs⟩ := mem_sourceRD.mp hw
  unfold sourceR sParam at hrs
  unfold sourceAnnulus
  rw [Finset.mem_filter, mem_cube]
  refine ⟨fun i => ?_, hcA⟩
  have hi : (w i).natAbs ≤ linfDist (0 : Fin (k + 1) → ℤ) w := by
    rw [linfDist_zero]
    exact Finset.le_sup (f := fun i => (w i).natAbs) (Finset.mem_univ i)
  rw [Int.abs_eq_natAbs]
  omega

/-- Case 1 of prop.var_term_3 (`u ∈ RD`), with explicit constant. -/
theorem var_term_3_case1 {e n c : ℕ} (hn : 1 ≤ n) (hcn : c ≤ n)
    (g tau F : (Fin (e + 6 + 1) → ℤ) → ℝ) {Cg Ct CF : ℝ}
    (hCg : 0 ≤ Cg) (hCt : 0 ≤ Ct) (hCF : 0 ≤ CF)
    (hnn : ∀ u ∈ (sourceRD n c : Finset (Fin (e + 6 + 1) → ℤ)),
      0 ≤ g u ∧ 0 ≤ tau u ∧ 0 ≤ F u)
    (hg : ∀ u ∈ (sourceRD n c : Finset (Fin (e + 6 + 1) → ℤ)),
      g u ≤ Cg / ((sourceR c u : ℝ) + 1) ^ 2)
    (htau : ∀ u ∈ (sourceRD n c : Finset (Fin (e + 6 + 1) → ℤ)),
      tau u ≤ Ct * ((sourceR c u : ℝ) + 1) / ((n : ℝ) ^ (e + 6) * (sParam c u : ℝ)))
    (hF : ∀ u ∈ (sourceRD n c : Finset (Fin (e + 6 + 1) → ℤ)),
      F u ≤ CF * ((sourceR c u : ℝ) + 1) / ((n : ℝ) ^ (e + 3) * (sParam c u : ℝ))) :
    (n : ℝ) ^ 3 * ∑ u ∈ (sourceRD n c : Finset (Fin (e + 6 + 1) → ℤ)), g u * tau u * F u
      ≤ Cg * Ct * CF * (4 * ((e + 6 : ℕ) : ℝ) * (((e + 6 : ℕ) : ℝ) + 1) * 3 ^ (e + 5)) *
          (1 + Real.log (c : ℝ)) / (n : ℝ) ^ (e + 1) := by
  have hnpos : (0 : ℝ) < n := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnpos
  have hK0 : 0 ≤ Cg * Ct * CF / ((n : ℝ) ^ (e + 6) * (n : ℝ) ^ (e + 3)) :=
    div_nonneg (mul_nonneg (mul_nonneg hCg hCt) hCF) (by positivity)
  have hpt : ∀ u ∈ (sourceRD n c : Finset (Fin (e + 6 + 1) → ℤ)),
      g u * tau u * F u ≤ Cg * Ct * CF / ((n : ℝ) ^ (e + 6) * (n : ℝ) ^ (e + 3)) *
        ((1 : ℝ) / ((sParam c u : ℕ) : ℝ) ^ 2) := by
    intro u hu
    obtain ⟨hg0, ht0, hF0⟩ := hnn u hu
    have hs : 1 ≤ sParam c u := by
      have := (mem_sourceRD.mp hu).2
      omega
    have hspos : (0 : ℝ) < (sParam c u : ℝ) := by exact_mod_cast hs
    have hR : (0 : ℝ) < (sourceR c u : ℝ) + 1 := by positivity
    have hs0 := hspos.ne'
    have hR0 := hR.ne'
    have hgB0 : 0 ≤ Cg / ((sourceR c u : ℝ) + 1) ^ 2 := div_nonneg hCg (by positivity)
    have htB0 : 0 ≤ Ct * ((sourceR c u : ℝ) + 1) / ((n : ℝ) ^ (e + 6) * (sParam c u : ℝ)) :=
      div_nonneg (mul_nonneg hCt hR.le) (by positivity)
    calc g u * tau u * F u
        ≤ (Cg / ((sourceR c u : ℝ) + 1) ^ 2) *
            (Ct * ((sourceR c u : ℝ) + 1) / ((n : ℝ) ^ (e + 6) * (sParam c u : ℝ))) *
            (CF * ((sourceR c u : ℝ) + 1) / ((n : ℝ) ^ (e + 3) * (sParam c u : ℝ))) :=
          mul_le_mul (mul_le_mul (hg u hu) (htau u hu) ht0 hgB0) (hF u hu) hF0
            (mul_nonneg hgB0 htB0)
      _ = _ := by field_simp <;> ring
  have hsum : ∑ u ∈ (sourceRD n c : Finset (Fin (e + 6 + 1) → ℤ)), g u * tau u * F u ≤
      Cg * Ct * CF / ((n : ℝ) ^ (e + 6) * (n : ℝ) ^ (e + 3)) *
        ∑ u ∈ (sourceRD n c : Finset (Fin (e + 6 + 1) → ℤ)),
          (1 : ℝ) / ((sParam c u : ℕ) : ℝ) ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum hpt
  have hRD := sourceRD_inv_sq_sum_le (k := e + 6) (by omega) hcn
  rw [show e + 6 - 1 = e + 5 by omega] at hRD
  have hlog : 0 ≤ 1 + Real.log (c : ℝ) := by
    have := Real.log_natCast_nonneg c
    linarith
  have hA0 : 0 ≤ Cg * Ct * CF * (4 * ((e + 6 : ℕ) : ℝ) * (((e + 6 : ℕ) : ℝ) + 1)) *
      (1 + Real.log (c : ℝ)) :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hCg hCt) hCF) (by positivity)) hlog
  calc _ ≤ (n : ℝ) ^ 3 * (Cg * Ct * CF / ((n : ℝ) ^ (e + 6) * (n : ℝ) ^ (e + 3)) *
          (4 * ((e + 6 : ℕ) : ℝ) * (((e + 6 : ℕ) : ℝ) + 1) * (2 * (c : ℝ) + 1) ^ (e + 5) *
            (1 + Real.log (c : ℝ)))) :=
        mul_le_mul_of_nonneg_left (hsum.trans (mul_le_mul_of_nonneg_left hRD hK0))
          (by positivity)
    _ = (Cg * Ct * CF * (4 * ((e + 6 : ℕ) : ℝ) * (((e + 6 : ℕ) : ℝ) + 1)) *
          (1 + Real.log (c : ℝ))) *
          ((n : ℝ) ^ 3 * (2 * (c : ℝ) + 1) ^ (e + 5) /
            ((n : ℝ) ^ (e + 6) * (n : ℝ) ^ (e + 3))) := by ring
    _ ≤ (Cg * Ct * CF * (4 * ((e + 6 : ℕ) : ℝ) * (((e + 6 : ℕ) : ℝ) + 1)) *
          (1 + Real.log (c : ℝ))) * (3 ^ (e + 5) / (n : ℝ) ^ (e + 1)) :=
        mul_le_mul_of_nonneg_left (scale_bound_cubic hn hcn e) hA0
    _ = _ := by ring

/-- Case 2 of prop.var_term_3 (`u ∈ (Ann ∩ Λ_h) \ RD`), with explicit constant. -/
theorem var_term_3_case2 {e n h c : ℕ} (hn : 1 ≤ n) (hhn : h ≤ n) (hch : c ≤ h)
    (g tau F : (Fin (e + 6 + 1) → ℤ) → ℝ) {Cg Ct CF : ℝ}
    (hCg : 0 ≤ Cg) (hCt : 0 ≤ Ct) (hCF : 0 ≤ CF)
    (hnn : ∀ u ∈ (sourceAnnComplRD h c : Finset (Fin (e + 6 + 1) → ℤ)),
      0 ≤ g u ∧ 0 ≤ tau u ∧ 0 ≤ F u)
    (hg : ∀ u ∈ (sourceAnnComplRD h c : Finset (Fin (e + 6 + 1) → ℤ)),
      g u ≤ Cg / ((sourceR c u : ℝ) + 1) ^ 2)
    (htau : ∀ u ∈ (sourceAnnComplRD h c : Finset (Fin (e + 6 + 1) → ℤ)),
      tau u ≤ Ct / (n : ℝ) ^ (e + 6))
    (hF : ∀ u ∈ (sourceAnnComplRD h c : Finset (Fin (e + 6 + 1) → ℤ)),
      F u ≤ CF / (n : ℝ) ^ (e + 3)) :
    (n : ℝ) ^ 3 * ∑ u ∈ (sourceAnnComplRD h c : Finset (Fin (e + 6 + 1) → ℤ)),
        g u * tau u * F u
      ≤ Cg * Ct * CF * (8 * ((e + 6 : ℕ) : ℝ) * (((e + 6 : ℕ) : ℝ) + 1) * 3 ^ (e + 5)) *
          (1 + Real.log ((h - c + 1 : ℕ) : ℝ)) / (n : ℝ) ^ (e + 1) := by
  have hnpos : (0 : ℝ) < n := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnpos
  have hK0 : 0 ≤ Cg * Ct * CF / ((n : ℝ) ^ (e + 6) * (n : ℝ) ^ (e + 3)) :=
    div_nonneg (mul_nonneg (mul_nonneg hCg hCt) hCF) (by positivity)
  have hpt : ∀ u ∈ (sourceAnnComplRD h c : Finset (Fin (e + 6 + 1) → ℤ)),
      g u * tau u * F u ≤ Cg * Ct * CF / ((n : ℝ) ^ (e + 6) * (n : ℝ) ^ (e + 3)) *
        ((1 : ℝ) / ((sourceR c u + 1 : ℕ) : ℝ) ^ 2) := by
    intro u hu
    obtain ⟨hg0, ht0, hF0⟩ := hnn u hu
    have hR : (0 : ℝ) < (sourceR c u : ℝ) + 1 := by positivity
    have hR0 := hR.ne'
    have hgB0 : 0 ≤ Cg / ((sourceR c u : ℝ) + 1) ^ 2 := div_nonneg hCg (by positivity)
    have htB0 : 0 ≤ Ct / (n : ℝ) ^ (e + 6) := div_nonneg hCt (by positivity)
    calc g u * tau u * F u
        ≤ (Cg / ((sourceR c u : ℝ) + 1) ^ 2) * (Ct / (n : ℝ) ^ (e + 6)) *
            (CF / (n : ℝ) ^ (e + 3)) :=
          mul_le_mul (mul_le_mul (hg u hu) (htau u hu) ht0 hgB0) (hF u hu) hF0
            (mul_nonneg hgB0 htB0)
      _ = _ := by push_cast; field_simp <;> ring
  have hsum : ∑ u ∈ (sourceAnnComplRD h c : Finset (Fin (e + 6 + 1) → ℤ)),
      g u * tau u * F u ≤
      Cg * Ct * CF / ((n : ℝ) ^ (e + 6) * (n : ℝ) ^ (e + 3)) *
        ∑ u ∈ (sourceAnnComplRD h c : Finset (Fin (e + 6 + 1) → ℤ)),
          (1 : ℝ) / ((sourceR c u + 1 : ℕ) : ℝ) ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum hpt
  have hC := sourceAnnComplRD_inv_sq_sum_le (k := e + 6) (by omega) hch
  rw [show e + 6 - 1 = e + 5 by omega] at hC
  have hlog : 0 ≤ 1 + Real.log ((h - c + 1 : ℕ) : ℝ) := by
    have := Real.log_natCast_nonneg (h - c + 1)
    linarith
  have hA0 : 0 ≤ Cg * Ct * CF * (8 * ((e + 6 : ℕ) : ℝ) * (((e + 6 : ℕ) : ℝ) + 1)) *
      (1 + Real.log ((h - c + 1 : ℕ) : ℝ)) :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hCg hCt) hCF) (by positivity)) hlog
  calc _ ≤ (n : ℝ) ^ 3 * (Cg * Ct * CF / ((n : ℝ) ^ (e + 6) * (n : ℝ) ^ (e + 3)) *
          (8 * ((e + 6 : ℕ) : ℝ) * (((e + 6 : ℕ) : ℝ) + 1) * (2 * (h : ℝ) + 1) ^ (e + 5) *
            (1 + Real.log ((h - c + 1 : ℕ) : ℝ)))) :=
        mul_le_mul_of_nonneg_left (hsum.trans (mul_le_mul_of_nonneg_left hC hK0))
          (by positivity)
    _ = (Cg * Ct * CF * (8 * ((e + 6 : ℕ) : ℝ) * (((e + 6 : ℕ) : ℝ) + 1)) *
          (1 + Real.log ((h - c + 1 : ℕ) : ℝ))) *
          ((n : ℝ) ^ 3 * (2 * (h : ℝ) + 1) ^ (e + 5) /
            ((n : ℝ) ^ (e + 6) * (n : ℝ) ^ (e + 3))) := by ring
    _ ≤ (Cg * Ct * CF * (8 * ((e + 6 : ℕ) : ℝ) * (((e + 6 : ℕ) : ℝ) + 1)) *
          (1 + Real.log ((h - c + 1 : ℕ) : ℝ))) * (3 ^ (e + 5) / (n : ℝ) ^ (e + 1)) :=
        mul_le_mul_of_nonneg_left (scale_bound_cubic hn hhn e) hA0
    _ = _ := by ring

/-- The inner-region coefficient depends only on dimension and kernel bounds. -/
noncomputable def varTermThreeInnerConstant (e : ℕ) (Cg Ct CF : ℝ) : ℝ :=
  Cg * Ct * CF * (8 * ((e + 6 : ℕ) : ℝ) * (((e + 6 : ℕ) : ℝ) + 1) * 3 ^ (e + 5))

/-- prop.var_term_3 on the literal source geometry, given the pointwise g/τ/F inputs and the
explicit regime hypothesis `(1+log n)/n^{d-6} ≤ K/r^{d-6}` (`d = e+7`). -/
theorem var_term_3_source_bound {e n r h c : ℕ} (hn : 1 ≤ n) (hr : 1 ≤ r) (hrn : r ≤ n)
    (hc1 : 1 ≤ c) (h2c : 2 * c ≤ h) (hhn : h ≤ n)
    (g tau F : (Fin (e + 6 + 1) → ℤ) → ℝ) {Cg Ct CF ρ Cρ Kreg : ℝ}
    (hCg : 0 ≤ Cg) (hCt : 0 ≤ Ct) (hCF : 0 ≤ CF) (hCρ : 0 ≤ Cρ) (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ Cρ)
    (hKreg : 0 ≤ Kreg)
    (hnn : ∀ u ∈ (sourceAnnulus h c : Finset (Fin (e + 6 + 1) → ℤ)),
      0 ≤ g u ∧ 0 ≤ tau u ∧ 0 ≤ F u)
    (hg : ∀ u ∈ (sourceAnnulus h c : Finset (Fin (e + 6 + 1) → ℤ)),
      g u ≤ Cg / ((sourceR c u : ℝ) + 1) ^ 2)
    (htau1 : ∀ u ∈ (sourceRD n c : Finset (Fin (e + 6 + 1) → ℤ)),
      tau u ≤ Ct * ((sourceR c u : ℝ) + 1) / ((n : ℝ) ^ (e + 6) * (sParam c u : ℝ)))
    (hF1 : ∀ u ∈ (sourceRD n c : Finset (Fin (e + 6 + 1) → ℤ)),
      F u ≤ CF * ((sourceR c u : ℝ) + 1) / ((n : ℝ) ^ (e + 3) * (sParam c u : ℝ)))
    (htau2 : ∀ u ∈ (sourceAnnComplRD h c : Finset (Fin (e + 6 + 1) → ℤ)),
      tau u ≤ Ct / (n : ℝ) ^ (e + 6))
    (hF2 : ∀ u ∈ (sourceAnnComplRD h c : Finset (Fin (e + 6 + 1) → ℤ)),
      F u ≤ CF / (n : ℝ) ^ (e + 3))
    (hreg : (1 + Real.log (n : ℝ)) / (n : ℝ) ^ (e + 1) ≤ Kreg / (r : ℝ) ^ (e + 1)) :
    (n : ℝ) ^ 3 * (ρ * ∑ u ∈ (sourceAnnulus h c : Finset (Fin (e + 6 + 1) → ℤ)),
      g u * tau u * F u) ≤ Cρ * (2 * (varTermThreeInnerConstant e Cg Ct CF * Kreg)) / (r : ℝ) ^ (e + 6 + 1 - 6) := by
  have hSRD : (sourceRD n c : Finset (Fin (e + 6 + 1) → ℤ)) ⊆ sourceAnnulus h c :=
    sourceRD_subset_sourceAnnulus h2c
  have hcompl : (sourceAnnComplRD h c : Finset (Fin (e + 6 + 1) → ℤ)) ⊆ sourceAnnulus h c := by
    unfold sourceAnnComplRD; exact Finset.filter_subset _ _
  have hcn : c ≤ n := by omega
  have hch : c ≤ h := by omega
  have hnpos : (0 : ℝ) < n := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hexp : e + 6 + 1 - 6 = e + 1 := by omega
  set A : ℝ := varTermThreeInnerConstant e Cg Ct CF with hA
  have hA0 : 0 ≤ A := by
    rw [hA, varTermThreeInnerConstant]; exact mul_nonneg (mul_nonneg (mul_nonneg hCg hCt) hCF) (by positivity)
  have hlogn : 0 ≤ 1 + Real.log (n : ℝ) := by
    have := Real.log_natCast_nonneg n
    linarith
  have hlogc : Real.log (c : ℝ) ≤ Real.log (n : ℝ) :=
    Real.log_le_log (by exact_mod_cast hc1) (by exact_mod_cast hcn)
  have hloghc : Real.log ((h - c + 1 : ℕ) : ℝ) ≤ Real.log (n : ℝ) :=
    Real.log_le_log (by positivity) (by exact_mod_cast (show h - c + 1 ≤ n by omega))
  have hcase1 : (n : ℝ) ^ 3 * ∑ u ∈ (sourceRD n c : Finset (Fin (e + 6 + 1) → ℤ)),
      g u * tau u * F u ≤ A * Kreg / (r : ℝ) ^ (e + 6 + 1 - 6) := by
    rw [hexp]
    have h1 := var_term_3_case1 hn hcn g tau F hCg hCt hCF
      (fun u hu => hnn u (hSRD hu)) (fun u hu => hg u (hSRD hu)) htau1 hF1
    have hc0 : 0 ≤ Cg * Ct * CF *
        (4 * ((e + 6 : ℕ) : ℝ) * (((e + 6 : ℕ) : ℝ) + 1) * 3 ^ (e + 5)) :=
      mul_nonneg (mul_nonneg (mul_nonneg hCg hCt) hCF) (by positivity)
    have hle4 : Cg * Ct * CF * (4 * ((e + 6 : ℕ) : ℝ) * (((e + 6 : ℕ) : ℝ) + 1) * 3 ^ (e + 5))
        ≤ A := by
      rw [hA, varTermThreeInnerConstant]
      have hb : 0 ≤ ((e + 6 : ℕ) : ℝ) * (((e + 6 : ℕ) : ℝ) + 1) * 3 ^ (e + 5) := by positivity
      have hC0 : 0 ≤ Cg * Ct * CF := mul_nonneg (mul_nonneg hCg hCt) hCF
      nlinarith
    calc _ ≤ _ := h1
      _ ≤ A * (1 + Real.log (n : ℝ)) / (n : ℝ) ^ (e + 1) :=
          div_le_div_of_nonneg_right
            (mul_le_mul hle4 (by linarith) (by have := Real.log_natCast_nonneg c; linarith) hA0)
            (by positivity)
      _ = A * ((1 + Real.log (n : ℝ)) / (n : ℝ) ^ (e + 1)) := by ring
      _ ≤ A * (Kreg / (r : ℝ) ^ (e + 1)) := mul_le_mul_of_nonneg_left hreg hA0
      _ = _ := by ring
  have hcase2 : (n : ℝ) ^ 3 * ∑ u ∈ (sourceAnnulus h c : Finset (Fin (e + 6 + 1) → ℤ)) \
      sourceRD n c, g u * tau u * F u ≤ A * Kreg / (r : ℝ) ^ (e + 6 + 1 - 6) := by
    rw [hexp, ← sourceAnnComplRD_eq hhn]
    have h2 := var_term_3_case2 hn hhn hch g tau F hCg hCt hCF
      (fun u hu => hnn u (hcompl hu)) (fun u hu => hg u (hcompl hu)) htau2 hF2
    calc _ ≤ _ := h2
      _ ≤ A * (1 + Real.log (n : ℝ)) / (n : ℝ) ^ (e + 1) :=
          div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left (by linarith) hA0) (by positivity)
      _ = A * ((1 + Real.log (n : ℝ)) / (n : ℝ) ^ (e + 1)) := by ring
      _ ≤ A * (Kreg / (r : ℝ) ^ (e + 1)) := mul_le_mul_of_nonneg_left hreg hA0
      _ = _ := by ring
  exact var_term_3_bound (d := e + 6 + 1) (by omega) hr hrn (sourceAnnulus h c) (sourceRD n c)
    g tau F ρ Cρ (A * Kreg) hCρ (mul_nonneg hA0 hKreg) hρ0 hρ hSRD
    (fun u hu => by
      obtain ⟨h1, h2, h3⟩ := hnn u hu
      exact mul_nonneg (mul_nonneg h1 h2) h3)
    hcase1 hcase2

/-- Existential form of the source third diagram bound. -/
theorem var_term_3_source {e n r h c : ℕ} (hn : 1 ≤ n) (hr : 1 ≤ r) (hrn : r ≤ n)
    (hc1 : 1 ≤ c) (h2c : 2 * c ≤ h) (hhn : h ≤ n)
    (g tau F : (Fin (e + 6 + 1) → ℤ) → ℝ) {Cg Ct CF ρ Cρ Kreg : ℝ}
    (hCg : 0 ≤ Cg) (hCt : 0 ≤ Ct) (hCF : 0 ≤ CF) (hCρ : 0 ≤ Cρ) (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ Cρ)
    (hKreg : 0 ≤ Kreg)
    (hnn : ∀ u ∈ (sourceAnnulus h c : Finset (Fin (e + 6 + 1) → ℤ)),
      0 ≤ g u ∧ 0 ≤ tau u ∧ 0 ≤ F u)
    (hg : ∀ u ∈ (sourceAnnulus h c : Finset (Fin (e + 6 + 1) → ℤ)),
      g u ≤ Cg / ((sourceR c u : ℝ) + 1) ^ 2)
    (htau1 : ∀ u ∈ (sourceRD n c : Finset (Fin (e + 6 + 1) → ℤ)),
      tau u ≤ Ct * ((sourceR c u : ℝ) + 1) / ((n : ℝ) ^ (e + 6) * (sParam c u : ℝ)))
    (hF1 : ∀ u ∈ (sourceRD n c : Finset (Fin (e + 6 + 1) → ℤ)),
      F u ≤ CF * ((sourceR c u : ℝ) + 1) / ((n : ℝ) ^ (e + 3) * (sParam c u : ℝ)))
    (htau2 : ∀ u ∈ (sourceAnnComplRD h c : Finset (Fin (e + 6 + 1) → ℤ)),
      tau u ≤ Ct / (n : ℝ) ^ (e + 6))
    (hF2 : ∀ u ∈ (sourceAnnComplRD h c : Finset (Fin (e + 6 + 1) → ℤ)),
      F u ≤ CF / (n : ℝ) ^ (e + 3))
    (hreg : (1 + Real.log (n : ℝ)) / (n : ℝ) ^ (e + 1) ≤ Kreg / (r : ℝ) ^ (e + 1)) :
    ∃ C : ℝ, 0 ≤ C ∧
      (n : ℝ) ^ 3 * (ρ * ∑ u ∈ (sourceAnnulus h c : Finset (Fin (e + 6 + 1) → ℤ)),
        g u * tau u * F u) ≤ C / (r : ℝ) ^ (e + 6 + 1 - 6) := by
  have hconst : 0 ≤ varTermThreeInnerConstant e Cg Ct CF := by
    unfold varTermThreeInnerConstant
    positivity
  exact ⟨Cρ * (2 * (varTermThreeInnerConstant e Cg Ct CF * Kreg)), by positivity,
    var_term_3_source_bound hn hr hrn hc1 h2c hhn g tau F hCg hCt hCF hCρ hρ0 hρ hKreg
      hnn hg htau1 hF1 htau2 hF2 hreg⟩

end NearCritical.AppendixVariance
