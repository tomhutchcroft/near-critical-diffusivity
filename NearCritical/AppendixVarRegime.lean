module

public import NearCritical.AppendixVarCapstoneFull

/-! The regime hypothesis is discharged by the source's own quantifier order.

prop:VARf1 (main.tex 3502) reads "for any `r` there is `n₀(c₁, r)` such that for any `n ≥ n₀`".
With `r` fixed and `n` large, `(1 + log n)/n^{d-6} ≤ 1/r^{d-6}`. Concretely, `log n ≤ n - 1`
gives `(1 + log n)/n^{E+1} ≤ 1/n^E ≤ 1/r^{E+1}` once `n ≥ 2r^{E+1}`.

This CORRECTS earlier notes (mine and in the divergence report) calling the source's step
"`n^{6-d} log n ≲ r^{6-d}` since `n` is sufficiently large" invalid. It is invalid only uniformly in
`r ≤ n`. In the source's actual quantifier order (`n ≥ n₀(r)`) it holds.

`VARf_capstone_large_n` is `VARf_capstone_full` with `hreg` replaced by `2r^{E+1} ≤ n`, matching
the `n ≥ n₀(r)` form of prop:VARf1 with an explicit `n₀ = 2r^{d-6}`. Its constant is independent of
`n` and `r`. -/
@[expose] public section
namespace NearCritical.AppendixVariance
open scoped BigOperators

/-- For `n ≥ 2r^{E+1}` (`E ≥ 1`, `r ≥ 1`): `(1 + log n)/n^{E+1} ≤ 1/r^{E+1}`. -/
theorem regime_of_large_n {E n r : ℕ} (hE : 1 ≤ E) (hr : 1 ≤ r)
    (hn0 : 2 * r ^ (E + 1) ≤ n) :
    (1 + Real.log (n : ℝ)) / (n : ℝ) ^ (E + 1) ≤ 1 / (r : ℝ) ^ (E + 1) := by
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hrp : (1 : ℝ) ≤ (r : ℝ) ^ (E + 1) := one_le_pow₀ hr1
  have hnR : 2 * (r : ℝ) ^ (E + 1) ≤ n := by exact_mod_cast hn0
  have hn1 : (1 : ℝ) ≤ n := by linarith
  have hnpos : (0 : ℝ) < n := by linarith
  have hlog : 1 + Real.log (n : ℝ) ≤ n := by
    have := Real.log_le_sub_one_of_pos hnpos; linarith
  have hnE : (n : ℝ) ≤ (n : ℝ) ^ E := by
    calc (n : ℝ) = (n : ℝ) ^ 1 := (pow_one _).symm
      _ ≤ (n : ℝ) ^ E := pow_le_pow_right₀ hn1 hE
  have hrn : (r : ℝ) ^ (E + 1) ≤ (n : ℝ) ^ E := by linarith
  calc (1 + Real.log (n : ℝ)) / (n : ℝ) ^ (E + 1)
      ≤ (n : ℝ) / (n : ℝ) ^ (E + 1) := div_le_div_of_nonneg_right hlog (by positivity)
    _ = 1 / (n : ℝ) ^ E := by
        rw [pow_succ]; field_simp <;> ring
    _ ≤ 1 / (r : ℝ) ^ (E + 1) := one_div_le_one_div_of_le (by positivity) hrn

/-- Appendix B variance bound in the source's `n ≥ n₀(r)` form, with no regime hypothesis. -/
theorem VARf_capstone_large_n_bound {E : ℕ} (hE : 2 ≤ E) (x : Fin (E + 7) → ℤ) {n r h c : ℕ}
    (hn : 1 ≤ n) (hr : 1 ≤ r) (hrn : r ≤ n) (hn0 : 2 * r ^ (E + 1) ≤ n)
    (hc1 : 1 ≤ c) (h2c : 2 * c ≤ h) (h2h : 2 * h ≤ n)
    (hx : linfDist (0 : Fin (E + 7) → ℤ) x = n)
    (g F l : (Fin (E + 7) → ℤ) → ℝ) (tau : (Fin (E + 7) → ℤ) → (Fin (E + 7) → ℤ) → ℝ)
    (Var ρ : ℝ)
    {Cgo Cg CF CFr Ca Cb Cc Cτ Ct Cρ : ℝ}
    (hCgo : 0 ≤ Cgo) (hCg : 0 ≤ Cg) (hCF : 0 ≤ CF) (hCFr : 0 ≤ CFr) (hCa : 0 ≤ Ca)
    (hCb : 0 ≤ Cb) (hCc : 0 ≤ Cc) (hCτ : 0 ≤ Cτ) (hCt : 0 ≤ Ct)
    (hCρ : 0 ≤ Cρ) (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ Cρ)
    (hdecomp : Var ≤
      (n : ℝ) ^ 3 * ∑ u ∈ (sourceAnnulus n c : Finset (Fin (E + 7) → ℤ)),
          ∑ w ∈ (sourceAnnulus n c : Finset (Fin (E + 7) → ℤ)),
            g w * tau w u * tau u x * F w * F u +
        (n : ℝ) ^ 3 * ∑ u ∈ (sourceAnnulus n c : Finset (Fin (E + 7) → ℤ)),
          ∑ w ∈ (sourceAnnulus n c : Finset (Fin (E + 7) → ℤ)),
            g u * tau u w * tau u x * F w ^ 2 +
        (n : ℝ) ^ 3 * (ρ * ∑ u ∈ (sourceAnnulus h c : Finset (Fin (E + 7) → ℤ)),
          g u * tau u x * F u) +
        ∑ w ∈ (sourceAnnulus n c : Finset (Fin (E + 7) → ℤ)), g w * F w ^ 2)
    (hg0 : ∀ u ∈ (sourceAnnulus n c : Finset (Fin (E + 7) → ℤ)), 0 ≤ g u)
    (hF0 : ∀ u ∈ (sourceAnnulus n c : Finset (Fin (E + 7) → ℤ)), 0 ≤ F u)
    (htau0 : ∀ a ∈ (sourceAnnulus n c : Finset (Fin (E + 7) → ℤ)),
      ∀ b ∈ (sourceAnnulus n c : Finset (Fin (E + 7) → ℤ)), 0 ≤ tau a b)
    (htx0 : ∀ u ∈ (sourceAnnulus n c : Finset (Fin (E + 7) → ℤ)), 0 ≤ tau u x)
    (hl0 : ∀ u ∈ (sourceAnnulus n c : Finset (Fin (E + 7) → ℤ)), 0 ≤ l u)
    (hl : ∀ u ∈ (sourceAnnulus n c : Finset (Fin (E + 7) → ℤ)), l u ≤ (linfDist x u : ℝ))
    (hgo : ∀ w ∈ (capOuter n h c : Finset (Fin (E + 7) → ℤ)),
      (n : ℝ) ^ 3 * g w ≤ Cgo * ((linfDist x w + 1 : ℕ) : ℝ))
    (hgi : ∀ u ∈ (sourceAnnulus h c : Finset (Fin (E + 7) → ℤ)),
      g u ≤ Cg / ((sourceR c u : ℝ) + 1) ^ 2)
    (hF : ∀ u ∈ (sourceAnnulus n c : Finset (Fin (E + 7) → ℤ)),
      F u ≤ CF / (max (r : ℝ) ((linfDist x u + 1 : ℕ) : ℝ)) ^ (E + 3))
    (hFRD : ∀ u ∈ (sourceRD n c : Finset (Fin (E + 7) → ℤ)),
      F u ≤ CFr * ((sourceR c u : ℝ) + 1) / ((n : ℝ) ^ (E + 3) * (sParam c u : ℝ)))
    (htwu : ∀ w ∈ (sourceAnnulus n c : Finset (Fin (E + 7) → ℤ)),
      ∀ u ∈ (sourceAnnulus n c : Finset (Fin (E + 7) → ℤ)),
        tau w u ≤ Ca * (1 + l u) / ((linfDist w u + 1 : ℕ) : ℝ) ^ (E + 6))
    (htw_near : ∀ w ∈ (sourceAnnulus h c : Finset (Fin (E + 7) → ℤ)),
      ∀ u ∈ (sourceAnnulus n c : Finset (Fin (E + 7) → ℤ)), linfDist x u < (n - h) / 2 →
        tau w u ≤ Ca * (1 + l u) / (n : ℝ) ^ (E + 6))
    (htw : ∀ w ∈ (sourceAnnulus n c : Finset (Fin (E + 7) → ℤ)),
      ∀ u ∈ (sourceAnnulus n c : Finset (Fin (E + 7) → ℤ)),
        tau w u ≤ Cτ / ((linfDist w u + 1 : ℕ) : ℝ) ^ (E + 5))
    (htx : ∀ u ∈ (sourceAnnulus n c : Finset (Fin (E + 7) → ℤ)),
      tau u x ≤ Cb * (1 + l u) / ((linfDist x u + 1 : ℕ) : ℝ) ^ (E + 7))
    (htx_far : ∀ u ∈ (sourceAnnulus n c : Finset (Fin (E + 7) → ℤ)),
      (n - h) / 2 ≤ linfDist x u → tau u x ≤ Cc / (n : ℝ) ^ (E + 6))
    (htxRD : ∀ u ∈ (sourceRD n c : Finset (Fin (E + 7) → ℤ)),
      tau u x ≤ Ct * ((sourceR c u : ℝ) + 1) / ((n : ℝ) ^ (E + 6) * (sParam c u : ℝ))) :
    let C := varCapstoneConstant E Cgo Cg CF CFr Ca Cb Cc Cτ Ct
      (varBubbleConstant E Cgo CF Cb Cτ) Cρ 1
    0 ≤ C ∧ Var ≤ C / (r : ℝ) ^ (E + 7 - 6) :=
  VARf_capstone_full_bound hE x hn hr hrn hc1 h2c h2h hx g F l tau Var ρ hCgo hCg hCF hCFr hCa hCb
    hCc hCτ hCt hCρ zero_le_one hρ0 hρ hdecomp hg0 hF0 htau0 htx0 hl0 hl hgo hgi hF hFRD htwu
    htw_near htw htx htx_far htxRD (regime_of_large_n (by omega) hr hn0)

/-- Existential form of the large-cube capstone. -/
theorem VARf_capstone_large_n {E : ℕ} (hE : 2 ≤ E) (x : Fin (E + 7) → ℤ) {n r h c : ℕ}
    (hn : 1 ≤ n) (hr : 1 ≤ r) (hrn : r ≤ n) (hn0 : 2 * r ^ (E + 1) ≤ n)
    (hc1 : 1 ≤ c) (h2c : 2 * c ≤ h) (h2h : 2 * h ≤ n)
    (hx : linfDist (0 : Fin (E + 7) → ℤ) x = n)
    (g F l : (Fin (E + 7) → ℤ) → ℝ) (tau : (Fin (E + 7) → ℤ) → (Fin (E + 7) → ℤ) → ℝ)
    (Var ρ : ℝ)
    {Cgo Cg CF CFr Ca Cb Cc Cτ Ct Cρ : ℝ}
    (hCgo : 0 ≤ Cgo) (hCg : 0 ≤ Cg) (hCF : 0 ≤ CF) (hCFr : 0 ≤ CFr) (hCa : 0 ≤ Ca)
    (hCb : 0 ≤ Cb) (hCc : 0 ≤ Cc) (hCτ : 0 ≤ Cτ) (hCt : 0 ≤ Ct)
    (hCρ : 0 ≤ Cρ) (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ Cρ)
    (hdecomp : Var ≤
      (n : ℝ) ^ 3 * ∑ u ∈ (sourceAnnulus n c : Finset (Fin (E + 7) → ℤ)),
          ∑ w ∈ (sourceAnnulus n c : Finset (Fin (E + 7) → ℤ)),
            g w * tau w u * tau u x * F w * F u +
        (n : ℝ) ^ 3 * ∑ u ∈ (sourceAnnulus n c : Finset (Fin (E + 7) → ℤ)),
          ∑ w ∈ (sourceAnnulus n c : Finset (Fin (E + 7) → ℤ)),
            g u * tau u w * tau u x * F w ^ 2 +
        (n : ℝ) ^ 3 * (ρ * ∑ u ∈ (sourceAnnulus h c : Finset (Fin (E + 7) → ℤ)),
          g u * tau u x * F u) +
        ∑ w ∈ (sourceAnnulus n c : Finset (Fin (E + 7) → ℤ)), g w * F w ^ 2)
    (hg0 : ∀ u ∈ (sourceAnnulus n c : Finset (Fin (E + 7) → ℤ)), 0 ≤ g u)
    (hF0 : ∀ u ∈ (sourceAnnulus n c : Finset (Fin (E + 7) → ℤ)), 0 ≤ F u)
    (htau0 : ∀ a ∈ (sourceAnnulus n c : Finset (Fin (E + 7) → ℤ)),
      ∀ b ∈ (sourceAnnulus n c : Finset (Fin (E + 7) → ℤ)), 0 ≤ tau a b)
    (htx0 : ∀ u ∈ (sourceAnnulus n c : Finset (Fin (E + 7) → ℤ)), 0 ≤ tau u x)
    (hl0 : ∀ u ∈ (sourceAnnulus n c : Finset (Fin (E + 7) → ℤ)), 0 ≤ l u)
    (hl : ∀ u ∈ (sourceAnnulus n c : Finset (Fin (E + 7) → ℤ)), l u ≤ (linfDist x u : ℝ))
    (hgo : ∀ w ∈ (capOuter n h c : Finset (Fin (E + 7) → ℤ)),
      (n : ℝ) ^ 3 * g w ≤ Cgo * ((linfDist x w + 1 : ℕ) : ℝ))
    (hgi : ∀ u ∈ (sourceAnnulus h c : Finset (Fin (E + 7) → ℤ)),
      g u ≤ Cg / ((sourceR c u : ℝ) + 1) ^ 2)
    (hF : ∀ u ∈ (sourceAnnulus n c : Finset (Fin (E + 7) → ℤ)),
      F u ≤ CF / (max (r : ℝ) ((linfDist x u + 1 : ℕ) : ℝ)) ^ (E + 3))
    (hFRD : ∀ u ∈ (sourceRD n c : Finset (Fin (E + 7) → ℤ)),
      F u ≤ CFr * ((sourceR c u : ℝ) + 1) / ((n : ℝ) ^ (E + 3) * (sParam c u : ℝ)))
    (htwu : ∀ w ∈ (sourceAnnulus n c : Finset (Fin (E + 7) → ℤ)),
      ∀ u ∈ (sourceAnnulus n c : Finset (Fin (E + 7) → ℤ)),
        tau w u ≤ Ca * (1 + l u) / ((linfDist w u + 1 : ℕ) : ℝ) ^ (E + 6))
    (htw_near : ∀ w ∈ (sourceAnnulus h c : Finset (Fin (E + 7) → ℤ)),
      ∀ u ∈ (sourceAnnulus n c : Finset (Fin (E + 7) → ℤ)), linfDist x u < (n - h) / 2 →
        tau w u ≤ Ca * (1 + l u) / (n : ℝ) ^ (E + 6))
    (htw : ∀ w ∈ (sourceAnnulus n c : Finset (Fin (E + 7) → ℤ)),
      ∀ u ∈ (sourceAnnulus n c : Finset (Fin (E + 7) → ℤ)),
        tau w u ≤ Cτ / ((linfDist w u + 1 : ℕ) : ℝ) ^ (E + 5))
    (htx : ∀ u ∈ (sourceAnnulus n c : Finset (Fin (E + 7) → ℤ)),
      tau u x ≤ Cb * (1 + l u) / ((linfDist x u + 1 : ℕ) : ℝ) ^ (E + 7))
    (htx_far : ∀ u ∈ (sourceAnnulus n c : Finset (Fin (E + 7) → ℤ)),
      (n - h) / 2 ≤ linfDist x u → tau u x ≤ Cc / (n : ℝ) ^ (E + 6))
    (htxRD : ∀ u ∈ (sourceRD n c : Finset (Fin (E + 7) → ℤ)),
      tau u x ≤ Ct * ((sourceR c u : ℝ) + 1) / ((n : ℝ) ^ (E + 6) * (sParam c u : ℝ))) :
    ∃ C : ℝ, 0 ≤ C ∧ Var ≤ C / (r : ℝ) ^ (E + 7 - 6) := by
  obtain ⟨hC, hVar⟩ := VARf_capstone_large_n_bound hE x hn hr hrn hn0 hc1 h2c h2h hx g F l tau
    Var ρ hCgo hCg hCF hCFr hCa hCb hCc hCτ hCt hCρ hρ0 hρ hdecomp hg0 hF0 htau0 htx0
    hl0 hl hgo hgi hF hFRD htwu htw_near htw htx htx_far htxRD
  exact ⟨_, hC, hVar⟩

end NearCritical.AppendixVariance
