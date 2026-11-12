module

public import NearCritical.AppendixVarTerm13
public import NearCritical.AppendixVarTerm2

/-! Assembly of the four Appendix-B `var_term` bounds into the variance propositions
`prop.VARf1` / `prop.VARf2` (source/main.tex 3501/3509, proof 3627-3737).

The source proof bounds the conditional variance `var[ERE_i | x∈𝔠]` by the sum of EXACTLY the
four `var_term` left-hand sides (eqs. sunzi1, the F²-term, vskfnob, sunzi4), via Lemma
`lem.Ay1y2_diagrams` and Corollary `cor.PxinfC`, and then bounds each of the four by `r^{6-d}`
(the main text bounds the `Λ_n\Λ_{n/2}` part of the third; the Appendix — our `var_term_1..4` —
bounds the rest). This file provides the final arithmetic assembly: given the probabilistic
decomposition `Var ≤ T1+T2+T3+T4` (hypothesis `hdecomp`, = `lem.Ay1y2_diagrams` + `cor.PxinfC`,
genuinely probabilistic Appendix-A/main-text input) and the four `var_term` outputs
`∃ C ≥ 0, Tᵢ ≤ C/r^{d-6}` (exactly the conclusions of `var_term_1`, `var_term_2`, `var_term_3`,
`var_term_4`), it concludes `∃ C ≥ 0, Var ≤ C/r^{d-6}` — i.e. `var[ERE_i|x∈𝔠] ≲ r^{6-d}`, the
statement of `prop.VARf1`/`prop.VARf2`.

So `VARf_assembly` is the faithful formalization of how `var_term_1..4` combine into the variance
propositions, as a conditional reduction: the probabilistic variance decomposition is the only
remaining explicit hypothesis, and the four analytic bounds plug in directly. -/
@[expose] public section
namespace NearCritical.AppendixVariance
open scoped BigOperators

/-- `prop.VARf1`/`prop.VARf2` assembly: the conditional variance, decomposed (probabilistically)
as `Var ≤ T1+T2+T3+T4` with each `Tᵢ ≲ r^{6-d}` (the `var_term_i` outputs), satisfies
`Var ≲ r^{6-d}`. -/
theorem VARf_assembly {d r : ℕ} (Var T1 T2 T3 T4 : ℝ)
    (hdecomp : Var ≤ T1 + T2 + T3 + T4)
    (h1 : ∃ C : ℝ, 0 ≤ C ∧ T1 ≤ C / (r : ℝ) ^ (d - 6))
    (h2 : ∃ C : ℝ, 0 ≤ C ∧ T2 ≤ C / (r : ℝ) ^ (d - 6))
    (h3 : ∃ C : ℝ, 0 ≤ C ∧ T3 ≤ C / (r : ℝ) ^ (d - 6))
    (h4 : ∃ C : ℝ, 0 ≤ C ∧ T4 ≤ C / (r : ℝ) ^ (d - 6)) :
    ∃ C : ℝ, 0 ≤ C ∧ Var ≤ C / (r : ℝ) ^ (d - 6) := by
  obtain ⟨C1, hC1, hT1⟩ := h1
  obtain ⟨C2, hC2, hT2⟩ := h2
  obtain ⟨C3, hC3, hT3⟩ := h3
  obtain ⟨C4, hC4, hT4⟩ := h4
  refine ⟨C1 + C2 + C3 + C4, by linarith, le_trans hdecomp ?_⟩
  rw [add_div, add_div, add_div]
  linarith

end NearCritical.AppendixVariance
