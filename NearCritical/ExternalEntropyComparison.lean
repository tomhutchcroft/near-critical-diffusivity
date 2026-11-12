module

public import Essakine2026Tight.Mathlib.InformationTheory.Pinsker
public import Essakine2026Tight.Mathlib.InformationTheory.KLBernstein
public import Essakine2026Tight.Mathlib.InformationTheory.KLStoppedPrefix
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
Entropy comparison machinery from RemyDegenne/entropy-mdp commit
611f5528b4d64035dac74f92da9eaa7831150180, using its pinned LML extension
commit dde3322b0a3978367029a100be43446ac8d04053. Apache licenses/copyright
headers and exact original hashes are retained in third_party.

Candidate integration step: KL-Bernstein plus the trivial event-probability
cap yields the refined sqrt(max probability * KL budget) dependence needed
by the paper's entropic comparison. Actual finite-halfspace transcript laws,
fresh-query conditional kernels, stopping rule and cluster-cost bound remain
UNPROVED bridges. This module and its new dependencies are UNCOMPILED locally.
-/
@[expose] public section
namespace NearCritical.External
open MeasureTheory ProbabilityTheory

/-- The existing Bernoulli relative-entropy upper bound, with all endpoint guards. -/
theorem bernoulli_kl_quadratic_upper {p q : ℝ}
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (hq : 0 < q) (hq1 : q < 1) :
    InformationTheory.klBerReal p q ≤ (p - q) ^ 2 / (q * (1 - q)) :=
  InformationTheory.klBerReal_le_div hp hp1 hq hq1

private theorem refined_of_bernstein {P Q a : ℝ} (hP : 0 ≤ P) (hQ : 0 ≤ Q)
    (ha : 0 ≤ a)
    (hB : |P - Q| ≤ Real.sqrt (2 * max P Q * a) + (2 / 3 : ℝ) * a) :
    |P - Q| ≤ 3 * Real.sqrt (max P Q * a) := by
  let M := max P Q
  have hPM : P ≤ M := le_max_left _ _
  have hQM : Q ≤ M := le_max_right _ _
  have hM : 0 ≤ M := hP.trans hPM
  let s := Real.sqrt (M * a)
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have hss : s ^ 2 = M * a := Real.sq_sqrt (mul_nonneg hM ha)
  change |P - Q| ≤ 3 * s
  by_cases haM : a ≤ M
  · have haa : a ^ 2 ≤ M * a := by
      nlinarith [mul_nonneg ha (sub_nonneg.mpr haM)]
    have has : a ≤ s := by nlinarith
    have ht : 0 ≤ 2 * M * a := mul_nonneg (mul_nonneg (by norm_num) hM) ha
    have hts : Real.sqrt (2 * M * a) ≤ 2 * s := by
      have ht0 := Real.sqrt_nonneg (2 * M * a)
      have ht2 := Real.sq_sqrt ht
      nlinarith [mul_nonneg hM ha]
    calc |P - Q| ≤ Real.sqrt (2 * M * a) + (2 / 3 : ℝ) * a := hB
      _ ≤ 3 * s := by nlinarith
  · have hMa : M ≤ a := le_of_lt (lt_of_not_ge haM)
    have hMM : M ^ 2 ≤ M * a := by
      nlinarith [mul_nonneg hM (sub_nonneg.mpr hMa)]
    have hMs : M ≤ s := by nlinarith
    have hcap : |P - Q| ≤ M := abs_le.mpr ⟨by linarith, by linarith⟩
    exact hcap.trans (by nlinarith)

/-- A refined event comparison from an actual KL budget, not an assumed event bound. -/
theorem event_difference_le_three_sqrt_max_kl {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (A : Set Ω) (hA : MeasurableSet A) {a : ℝ} (ha : 0 ≤ a)
    (hKL : InformationTheory.klDiv μ ν ≤ ENNReal.ofReal a) :
    |μ.real A - ν.real A| ≤ 3 * Real.sqrt (max (μ.real A) (ν.real A) * a) := by
  let f : Ω → ℝ := A.indicator (fun _ => 1)
  have hfm : Measurable f := measurable_const.indicator hA
  have hf : ∀ᵐ x ∂ν, f x ∈ Set.Icc 0 (1 : ℝ) :=
    Filter.Eventually.of_forall fun x => by
      by_cases hx : x ∈ A <;> simp [f, hx]
  have hμ : (∫ x, f x ∂μ) = μ.real A := by
    simp [f, integral_indicator_const (1 : ℝ) hA]
  have hν : (∫ x, f x ∂ν) = ν.real A := by
    simp [f, integral_indicator_const (1 : ℝ) hA]
  have hv : variance f ν ≤ ν.real A := by
    have h := variance_le_mul_integral hf hfm.aestronglyMeasurable
    simpa only [one_mul, hν] using h
  have hB := InformationTheory.abs_integral_sub_integral_le_of_klDiv_le
    (μ := μ) (ν := ν) (f := f) (a := a) (b := 1)
    (by norm_num) ha hf hfm.aestronglyMeasurable hKL
  rw [hμ, hν] at hB
  have hvm : variance f ν ≤ max (μ.real A) (ν.real A) :=
    hv.trans (le_max_right _ _)
  have hroot : Real.sqrt (2 * variance f ν * a) ≤
      Real.sqrt (2 * max (μ.real A) (ν.real A) * a) :=
    Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hvm (by norm_num)) ha)
  apply refined_of_bernstein (measureReal_nonneg) (measureReal_nonneg) ha
  calc |μ.real A - ν.real A| ≤ Real.sqrt (2 * variance f ν * a) + (2 / 3 : ℝ) * 1 * a := hB
    _ ≤ Real.sqrt (2 * max (μ.real A) (ν.real A) * a) + (2 / 3 : ℝ) * a := by
      simpa only [mul_one] using
        (add_le_add hroot (le_refl ((2 / 3 : ℝ) * a)))

end NearCritical.External
