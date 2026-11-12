module

public import NearCritical.LatticeDifferential
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-! Integration of the square-root differential inequality in
`eq.upper_step_2plus`. Zero values of f are handled by epsilon regularization;
no strict positivity of f is assumed in the final theorem. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Set Filter MeasureTheory
open scoped Topology

/-- The regularized estimate used to integrate safely through zeros of f. -/
lemma sqrt_differential_integral_regularized {a b ε : ℝ} {f g : ℝ → ℝ}
    (hab : a ≤ b) (hε : 0 < ε)
    (hfcont : ContinuousOn f (Icc a b))
    (hf : ∀ x ∈ Ioo a b, DifferentiableAt ℝ f x)
    (hf0 : ∀ x ∈ Icc a b, 0 ≤ f x)
    (hgcont : ContinuousOn g (Icc a b))
    (hg0 : ∀ x ∈ Icc a b, 0 ≤ g x)
    (hdiff : ∀ x ∈ Ioo a b, deriv f x ≤ 2 * g x * Real.sqrt (f x)) :
    Real.sqrt (f b + ε) ≤ Real.sqrt (f a + ε) + ∫ x in a..b, g x := by
  let F : ℝ → ℝ := fun x ↦ Real.sqrt (f x + ε)
  let D : ℝ → ℝ := fun x ↦ deriv f x / (2 * Real.sqrt (f x + ε))
  have hF : ContinuousOn F (Icc a b) :=
    Real.continuous_sqrt.comp_continuousOn (hfcont.add continuousOn_const)
  have hD : ∀ x ∈ Ioo a b, HasDerivWithinAt F (D x) (Ioi x) x := by
    intro x hx
    have hx0 : 0 < f x + ε := by linarith [hf0 x ⟨hx.1.le, hx.2.le⟩]
    exact (((hf x hx).hasDerivAt.add_const ε).sqrt (ne_of_gt hx0)).hasDerivWithinAt
  have hle : ∀ x ∈ Ioo a b, D x ≤ g x := by
    intro x hx
    have hx0 : 0 < f x + ε := by linarith [hf0 x ⟨hx.1.le, hx.2.le⟩]
    have hsqrt : Real.sqrt (f x) ≤ Real.sqrt (f x + ε) := Real.sqrt_le_sqrt (by linarith)
    have hg := hg0 x ⟨hx.1.le, hx.2.le⟩
    apply (div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) (Real.sqrt_pos.mpr hx0))).mpr
    have hm := mul_le_mul_of_nonneg_left hsqrt hg
    nlinarith [hdiff x hx]
  have h := intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le hab hF hD
    hgcont.integrableOn_Icc hle
  dsimp [F] at h
  linarith

/-- Square-root integration for nonnegative f, including points where f=0.
Only differentiability on the open interval and continuity on the closed
interval are needed. This is the analytic step of `eq.upper_step_2plus`. -/
theorem sqrt_differential_integral {a b : ℝ} {f g : ℝ → ℝ}
    (hab : a ≤ b) (hfcont : ContinuousOn f (Icc a b))
    (hf : ∀ x ∈ Ioo a b, DifferentiableAt ℝ f x)
    (hf0 : ∀ x ∈ Icc a b, 0 ≤ f x)
    (hgcont : ContinuousOn g (Icc a b))
    (hg0 : ∀ x ∈ Icc a b, 0 ≤ g x)
    (hdiff : ∀ x ∈ Ioo a b, deriv f x ≤ 2 * g x * Real.sqrt (f x)) :
    Real.sqrt (f b) ≤ Real.sqrt (f a) + ∫ x in a..b, g x := by
  have hlim (c : ℝ) : Tendsto (fun n : ℕ ↦ Real.sqrt (c + 1 / ((n : ℝ) + 1)))
      atTop (𝓝 (Real.sqrt c)) := by
    have hc : Tendsto (fun n : ℕ ↦ c + 1 / ((n : ℝ) + 1)) atTop (𝓝 c) := by
      have heps : Tendsto (fun n : ℕ ↦ (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 (0 : ℝ)) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      have hcst : Tendsto (fun _ : ℕ ↦ c) atTop (𝓝 c) := tendsto_const_nhds
      simpa only [add_zero] using hcst.add heps
    exact Real.continuous_sqrt.continuousAt.tendsto.comp hc
  apply le_of_tendsto_of_tendsto' (hlim (f b)) ((hlim (f a)).add_const (∫ x in a..b, g x))
  intro n
  exact sqrt_differential_integral_regularized hab (by positivity) hfcont hf hf0 hgcont hg0 hdiff

/-- Constant-majorant form, with no positivity assumption on f beyond f>=0. -/
theorem sqrt_differential_constant {a b C : ℝ} {f : ℝ → ℝ}
    (hab : a ≤ b) (hC : 0 ≤ C) (hfcont : ContinuousOn f (Icc a b))
    (hf : ∀ x ∈ Ioo a b, DifferentiableAt ℝ f x)
    (hf0 : ∀ x ∈ Icc a b, 0 ≤ f x)
    (hdiff : ∀ x ∈ Ioo a b, deriv f x ≤ 2 * C * Real.sqrt (f x)) :
    Real.sqrt (f b) ≤ Real.sqrt (f a) + C * (b - a) := by
  have h := sqrt_differential_integral hab hfcont hf hf0 continuousOn_const (fun _ _ ↦ hC) hdiff
  simpa only [intervalIntegral.integral_const, smul_eq_mul, mul_comm] using h

/-- Integration when the differential inequality is bounded by a constant
multiple of sqrt(f)*sqrt(B), the form used after localizing p away from 0 and 1. -/
theorem sqrt_differential_integral_majorant {a b C : ℝ} {f B : ℝ → ℝ}
    (hab : a ≤ b) (hC : 0 ≤ C) (hfcont : ContinuousOn f (Icc a b))
    (hf : ∀ x ∈ Ioo a b, DifferentiableAt ℝ f x)
    (hf0 : ∀ x ∈ Icc a b, 0 ≤ f x) (hBcont : ContinuousOn B (Icc a b))
    (hdiff : ∀ x ∈ Ioo a b, deriv f x ≤ C * Real.sqrt (f x) * Real.sqrt (B x)) :
    Real.sqrt (f b) ≤ Real.sqrt (f a) + (C / 2) * ∫ x in a..b, Real.sqrt (B x) := by
  let g : ℝ → ℝ := fun x ↦ (C / 2) * Real.sqrt (B x)
  have hgcont : ContinuousOn g (Icc a b) :=
    continuousOn_const.mul (Real.continuous_sqrt.comp_continuousOn hBcont)
  have hg0 : ∀ x ∈ Icc a b, 0 ≤ g x := by
    intro x _
    exact mul_nonneg (div_nonneg hC (by norm_num)) (Real.sqrt_nonneg _)
  have hd : ∀ x ∈ Ioo a b, deriv f x ≤ 2 * g x * Real.sqrt (f x) := by
    intro x hx
    convert hdiff x hx using 1; dsimp [g]; ring
  have h := sqrt_differential_integral hab hfcont hf hf0 hgcont hg0 hd
  dsimp [g] at h
  rw [intervalIntegral.integral_const_mul] at h
  exact h

/-- A uniform bound for the source's factor on a compact interval contained
in (0,1), with the dependence on the interval endpoints kept explicit. -/
lemma reciprocal_sqrt_factor_le {a b x : ℝ} (ha : 0 < a) (hb : b < 1)
    (hx : x ∈ Icc a b) :
    1 / (Real.sqrt x * (1 - x)) ≤ 1 / (Real.sqrt a * (1 - b)) := by
  have hsa : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
  have hsx : 0 < Real.sqrt x := Real.sqrt_pos.mpr (ha.trans_le hx.1)
  have h1b : 0 < 1 - b := sub_pos.mpr hb
  have h1x : 0 < 1 - x := sub_pos.mpr (hx.2.trans_lt hb)
  have hden : Real.sqrt a * (1 - b) ≤ Real.sqrt x * (1 - x) := by
    apply (mul_le_mul_of_nonneg_left (sub_le_sub_left hx.2 1) hsa.le).trans
    exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hx.1) h1x.le
  apply (div_le_div_iff₀ (mul_pos hsx h1x) (mul_pos hsa h1b)).mpr
  simpa only [one_mul] using hden

/-- `eq.upper_step_2plus` with an explicit endpoint-dependent constant. The
interval containment 0<a<=b<1 is required, and f is allowed to vanish. -/
theorem sqrt_differential_integral_percolation_factor {a b : ℝ} {f B : ℝ → ℝ}
    (hab : a ≤ b) (ha : 0 < a) (hb : b < 1)
    (hfcont : ContinuousOn f (Icc a b))
    (hf : ∀ x ∈ Ioo a b, DifferentiableAt ℝ f x)
    (hf0 : ∀ x ∈ Icc a b, 0 ≤ f x) (hBcont : ContinuousOn B (Icc a b))
    (hdiff : ∀ x ∈ Ioo a b, deriv f x ≤
      Real.sqrt (f x) * Real.sqrt (B x) / (Real.sqrt x * (1 - x))) :
    Real.sqrt (f b) ≤ Real.sqrt (f a) +
      ((1 / (Real.sqrt a * (1 - b))) / 2) * ∫ x in a..b, Real.sqrt (B x) := by
  have hC : 0 ≤ 1 / (Real.sqrt a * (1 - b)) :=
    (div_pos (by norm_num : (0 : ℝ) < 1)
      (mul_pos (Real.sqrt_pos.mpr ha) (sub_pos.mpr hb))).le
  apply sqrt_differential_integral_majorant hab hC hfcont hf hf0 hBcont
  intro x hx
  have hfac := reciprocal_sqrt_factor_le ha hb ⟨hx.1.le, hx.2.le⟩
  have hm := mul_le_mul_of_nonneg_right hfac
    (mul_nonneg (Real.sqrt_nonneg (f x)) (Real.sqrt_nonneg (B x)))
  have heq : Real.sqrt (f x) * Real.sqrt (B x) / (Real.sqrt x * (1 - x)) =
      (1 / (Real.sqrt x * (1 - x))) *
        (Real.sqrt (f x) * Real.sqrt (B x)) := by ring
  have hd := hdiff x hx
  rw [heq] at hd
  have h := hd.trans hm
  convert h using 1; ring

lemma finiteExpectation_continuous {E : Type*} [Fintype E] (F : (E → Bool) → ℝ) :
    Continuous (fun p ↦ finiteExpectation p F) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  exact (finiteExpectation_hasDerivAt p F).continuousAt

lemma annealedRelaxed_continuous {d : ℕ} (U : Finset (Vertex d)) (i : Fin d) :
    Continuous (annealedRelaxed U i) :=
  finiteExpectation_continuous (localRelaxedConductivity U i)

lemma annealedB_continuous {d : ℕ} (U : Finset (Vertex d)) (i : Fin d) :
    Continuous (annealedB U i) := finiteExpectation_continuous (localB U i)

lemma localRelaxedConductivity_nonneg {d : ℕ} (U : Finset (Vertex d)) (i : Fin d)
    (η : IssuedBond U → Bool) : 0 ≤ localRelaxedConductivity U i η := by
  rw [localRelaxedConductivity_eq_binary]
  apply div_nonneg _ (Nat.cast_nonneg U.card)
  exact (issuedNetwork U).conductance_nonneg (Network.binaryWeights_nonneg η) _ _

lemma annealedRelaxed_nonneg {d : ℕ} (U : Finset (Vertex d)) (i : Fin d) {p : ℝ}
    (hp : 0 ≤ p) (hp1 : p ≤ 1) : 0 ≤ annealedRelaxed U i p :=
  finiteExpectation_nonneg hp hp1 (localRelaxedConductivity_nonneg U i)

/-- The source's actual `eq.upper_step_2plus`, with its suppressed constant
made explicit. There are no unproved differentiability, positivity, or pivotal
support hypotheses on the lattice conductivity. The interval stays inside
(0,1), exactly as required to control the source's derivative prefactor. -/
theorem annealedRelaxed_sqrt_integral {d : ℕ} {U : Finset (Vertex d)}
    (hU : U.Nonempty) (i : Fin d) {a b : ℝ} (hab : a ≤ b) (ha : 0 < a) (hb : b < 1) :
    Real.sqrt (annealedRelaxed U i b) ≤ Real.sqrt (annealedRelaxed U i a) +
      ((1 / (Real.sqrt a * (1 - b))) / 2) *
        ∫ x in a..b, Real.sqrt (annealedB U i x) := by
  apply sqrt_differential_integral_percolation_factor hab ha hb
    (annealedRelaxed_continuous U i).continuousOn
  · intro x _
    exact (finiteExpectation_hasDerivAt x (localRelaxedConductivity U i)).differentiableAt
  · intro x hx
    exact annealedRelaxed_nonneg U i (ha.le.trans hx.1) (hx.2.trans hb.le)
  · exact (annealedB_continuous U i).continuousOn
  · intro x hx
    exact annealedRelaxed_differential_inequality hU i (ha.trans hx.1) (hx.2.trans hb)

end NearCritical
