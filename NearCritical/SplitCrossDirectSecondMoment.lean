module

public import NearCritical.Events
public import Mathlib.Algebra.QuadraticDiscriminant

/-! Generic second-moment bound (item A of the direct proof of
`SplitCrossInput`).

`sq_integral_le_integral_sq_mul_measure_ne_zero`: for a real random variable
`N` with `N` and `N^2` integrable under a finite measure,

  `(E[N])^2 <= E[N^2] * P[N != 0]`.

Proof: `0 <= E[(N - s 1{N != 0})^2] = E[N^2] - 2 s E[N] + s^2 P[N != 0]` for
every real `s`, so the discriminant is nonpositive.
-/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory Set

theorem sq_integral_le_integral_sq_mul_measure_ne_zero {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (N : Ω → ℝ) (hm : Measurable N)
    (hN : Integrable N μ) (hN2 : Integrable (fun ω => N ω ^ 2) μ) :
    (∫ ω, N ω ∂μ) ^ 2 ≤ (∫ ω, N ω ^ 2 ∂μ) * μ.real {ω | N ω ≠ 0} := by
  have hA : MeasurableSet {ω | N ω ≠ 0} := (hm (measurableSet_singleton 0)).compl
  have hind : Integrable ({ω | N ω ≠ 0}.indicator (fun _ => (1 : ℝ))) μ :=
    (integrable_const (1 : ℝ)).indicator hA
  have hquad : ∀ s : ℝ, 0 ≤ μ.real {ω | N ω ≠ 0} * (s * s) +
      (-2 * ∫ ω, N ω ∂μ) * s + ∫ ω, N ω ^ 2 ∂μ := by
    intro s
    have hpt : ∀ ω, (N ω - s * {ω | N ω ≠ 0}.indicator (fun _ => (1 : ℝ)) ω) ^ 2 =
        N ω ^ 2 - 2 * s * N ω + s * s * {ω | N ω ≠ 0}.indicator (fun _ => (1 : ℝ)) ω := by
      intro ω
      by_cases h : N ω = 0
      · have hmem : ω ∉ {ω | N ω ≠ 0} := fun hc => hc h
        rw [Set.indicator_of_notMem hmem, h]
        ring
      · have hmem : ω ∈ {ω | N ω ≠ 0} := h
        rw [Set.indicator_of_mem hmem]
        ring
    have h0 : 0 ≤ ∫ ω, (N ω - s * {ω | N ω ≠ 0}.indicator (fun _ => (1 : ℝ)) ω) ^ 2 ∂μ :=
      integral_nonneg (fun ω => sq_nonneg _)
    have hcalc : (∫ ω, (N ω - s * {ω | N ω ≠ 0}.indicator (fun _ => (1 : ℝ)) ω) ^ 2 ∂μ) =
        (∫ ω, N ω ^ 2 ∂μ) - 2 * s * (∫ ω, N ω ∂μ) + s * s * μ.real {ω | N ω ≠ 0} := by
      simp_rw [hpt]
      have h1 : (∫ ω, (N ω ^ 2 - 2 * s * N ω +
            s * s * {ω | N ω ≠ 0}.indicator (fun _ => (1 : ℝ)) ω) ∂μ) =
          (∫ ω, (N ω ^ 2 - 2 * s * N ω) ∂μ) +
            ∫ ω, s * s * {ω | N ω ≠ 0}.indicator (fun _ => (1 : ℝ)) ω ∂μ :=
        integral_add (hN2.sub (hN.const_mul (2 * s))) (hind.const_mul (s * s))
      have h2 : (∫ ω, (N ω ^ 2 - 2 * s * N ω) ∂μ) =
          (∫ ω, N ω ^ 2 ∂μ) - ∫ ω, 2 * s * N ω ∂μ :=
        integral_sub hN2 (hN.const_mul (2 * s))
      have h3 : (∫ ω, {ω | N ω ≠ 0}.indicator (fun _ => (1 : ℝ)) ω ∂μ) =
          μ.real {ω | N ω ≠ 0} := integral_indicator_one hA
      rw [h1, h2, integral_const_mul, integral_const_mul, h3]
    rw [hcalc] at h0
    linarith
  have hd := discrim_le_zero hquad
  unfold discrim at hd
  nlinarith [hd]

end NearCritical
