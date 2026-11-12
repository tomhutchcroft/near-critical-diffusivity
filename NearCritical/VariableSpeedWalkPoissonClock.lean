module

public import NearCritical.VariableSpeedWalkPoissonWindow
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! The exponential proposal clock has Poisson counts: the number of rate-`r`
exponential waiting times completed by time `t` is Poisson with mean `r t`.
This proves `ExponentialClockPoissonInput`, which was a premise of the
variable-speed walk diffusivity theorem.

The renewal recursion and the base case are in
`VariableSpeedWalkPoissonWindow`; here the recursion is solved by induction.

 -/
@[expose] public section
noncomputable section

namespace NearCritical

open Filter MeasureTheory ProbabilityTheory Set
open scoped Classical ENNReal NNReal

/-- One renewal step: integrating the Poisson weight of order `n` at the
remaining time against the first exponential wait gives the weight of order
`n + 1`. -/
theorem setLIntegral_expMeasure_poisson_step {r : ℝ} (hr : 0 < r) (n : ℕ) {t : ℝ}
    (ht : 0 ≤ t) :
    ∫⁻ s in Ioc 0 t, ENNReal.ofReal
        (Real.exp (-(r * (t - s))) * (r * (t - s)) ^ n / (n.factorial : ℝ)) ∂expMeasure r =
      ENNReal.ofReal (Real.exp (-(r * t)) * (r * t) ^ (n + 1) / ((n + 1).factorial : ℝ)) := by
  have hmeas : Measurable fun s : ℝ => ENNReal.ofReal
      (Real.exp (-(r * (t - s))) * (r * (t - s)) ^ n / (n.factorial : ℝ)) := by fun_prop
  have hpdf : Measurable (exponentialPDF r) := (measurable_exponentialPDFReal r).ennreal_ofReal
  have hE : expMeasure r = volume.withDensity (exponentialPDF r) := rfl
  let c : ℝ := r * Real.exp (-(r * t)) * r ^ n / (n.factorial : ℝ)
  have hfac : (0 : ℝ) < (n.factorial : ℝ) := by exact_mod_cast n.factorial_pos
  have hc : 0 ≤ c := by positivity
  rw [hE, setLIntegral_withDensity_eq_setLIntegral_mul _ hpdf hmeas measurableSet_Ioc]
  have hcongr : ∫⁻ s in Ioc 0 t, (exponentialPDF r * fun s : ℝ => ENNReal.ofReal
        (Real.exp (-(r * (t - s))) * (r * (t - s)) ^ n / (n.factorial : ℝ))) s =
      ∫⁻ s in Ioc 0 t, ENNReal.ofReal (c * (t - s) ^ n) := by
    apply setLIntegral_congr_fun measurableSet_Ioc
    intro s hs
    have hexp : Real.exp (-(r * s)) * Real.exp (-(r * (t - s))) = Real.exp (-(r * t)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    simp only [Pi.mul_apply]
    rw [exponentialPDF_of_nonneg hs.1.le, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    calc r * Real.exp (-(r * s)) *
          (Real.exp (-(r * (t - s))) * (r * (t - s)) ^ n / (n.factorial : ℝ))
        = r * (Real.exp (-(r * s)) * Real.exp (-(r * (t - s)))) * (r * (t - s)) ^ n /
            (n.factorial : ℝ) := by ring
      _ = c * (t - s) ^ n := by
          rw [hexp, mul_pow]
          simp only [c]
          ring
  rw [hcongr]
  have hcont : Continuous fun s : ℝ => c * (t - s) ^ n := by fun_prop
  have hint : IntegrableOn (fun s : ℝ => c * (t - s) ^ n) (Ioc 0 t) :=
    (hcont.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have hnn : 0 ≤ᵐ[volume.restrict (Ioc 0 t)] fun s : ℝ => c * (t - s) ^ n :=
    (ae_restrict_iff' measurableSet_Ioc).mpr (ae_of_all _ fun s hs =>
      mul_nonneg hc (pow_nonneg (by linarith [hs.2]) n))
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn]
  congr 1
  rw [← intervalIntegral.integral_of_le ht, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_sub_left (fun x : ℝ => x ^ n) t, integral_pow]
  have hn1 : ((n : ℝ) + 1) ≠ 0 := by positivity
  simp only [sub_self, sub_zero, c, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
    mul_pow, pow_succ]
  field_simp
  ring

/-- The finite-window probabilities are the Poisson weights. -/
theorem waitingCountWindow_measure {r : ℝ} (hr : 0 < r) (n : ℕ) :
    ∀ t : ℝ, 0 ≤ t → waitingPrefixLaw r (n + 1) (waitingCountWindow n t) =
      ENNReal.ofReal (Real.exp (-(r * t)) * (r * t) ^ n / (n.factorial : ℝ)) := by
  induction n with
  | zero =>
    intro t ht
    rw [waitingCountWindow_zero_measure hr ht]
    simp
  | succ n ih =>
    intro t ht
    rw [waitingCountWindow_succ_measure hr n t,
      setLIntegral_congr_fun measurableSet_Ioc
        (fun s (hs : s ∈ Ioc 0 t) => ih (t - s) (by linarith [hs.2]))]
    exact setLIntegral_expMeasure_poisson_step hr n ht

/-- **The exponential clock has Poisson counts.** -/
theorem exponentialClockPoissonInput : ExponentialClockPoissonInput := by
  intro r t hr ht
  apply Measure.ext_of_singleton
  intro n
  rw [waitingCount_singleton_eq_window hr ht n, waitingCountWindow_measure hr n t ht,
    poissonMeasure_singleton, Real.coe_toNNReal _ (mul_nonneg hr.le ht)]

end NearCritical
