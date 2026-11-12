module
public import NearCritical.SqrtDifferentialIntegration
public import NearCritical.SubcriticalKernelIntegral
public import NearCritical.SubcriticalSeed

/-! NEW homogeneous upper-log finite-volume analytic deduction. Pointwise
energy bounds in the modular interface are NEW premises, not standard results;
the consumer instantiates them from proved actual finite-cube prior bounds. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Set MeasureTheory

lemma sqrt_exp_envelope {X Q h c t : ℝ} (hQ : 0 ≤ Q) (hh : 0 < h)
    (hX : X ≤ (Q/h^2)*Real.exp (-c*h*t)) :
    Real.sqrt X ≤ (Real.sqrt Q/h)*Real.exp (-(c/2)*h*t) := by
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, hX.trans_eq ?_⟩
  rw [mul_pow, div_pow, Real.sq_sqrt hQ]
  have he : Real.exp (-(c/2)*h*t)^2 = Real.exp (-c*h*t) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [he]

/-- Actual homogeneous finite-volume integration, including zeros of the
conductivity. This is NOT the bulk/masked perturbation theorem. -/
theorem annealedRelaxed_upper_of_homogeneous_envelopes {d : ℕ} {U : Finset (Vertex d)}
    (hU : U.Nonempty) (i : Fin d) {h c K K0 a pc p : ℝ}
    (hh : 0 < h) (hc : 0 < c) (hK : 0 ≤ K) (hK0 : 0 ≤ K0)
    (hapc : a ≤ pc) (hpcp : pc ≤ p) (ha : 0 < a) (hp : p < 1)
    (hwindow : p-pc ≤ 1/h^2)
    (hseed : Real.sqrt (annealedRelaxed U i a) ≤ K0/h^3)
    (hsub : ∀ x ∈ Icc a pc, Real.sqrt (annealedB U i x) ≤
      (K/h)*Real.exp (-(c*h)*Real.sqrt (pc-x)))
    (hsup : ∀ x ∈ Icc pc p, Real.sqrt (annealedB U i x) ≤ K/h) :
    annealedRelaxed U i p ≤
      (K0+((1/(Real.sqrt a*(1-p)))/2)*(2*K/c^2+K))^2/h^6 := by
  let f := fun x => Real.sqrt (annealedB U i x)
  have hf : Continuous f := Real.continuous_sqrt.comp (annealedB_continuous U i)
  have hint := upper_perturbation_integral_le hapc hpcp hh hc hK hwindow
    (hf.intervalIntegrable a pc) (hf.intervalIntegrable pc p) hsub hsup
  let D := (1/(Real.sqrt a*(1-p)))/2
  have hD : 0 ≤ D := by dsimp [D]; positivity
  let Z := K0+D*(2*K/c^2+K)
  have hZ : 0 ≤ Z := by dsimp [Z]; positivity
  have H := annealedRelaxed_sqrt_integral hU i (hapc.trans hpcp) ha hp
  have Hsqrt : Real.sqrt (annealedRelaxed U i p) ≤ Z/h^3 := by
    apply H.trans
    calc
      _ ≤ K0/h^3+D*((2*K/c^2+K)/h^3) :=
        add_le_add hseed (mul_le_mul_of_nonneg_left hint hD)
      _ = _ := by dsimp [Z]; ring
  have hA := annealedRelaxed_nonneg U i (ha.le.trans (hapc.trans hpcp)) hp.le
  have Hsq := (sq_le_sq₀ (Real.sqrt_nonneg _) (div_nonneg hZ (pow_nonneg hh.le _))).mpr Hsqrt
  rw [Real.sq_sqrt hA] at Hsq
  convert Hsq using 1
  ring

/-- Close the actual homogeneous square-root integration at the explicit
subcritical seed. The log factor is retained in the final bound. -/
theorem annealedRelaxed_log_upper_of_prior_bounds {d : ℕ} {U : Finset (Vertex d)}
    (hU : U.Nonempty) (i : Fin d) {h c Q pc p : ℝ}
    (hh : 1 ≤ h) (hc : 0 < c) (hQ : 0 ≤ Q)
    (ha : 0 < subcriticalSeedParameter pc c h) (hpcp : pc ≤ p) (hp : p < 1)
    (hwindow : p-pc ≤ 1/h^2)
    (hstart : annealedRelaxed U i (subcriticalSeedParameter pc c h) ≤
      (Q/h^2)*Real.log h*Real.exp (-c*h*Real.sqrt (pc-subcriticalSeedParameter pc c h)))
    (hsub : ∀ x ∈ Icc (subcriticalSeedParameter pc c h) pc,
      annealedB U i x ≤ (Q/h^2)*Real.log h*Real.exp (-c*h*Real.sqrt (pc-x)))
    (hsup : ∀ x ∈ Icc pc p, annealedB U i x ≤ (Q/h^2)*Real.log h) :
    annealedRelaxed U i p ≤
      Q*(1+Real.log h)*(1+((1/(Real.sqrt (subcriticalSeedParameter pc c h)*(1-p)))/2)*
        (2/(c/2)^2+1))^2/h^6 := by
  have hh0 : 0 < h := lt_of_lt_of_le zero_lt_one hh
  have hl : 0 ≤ Real.log h := Real.log_nonneg hh
  let K := Real.sqrt (Q*(1+Real.log h))
  have hK : 0 ≤ K := Real.sqrt_nonneg _
  have hQK : Real.sqrt Q ≤ K := Real.sqrt_le_sqrt (by nlinarith)
  have hseed := (subcritical_seed_sqrt_bound hc hh hQ hstart).trans
    (div_le_div_of_nonneg_right hQK (by positivity : 0 ≤ h^3))
  have hsub' : ∀ x ∈ Icc (subcriticalSeedParameter pc c h) pc,
      Real.sqrt (annealedB U i x) ≤ (K/h)*Real.exp (-((c/2)*h)*Real.sqrt (pc-x)) := by
    intro x hx
    have hb : annealedB U i x ≤ (Q*(1+Real.log h)/h^2)*Real.exp (-c*h*Real.sqrt (pc-x)) := by
      apply (hsub x hx).trans
      apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
      calc
        _ = Q*Real.log h/h^2 := by ring
        _ ≤ _ := div_le_div_of_nonneg_right (by nlinarith) (sq_nonneg h)
    simpa only [K, neg_mul, mul_assoc] using sqrt_exp_envelope (by positivity) hh0 hb
  have hsup' : ∀ x ∈ Icc pc p, Real.sqrt (annealedB U i x) ≤ K/h := by
    intro x hx
    have hb : annealedB U i x ≤ Q*(1+Real.log h)/h^2 := by
      apply (hsup x hx).trans
      calc
        _ = Q*Real.log h/h^2 := by ring
        _ ≤ _ := div_le_div_of_nonneg_right (by nlinarith) (sq_nonneg h)
    calc
      _ ≤ Real.sqrt (Q*(1+Real.log h)/h^2) := Real.sqrt_le_sqrt hb
      _ = K/h := by rw [Real.sqrt_div (by positivity), Real.sqrt_sq hh0.le]
  have H := annealedRelaxed_upper_of_homogeneous_envelopes hU i hh0 (by positivity : 0 < c/2)
    hK hK (subcriticalSeedParameter_le pc c h) hpcp ha hp hwindow hseed hsub' hsup'
  apply H.trans_eq
  have hsq : K^2 = Q*(1+Real.log h) := Real.sq_sqrt (by positivity)
  calc
    _ = K^2*(1+((1/(Real.sqrt (subcriticalSeedParameter pc c h)*(1-p)))/2)*
        (2/(c/2)^2+1))^2/h^6 := by ring
    _ = _ := by rw [hsq]

end NearCritical
