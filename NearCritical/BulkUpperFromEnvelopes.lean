module

public import NearCritical.BulkIntegration
public import NearCritical.SubcriticalKernelIntegral
public import NearCritical.SubcriticalSeed

/-! The new log-removal analytic deduction on the actual finite conductivity.
The initial value and b-delta envelopes are visible NEW-paper dependencies;
this theorem does not assert those probability estimates or homogenization. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory Set

/-- From the actual bulk envelopes and initial value, the finite conductivity
has order h^-6. The compact-interval prefactor remains explicit. -/
theorem annealedRelaxed_upper_of_bulk_envelopes {d : ℕ} {U : Finset (Vertex d)}
    (hU : U.Nonempty) (i : Fin d) (δ : ℝ) {h c K K0 a pc p : ℝ}
    (hh : 0 < h) (hc : 0 < c) (hK : 0 ≤ K) (hK0 : 0 ≤ K0)
    (hapc : a ≤ pc) (hpcp : pc ≤ p) (ha : 0 < a) (hp : p < 1)
    (hwindow : p-pc ≤ 1/h^2)
    (hseed : Real.sqrt (annealedMaskedRelaxed U i (bulkBondMask U i h δ) p a) ≤ K0/h^3)
    (hsub : ∀ x ∈ Icc a pc,
      Real.sqrt (annealedMaskedB U i (bulkBondMask U i h δ) p x) ≤
        (K/h)*Real.exp (-(c*h)*Real.sqrt (pc-x)))
    (hsup : ∀ x ∈ Icc pc p,
      Real.sqrt (annealedMaskedB U i (bulkBondMask U i h δ) p x) ≤ K/h) :
    annealedRelaxed U i p ≤
      (K0+((1/(Real.sqrt a*(1-p)))/2)*(2*K/c^2+K))^2/h^6 := by
  let M := bulkBondMask U i h δ
  let f := fun x ↦ Real.sqrt (annealedMaskedB U i M p x)
  have hf : Continuous f := Real.continuous_sqrt.comp
    (finiteExpectationProfile_mask_continuous M p (localMaskedB U i M))
  have hint := upper_perturbation_integral_le hapc hpcp hh hc hK hwindow
    (hf.intervalIntegrable a pc) (hf.intervalIntegrable pc p) hsub hsup
  let D : ℝ := (1/(Real.sqrt a*(1-p)))/2
  have hD : 0 ≤ D := by dsimp [D]; positivity
  let C : ℝ := K0+D*(2*K/c^2+K)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have H := annealedBulkRelaxed_sqrt_integral hU i h δ (hapc.trans hpcp) ha hp
  have Hsqrt : Real.sqrt (annealedRelaxed U i p) ≤ C/h^3 := by
    apply H.trans
    calc
      _ ≤ K0/h^3+D*((2*K/c^2+K)/h^3) :=
        add_le_add hseed (mul_le_mul_of_nonneg_left hint hD)
      _ = _ := by dsimp [C]; ring
  have hA : 0 ≤ annealedRelaxed U i p :=
    annealedRelaxed_nonneg U i (ha.le.trans (hapc.trans hpcp)) hp.le
  have Hsq := (sq_le_sq₀ (Real.sqrt_nonneg _) (div_nonneg hC (pow_nonneg hh.le _))).mpr Hsqrt
  rw [Real.sq_sqrt hA] at Hsq
  change annealedRelaxed U i p ≤ C^2/h^6
  convert Hsq using 1
  ring

/-- The integration prefactor is uniform on the source's compact pc window.
The right side depends on pc, not on the chosen p or subcritical endpoint a. -/
lemma compact_bulk_factor_le {q a p : ℝ} (hq : 0 < q) (hq1 : q < 1)
    (ha : q/2 ≤ a) (hp : p ≤ (q+1)/2) :
    (1/(Real.sqrt a*(1-p)))/2 ≤
      (1/(Real.sqrt (q/2)*(1-(q+1)/2)))/2 := by
  have hqa : 0 < q/2 := by positivity
  have ha0 : 0 < a := hqa.trans_le ha
  have hqp : 0 < 1-(q+1)/2 := by linarith
  have hden : Real.sqrt (q/2)*(1-(q+1)/2) ≤ Real.sqrt a*(1-p) := by
    apply (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt ha) hqp.le).trans
    exact mul_le_mul_of_nonneg_left (by linarith : 1-(q+1)/2 ≤ 1-p) (Real.sqrt_nonneg _)
  have hi := one_div_le_one_div_of_le (mul_pos (Real.sqrt_pos.mpr hqa) hqp) hden
  exact div_le_div_of_nonneg_right hi (by norm_num)

/-- The full new finite-volume analytic argument, using the explicit
subcritical starting parameter. The supplied probability envelopes are still
visible dependencies; no homogenized or random-walk claim is made. -/
theorem annealedRelaxed_upper_of_bulk_probability_envelopes {d : ℕ}
    {U : Finset (Vertex d)} (hU : U.Nonempty) (i : Fin d) (δ : ℝ)
    {h c K C pc p : ℝ} (hh : 1 ≤ h) (hc : 0 < c) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (ha : 0 < subcriticalSeedParameter pc c h) (hpcp : pc ≤ p) (hp : p < 1)
    (hwindow : p-pc ≤ 1/h^2)
    (hstart : annealedMaskedRelaxed U i (bulkBondMask U i h δ) p
      (subcriticalSeedParameter pc c h) ≤
      (C/h^2)*Real.log h*Real.exp (-c*h*Real.sqrt (pc-subcriticalSeedParameter pc c h)))
    (hsub : ∀ x ∈ Icc (subcriticalSeedParameter pc c h) pc,
      Real.sqrt (annealedMaskedB U i (bulkBondMask U i h δ) p x) ≤
        (K/h)*Real.exp (-(c*h)*Real.sqrt (pc-x)))
    (hsup : ∀ x ∈ Icc pc p,
      Real.sqrt (annealedMaskedB U i (bulkBondMask U i h δ) p x) ≤ K/h) :
    annealedRelaxed U i p ≤
      (Real.sqrt C+((1/(Real.sqrt (subcriticalSeedParameter pc c h)*(1-p)))/2)*
        (2*K/c^2+K))^2/h^6 := by
  exact annealedRelaxed_upper_of_bulk_envelopes hU i δ
    (lt_of_lt_of_le zero_lt_one hh) hc hK (Real.sqrt_nonneg _)
    (subcriticalSeedParameter_le pc c h) hpcp ha hp hwindow
    (subcritical_seed_sqrt_bound hc hh hC hstart) hsub hsup

end NearCritical
