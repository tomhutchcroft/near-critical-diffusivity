module

public import NearCritical.BulkUpperFromEnvelopes
public import NearCritical.SubcriticalSeedWindow

/-! Uniform finite-volume cubic deduction in the new logarithm-removal proof.
The probability envelopes remain visible inputs; rounding, seed admissibility,
compact prefactor and conversion h^-6 to gap³ are proved internally. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Set

def correlationRadius (sharp gap : ℝ) : ℕ := ⌊(Real.sqrt (sharp/gap)-1)/2⌋₊

lemma correlationHeight_eq_radius (sharp gap : ℝ) :
    (correlationHeight sharp gap : ℝ) = 2*(correlationRadius sharp gap : ℝ)+1 := by
  simp [correlationHeight, oddCorrelationHeight, correlationRadius]

/-- One constant works for every sufficiently small gap and every transverse
width, given the stated uniform NEW probability envelopes on the actual cube. -/
theorem finiteCubicUpper_of_bulk_envelopes {d : ℕ} (i : Fin d)
    (δ pc sharp c K C : ℝ) (hpc : 0 < pc) (hpc1 : pc < 1)
    (hsharp : 0 < sharp) (hsharp1 : sharp ≤ 1) (hc : 0 < c) (hK : 0 ≤ K) (hC : 0 ≤ C) :
    ∃ ε D : ℝ, 0 < ε ∧ 0 < D ∧ ∀ (R : ℕ) (gap : ℝ), 0 < gap → gap ≤ ε →
      let h := (correlationHeight sharp gap : ℝ)
      let U := waterCube d i (correlationRadius sharp gap) R
      let p := pc+gap
      let a := subcriticalSeedParameter pc c h
      (annealedMaskedRelaxed U i (bulkBondMask U i h δ) p a ≤
        (C/h^2)*Real.log h*Real.exp (-c*h*Real.sqrt (pc-a))) →
      (∀ x ∈ Icc a pc, Real.sqrt (annealedMaskedB U i (bulkBondMask U i h δ) p x) ≤
        (K/h)*Real.exp (-(c*h)*Real.sqrt (pc-x))) →
      (∀ x ∈ Icc pc p, Real.sqrt (annealedMaskedB U i (bulkBondMask U i h δ) p x) ≤ K/h) →
      annealedRelaxed U i p ≤ D*gap^3 := by
  obtain ⟨ε0, hε0, hseed⟩ := correlation_seed_window hpc hsharp c
  let Q : ℝ := (1/(Real.sqrt (pc/2)*(1-(pc+1)/2)))/2
  have htop : 0 < 1-(pc+1)/2 := by linarith
  have hQ : 0 ≤ Q := by
    dsimp [Q]
    exact div_nonneg (div_nonneg zero_le_one
      (mul_nonneg (Real.sqrt_nonneg _) htop.le)) (by norm_num)
  let E : ℝ := 2*K/c^2+K
  have hE : 0 ≤ E := by dsimp [E]; positivity
  let X : ℝ := Real.sqrt C+Q*E
  have hX : 0 ≤ X := add_nonneg (Real.sqrt_nonneg _) (mul_nonneg hQ hE)
  let B : ℝ := 64*X^2/sharp^3
  have hB : 0 ≤ B := by dsimp [B]; positivity
  let D := B+1
  have hD : 0 < D := by dsimp [D]; positivity
  let ε := min ε0 (min (sharp/16) ((1-pc)/2))
  have hε : 0 < ε := by dsimp [ε]; positivity
  refine ⟨ε, D, hε, hD, ?_⟩
  intro R gap hgap hsmall
  let h : ℝ := (correlationHeight sharp gap : ℝ)
  let U := waterCube d i (correlationRadius sharp gap) R
  let p := pc+gap
  let a := subcriticalSeedParameter pc c h
  dsimp only
  intro hstart hsub hsup
  have hsmall0 : gap ≤ ε0 := hsmall.trans (min_le_left _ _)
  have hsmall1 : gap ≤ sharp/16 := hsmall.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hsmall2 : gap ≤ (1-pc)/2 := hsmall.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hwin := hseed gap hgap hsmall0
  have ha : 0 < a := by dsimp [a,h]; linarith [hwin.1]
  have hpbound : p ≤ (pc+1)/2 := by dsimp [p]; linarith
  have hp : p < 1 := by linarith
  have hpcp : pc ≤ p := by dsimp [p]; linarith
  have hh : 1 ≤ h := by
    have H := oddCorrelationHeight_pos (Real.sqrt (sharp/gap))
    have H' : 1 ≤ correlationHeight sharp gap := H
    change (1 : ℝ) ≤ (correlationHeight sharp gap : ℝ)
    exact_mod_cast H'
  have hwindow : p-pc ≤ 1/h^2 := by
    have H := correlationHeight_window hsharp hgap hsmall1
    have H' := div_le_div_of_nonneg_right hsharp1 (sq_nonneg h)
    simpa only [p, add_sub_cancel_left] using H.trans H'
  have H := annealedRelaxed_upper_of_bulk_probability_envelopes
    (waterCube_nonempty d i (correlationRadius sharp gap) R) i δ
    hh hc hK hC ha hpcp hp hwindow hstart hsub hsup
  let q : ℝ := (1/(Real.sqrt a*(1-p)))/2
  let Y : ℝ := Real.sqrt C+q*E
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hY : 0 ≤ Y := add_nonneg (Real.sqrt_nonneg _) (mul_nonneg hq hE)
  have hqQ : q ≤ Q := compact_bulk_factor_le hpc hpc1 hwin.1 hpbound
  have hYX : Y ≤ X := by
    dsimp [Y, X]
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_right hqQ hE)
  have hsq : Y^2 ≤ X^2 := (sq_le_sq₀ hY hX).mpr hYX
  have hscale := correlationHeight_inverse_six hsharp hgap hsmall1
  change annealedRelaxed U i p ≤ D*gap^3
  change annealedRelaxed U i p ≤ Y^2/h^6 at H
  calc
    _ ≤ Y^2/h^6 := H
    _ ≤ X^2/h^6 := div_le_div_of_nonneg_right hsq (pow_nonneg (by linarith [hh]) _)
    _ = X^2*(1/h^6) := by ring
    _ ≤ X^2*(64*gap^3/sharp^3) := mul_le_mul_of_nonneg_left hscale (sq_nonneg X)
    _ = B*gap^3 := by dsimp [B]; ring
    _ ≤ D*gap^3 := mul_le_mul_of_nonneg_right (by dsimp [D]; linarith) (pow_nonneg hgap.le _)

end NearCritical
