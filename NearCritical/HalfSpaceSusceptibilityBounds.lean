module

public import NearCritical.HalfSpaceSusceptibility
public import NearCritical.PioneerZeroLayer
public import Mathlib.Analysis.SumIntegralComparisons
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! Quantitative source susceptibility bounds, consuming the shared exact
boundary identity. The cited p-weighted positive-height estimate is explicit;
zero-height control is supplied by PioneerZeroLayer. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Set MeasureTheory
open scoped Classical ENNReal

lemma ennreal_exp_nat_succ_sum_le {t : ℝ} (ht : 0 < t) :
    (∑' m : ℕ, ENNReal.ofReal (Real.exp (-t * (m + 1 : ℝ)))) ≤ ENNReal.ofReal t⁻¹ := by
  have hanti : AntitoneOn (fun x : ℝ => Real.exp (-t * x)) (Ici 0) := by
    intro x hx y hy hxy
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hxy (neg_nonpos.mpr ht.le))
  have hint := integrableOn_exp_mul_Ioi (show -t < 0 by linarith) 0
  have hnonneg : ∀ x ∈ Ioi (0 : ℝ), 0 ≤ Real.exp (-t * x) := fun x _ => (Real.exp_pos _).le
  have hs := hanti.summable_of_integrableOn_Ioi_zero hint hnonneg
  have hs' : Summable (fun m : ℕ => Real.exp (-t * (m + 1 : ℝ))) := by
    have h := hs.comp_injective Nat.succ_injective
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one, Nat.cast_succ] using h
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun m => (Real.exp_pos _).le) hs']
  apply ENNReal.ofReal_le_ofReal
  have h := hanti.tsum_add_one_le_integral hint hnonneg
  rw [integral_exp_mul_Ioi (show -t < 0 by linarith) 0] at h
  simpa only [Nat.cast_add, Nat.cast_one, mul_zero, Real.exp_zero, neg_div_neg_eq, one_div] using h

/-- Normalized form; the literal cited input and its division cost are below. -/
def PositiveHeightPioneerDecay {d : ℕ} (p : unitInterval) (i : Fin d) (C c : ℝ) : Prop :=
  ∀ m : ℕ, 1 ≤ m → halfSpacePioneerMass p i (m : ℤ) ≤
    ENNReal.ofReal (C * Real.exp (-c * Real.sqrt ((criticalPoint d : ℝ) - (p : ℝ)) * (m : ℝ)))

/-- Literal STANDARD source eq.expansion_12 upper input, Hutchcroft2023 Thm2.3:
p*psi is bounded, and only positive heights are included. -/
def WeightedPositiveHeightPioneerDecay {d : ℕ} (p : unitInterval) (i : Fin d) (C c : ℝ) : Prop :=
  ∀ m : ℕ, 1 ≤ m → ENNReal.ofReal (p : ℝ) * halfSpacePioneerMass p i (m : ℤ) ≤
    ENNReal.ofReal (C * Real.exp (-c * Real.sqrt ((criticalPoint d : ℝ) - (p : ℝ)) * (m : ℝ)))

theorem positiveHeightPioneerDecay_of_weighted {d : ℕ} (p : unitInterval) (i : Fin d)
    {C c : ℝ} (hC : 0 < C) (hpc : 0 < (criticalPoint d : ℝ))
    (hplo : (criticalPoint d : ℝ) / 2 ≤ (p : ℝ))
    (decay : WeightedPositiveHeightPioneerDecay p i C c) :
    PositiveHeightPioneerDecay p i (2 * C / (criticalPoint d : ℝ)) c := by
  have hp : 0 < (p : ℝ) := (half_pos hpc).trans_le hplo
  have hp0 : ENNReal.ofReal (p : ℝ) ≠ 0 := (ENNReal.ofReal_pos.mpr hp).ne'
  have hCP : C / (p : ℝ) ≤ 2 * C / (criticalPoint d : ℝ) := by
    apply (div_le_div_iff₀ hp hpc).mpr
    nlinarith
  intro m hm
  have he : halfSpacePioneerMass p i (m : ℤ) ≤ ENNReal.ofReal
      ((C * Real.exp (-c * Real.sqrt ((criticalPoint d : ℝ) - (p : ℝ)) * (m : ℝ))) / (p : ℝ)) := by
    rw [ENNReal.ofReal_div_of_pos hp]
    apply (ENNReal.le_div_iff_mul_le (.inl hp0) (.inl ENNReal.ofReal_ne_top)).mpr
    simpa only [mul_comm] using decay m hm
  apply he.trans (ENNReal.ofReal_le_ofReal ?_)
  convert mul_le_mul_of_nonneg_right hCP (Real.exp_pos
    (-c * Real.sqrt ((criticalPoint d : ℝ) - (p : ℝ)) * (m : ℝ))).le using 1
  ring

/-- Every height, including zero, has a uniform bound from positive-height
cited decay and the proved actual-law zero-layer inequality. -/
theorem halfSpace_pioneer_uniform_of_weighted {d : ℕ} (p : unitInterval) (i : Fin d)
    {C c : ℝ} (hC : 0 < C) (hc : 0 < c) (hpc : 0 < (criticalPoint d : ℝ))
    (hplo : (criticalPoint d : ℝ) / 2 ≤ (p : ℝ))
    (decay : WeightedPositiveHeightPioneerDecay p i C c) (m : ℕ) :
    halfSpacePioneerMass p i (m : ℤ) ≤ ENNReal.ofReal (4 * C / (criticalPoint d : ℝ) ^ 2) := by
  let K : ℝ := 2 * C / (criticalPoint d : ℝ)
  have hK : 0 < K := by dsimp [K]; positivity
  have hpos : ∀ j : ℕ, 1 ≤ j → halfSpacePioneerMass p i (j : ℤ) ≤ ENNReal.ofReal K := by
    intro j hj
    apply (positiveHeightPioneerDecay_of_weighted p i hC hpc hplo decay j hj).trans
    apply ENNReal.ofReal_le_ofReal
    have he : Real.exp (-c * Real.sqrt ((criticalPoint d : ℝ) - (p : ℝ)) * (j : ℝ)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hc.le) (Real.sqrt_nonneg _)) (Nat.cast_nonneg j))
    simpa only [mul_one] using mul_le_mul_of_nonneg_left he hK.le
  have hp : 0 < (p : ℝ) := (half_pos hpc).trans_le hplo
  by_cases hm : m = 0
  · subst m
    have hz := (halfSpace_pioneer_zero_mul_le_one p i).trans (hpos 1 (by omega))
    have hp0 : ENNReal.ofReal (p : ℝ) ≠ 0 := (ENNReal.ofReal_pos.mpr hp).ne'
    have hb : halfSpacePioneerMass p i 0 ≤ ENNReal.ofReal (K / (p : ℝ)) := by
      rw [ENNReal.ofReal_div_of_pos hp]
      apply (ENNReal.le_div_iff_mul_le (.inl hp0) (.inl ENNReal.ofReal_ne_top)).mpr
      simpa only [mul_comm] using hz
    have hzreal : K / (p : ℝ) ≤ 2 * K / (criticalPoint d : ℝ) := by
      apply (div_le_div_iff₀ hp hpc).mpr
      nlinarith
    have heq : 2 * K / (criticalPoint d : ℝ) = 4 * C / (criticalPoint d : ℝ) ^ 2 := by
      dsimp [K]
      ring
    exact hb.trans (ENNReal.ofReal_le_ofReal (heq ▸ hzreal))
  · apply (hpos m (by omega)).trans (ENNReal.ofReal_le_ofReal ?_)
    dsimp [K]
    apply (div_le_div_iff₀ hpc (sq_pos_of_pos hpc)).mpr
    have hpcle : (criticalPoint d : ℝ) ≤ 1 := (criticalPoint d).property.2
    have hs : (criticalPoint d : ℝ) ^ 2 ≤ 2 * (criticalPoint d : ℝ) := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ 2 * C)]

/-- Upper susceptibility deduction after normalization of the cited input. -/
theorem halfSpace_susceptibility_upper_of_pioneers {d : ℕ} (p : unitInterval) (i : Fin d)
    {C c : ℝ} (hC : 0 < C) (hc : 0 < c) (hpc : 0 < (criticalPoint d : ℝ))
    (hplo : (criticalPoint d : ℝ) / 2 ≤ (p : ℝ)) (hpp : (p : ℝ) < (criticalPoint d : ℝ))
    (decay : PositiveHeightPioneerDecay p i C c) :
    halfSpaceSusceptibility p i 0 ≤ ENNReal.ofReal ((2 * C / (criticalPoint d : ℝ) + C / c) /
      Real.sqrt ((criticalPoint d : ℝ) - (p : ℝ))) := by
  let s : ℝ := Real.sqrt ((criticalPoint d : ℝ) - (p : ℝ))
  let t : ℝ := c * s
  have hs : 0 < s := Real.sqrt_pos.mpr (sub_pos.mpr hpp)
  have ht : 0 < t := mul_pos hc hs
  have hp : 0 < (p : ℝ) := (half_pos hpc).trans_le hplo
  have hs1 : s ≤ 1 := Real.sqrt_le_one.mpr (by linarith [p.property.1, (criticalPoint d).property.2])
  have h1 : halfSpacePioneerMass p i 1 ≤ ENNReal.ofReal C := by
    apply (decay 1 (by omega)).trans
    apply ENNReal.ofReal_le_ofReal
    have he : Real.exp (-c * s * (1 : ℝ)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    simpa only [Nat.cast_one, mul_one] using mul_le_mul_of_nonneg_left he hC.le
  have h0 : halfSpacePioneerMass p i 0 ≤ ENNReal.ofReal (2 * C / (criticalPoint d : ℝ)) := by
    have hb := (halfSpace_pioneer_zero_mul_le_one p i).trans h1
    have hp0 : ENNReal.ofReal (p : ℝ) ≠ 0 := (ENNReal.ofReal_pos.mpr hp).ne'
    have hz : halfSpacePioneerMass p i 0 ≤ ENNReal.ofReal (C / (p : ℝ)) := by
      rw [ENNReal.ofReal_div_of_pos hp]
      apply (ENNReal.le_div_iff_mul_le (.inl hp0) (.inl ENNReal.ofReal_ne_top)).mpr
      simpa only [mul_comm] using hb
    apply hz.trans (ENNReal.ofReal_le_ofReal ?_)
    apply (div_le_div_iff₀ hp hpc).mpr
    nlinarith
  have htail : (∑' m : ℕ, halfSpacePioneerMass p i ((m + 1 : ℕ) : ℤ)) ≤ ENNReal.ofReal (C / t) := by
    calc
      _ ≤ ∑' m : ℕ, ENNReal.ofReal (C * Real.exp (-t * (m + 1 : ℝ))) := by
        apply ENNReal.tsum_le_tsum
        intro m
        simpa only [Nat.cast_add, Nat.cast_one, t, s, neg_mul] using decay (m + 1) (by omega)
      _ = ENNReal.ofReal C * ∑' m : ℕ, ENNReal.ofReal (Real.exp (-t * (m + 1 : ℝ))) := by
        simp_rw [ENNReal.ofReal_mul hC.le]
        rw [ENNReal.tsum_mul_left]
      _ ≤ ENNReal.ofReal C * ENNReal.ofReal t⁻¹ := mul_le_mul' (le_refl _) (ennreal_exp_nat_succ_sum_le ht)
      _ = _ := by rw [← ENNReal.ofReal_mul hC.le, div_eq_mul_inv]
  have hC0 : 0 ≤ 2 * C / (criticalPoint d : ℝ) := by positivity
  have hupper : 2 * C / (criticalPoint d : ℝ) + C / t ≤ (2 * C / (criticalPoint d : ℝ) + C / c) / s := by
    dsimp [t]
    rw [div_mul_eq_div_div, add_div]
    have hh : 2 * C / (criticalPoint d : ℝ) ≤ (2 * C / (criticalPoint d : ℝ)) / s := by
      apply (le_div_iff₀ hs).mpr
      nlinarith [mul_le_mul_of_nonneg_left hs1 hC0]
    exact add_le_add hh le_rfl
  calc
    _ = halfSpacePioneerMass p i 0 + ∑' m : ℕ, halfSpacePioneerMass p i ((m + 1 : ℕ) : ℤ) := by
      rw [halfSpace_susceptibility_eq_tsum_pioneers, tsum_eq_zero_add' ENNReal.summable]
      rfl
    _ ≤ ENNReal.ofReal (2 * C / (criticalPoint d : ℝ)) + ENNReal.ofReal (C / t) := add_le_add h0 htail
    _ = ENNReal.ofReal (2 * C / (criticalPoint d : ℝ) + C / t) :=
      (ENNReal.ofReal_add hC0 (div_nonneg hC.le ht.le)).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal hupper

theorem halfSpace_susceptibility_upper_of_weighted_pioneers {d : ℕ} (p : unitInterval) (i : Fin d)
    {C c : ℝ} (hC : 0 < C) (hc : 0 < c) (hpc : 0 < (criticalPoint d : ℝ))
    (hplo : (criticalPoint d : ℝ) / 2 ≤ (p : ℝ)) (hpp : (p : ℝ) < (criticalPoint d : ℝ))
    (decay : WeightedPositiveHeightPioneerDecay p i C c) :
    halfSpaceSusceptibility p i 0 ≤ ENNReal.ofReal
      ((4 * C / (criticalPoint d : ℝ) ^ 2 + 2 * C / ((criticalPoint d : ℝ) * c)) /
        Real.sqrt ((criticalPoint d : ℝ) - (p : ℝ))) := by
  have hu := halfSpace_susceptibility_upper_of_pioneers p i
    (by positivity : 0 < 2 * C / (criticalPoint d : ℝ)) hc hpc hplo hpp
    (positiveHeightPioneerDecay_of_weighted p i hC hpc hplo decay)
  convert hu using 1
  congr 1
  congr 1
  field_simp [hpc.ne', hc.ne']
  ring

theorem halfSpace_susceptibility_finite_of_weighted_pioneers {d : ℕ} (p : unitInterval) (i : Fin d)
    {C c : ℝ} (hC : 0 < C) (hc : 0 < c) (hpc : 0 < (criticalPoint d : ℝ))
    (hplo : (criticalPoint d : ℝ) / 2 ≤ (p : ℝ)) (hpp : (p : ℝ) < (criticalPoint d : ℝ))
    (decay : WeightedPositiveHeightPioneerDecay p i C c) : halfSpaceSusceptibility p i 0 < ⊤ :=
  (halfSpace_susceptibility_upper_of_weighted_pioneers p i hC hc hpc hplo hpp decay).trans_lt ENNReal.ofReal_lt_top

end NearCritical
