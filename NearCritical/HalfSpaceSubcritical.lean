module

public import NearCritical.HalfSpacePioneerReduction
public import NearCritical.PercolationMonotonicity
public import NearCritical.HalfSpaceSusceptibilityBounds

/-! The NEW subcritical boundary-origin arm deduction in prop.onearm_half_plus.
Only the separately cited critical arm and positive-depth pioneer estimates
are inputs; the resulting exponential arm estimate is proved. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Set MeasureTheory
open scoped ENNReal

/-- STANDARD input eq.onearm_half: critical boundary one-arm upper estimate
(CH20 Proposition 3.1 / van2025one Theorem 1.2). -/
def HalfSpaceCriticalArmInput {d : ℕ} (i : Fin d) (A : ℝ) : Prop :=
  ∀ n : ℕ, 1 ≤ n → halfSpaceArmProbability (criticalPoint d) i (n : ℤ) ≤
    ENNReal.ofReal (A / (n : ℝ) ^ 3)

/-- Normalized positive-depth bound for the midpoint deduction. This is NOT
the literal cited p-weighted input; the final source theorem must derive it
by the proved division lemma under pc>0 and p>=pc/2. No m=0 bound. -/
def HalfSpacePioneerNormalizedInput {d : ℕ} (i : Fin d) (B b : ℝ) : Prop :=
  ∀ (p : unitInterval) (m : ℕ), 1 ≤ m →
    (criticalPoint d : ℝ) / 2 ≤ (p : ℝ) → p ≤ criticalPoint d →
    halfSpacePioneerMass p i (m : ℤ) ≤ ENNReal.ofReal
      (B * Real.exp (-b * Real.sqrt ((criticalPoint d : ℝ) - (p : ℝ)) * (m : ℝ)))

lemma halfSpaceArmProbability_mono {d : ℕ} {p q : unitInterval} (hpq : p ≤ q)
    (i : Fin d) (n : ℤ) : halfSpaceArmProbability p i n ≤ halfSpaceArmProbability q i n :=
  percolation_increasing_event_mono (measurableSet_connectionToSetEvent _ _ _)
    (connectionToSetEvent_increasing _ _ _) hpq

private lemma cubic_midpoint_bound {A N R : ℝ} (hA : 0 ≤ A) (hN : 0 < N)
    (hR : 0 < R) (hNR : N ≤ 2 * R) : A / R ^ 3 ≤ 8 * A / N ^ 3 := by
  apply (div_le_div_iff₀ (pow_pos hR 3) (pow_pos hN 3)).mpr
  calc
    A * N ^ 3 ≤ A * (2 * R) ^ 3 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hN.le hNR 3) hA
    _ = _ := by ring

private lemma midpoint_decay_bound {b t N L : ℝ} (hb : 0 ≤ b) (ht : 0 ≤ t)
    (hNL : N ≤ 3 * L) :
    Real.exp (-b * t * L) ≤ Real.exp (-(b / 3) * t * N) := by
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_left hNL (mul_nonneg hb ht)
  nlinarith

/-- NEW Step1 for the parameter range of the standard pioneer input. The
n=1 case is handled by probability<=1; no zero-depth pioneer bound is used. -/
theorem halfSpace_origin_subcritical_midrange_normalized {d : ℕ} (i : Fin d)
    {A B b : ℝ} (hA : 0 < A) (hB : 0 < B) (hb : 0 < b)
    (criticalArm : HalfSpaceCriticalArmInput i A)
    (pioneers : HalfSpacePioneerNormalizedInput i B b)
    (p : unitInterval) (hpLower : (criticalPoint d : ℝ) / 2 ≤ (p : ℝ))
    (hp : p ≤ criticalPoint d) (n : ℕ) (hn : 1 ≤ n) :
    halfSpaceArmProbability p i (n : ℤ) ≤ ENNReal.ofReal
      ((8 * A * B + Real.exp (b / 3)) / (n : ℝ) ^ 3 *
        Real.exp (-(b / 3) * Real.sqrt ((criticalPoint d : ℝ) - (p : ℝ)) * (n : ℝ))) := by
  let t := Real.sqrt ((criticalPoint d : ℝ) - (p : ℝ))
  have ht : 0 ≤ t := Real.sqrt_nonneg _
  have hC : 8 * A * B ≤ 8 * A * B + Real.exp (b / 3) :=
    le_add_of_nonneg_right (Real.exp_nonneg _)
  by_cases hn2 : 2 ≤ n
  · let l := n / 2
    let r := n - l
    have hl : 1 ≤ l := by dsimp [l]; omega
    have hr : 1 ≤ r := by dsimp [r, l]; omega
    have hln : l ≤ n := by dsimp [l]; omega
    have hNL : (n : ℝ) ≤ 3 * (l : ℝ) := by
      have hnat : n ≤ 3 * l := by dsimp [l]; omega
      exact_mod_cast hnat
    have hNR : (n : ℝ) ≤ 2 * (r : ℝ) := by
      have hnat : n ≤ 2 * r := by dsimp [r, l]; omega
      exact_mod_cast hnat
    have hN : 0 < (n : ℝ) := by positivity
    have hR : 0 < (r : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hr)
    have hψ := pioneers p l hl hpLower hp
    have hθ := (halfSpaceArmProbability_mono hp i (r : ℤ)).trans (criticalArm r hr)
    have hsplit := halfSpace_arm_le_pioneer_mul p i (l : ℤ) (n : ℤ)
      (by positivity) (by exact_mod_cast hln)
    have hnr : (n : ℤ) - (l : ℤ) = (r : ℤ) := by dsimp [r]; omega
    rw [hnr] at hsplit
    calc
      _ ≤ _ := hsplit
      _ ≤ ENNReal.ofReal (B * Real.exp (-b * t * (l : ℝ))) *
          ENNReal.ofReal (A / (r : ℝ) ^ 3) := mul_le_mul' hψ hθ
      _ = ENNReal.ofReal ((B * Real.exp (-b * t * (l : ℝ))) * (A / (r : ℝ) ^ 3)) :=
        (ENNReal.ofReal_mul (by positivity)).symm
      _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        have hdec := midpoint_decay_bound hb.le ht hNL
        have hcube := cubic_midpoint_bound hA.le hN hR hNR
        calc
          _ ≤ (B * Real.exp (-(b / 3) * t * (n : ℝ))) * (8 * A / (n : ℝ) ^ 3) :=
            mul_le_mul (mul_le_mul_of_nonneg_left hdec hB.le) hcube
              (by positivity) (by positivity)
          _ = (8 * A * B) / (n : ℝ) ^ 3 * Real.exp (-(b / 3) * t * (n : ℝ)) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_right
            (div_le_div_of_nonneg_right hC (by positivity)) (Real.exp_nonneg _)
  · have hn1 : n = 1 := by omega
    subst n
    have ht1 : t ≤ 1 := by
      apply Real.sqrt_le_one.mpr
      linarith [p.2.1, (criticalPoint d).2.2]
    have hreal : 1 ≤ (8 * A * B + Real.exp (b / 3)) * Real.exp (-(b / 3) * t) := by
      calc
        1 ≤ Real.exp (b / 3 + (-(b / 3) * t)) := by
          apply Real.one_le_exp_iff.mpr
          nlinarith
        _ = Real.exp (b / 3) * Real.exp (-(b / 3) * t) := Real.exp_add _ _
        _ ≤ _ := mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (by positivity)) (Real.exp_nonneg _)
    calc
      _ ≤ 1 := by exact prob_le_one
      _ = ENNReal.ofReal (1 : ℝ) := by simp
      _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        simpa only [Nat.cast_one, one_pow, div_one, mul_one] using hreal

private lemma decay_of_sqrt_comparison {b N s t : ℝ} (hb : 0 ≤ b) (hN : 0 ≤ N)
    (hst : t ≤ 2 * s) :
    Real.exp (-(b / 3) * s * N) ≤ Real.exp (-(b / 6) * t * N) := by
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_left hst (mul_nonneg hb hN)
  nlinarith

/-- Extend the NEW normalized midpoint estimate to all p<=pc by actual event
monotonicity. Clamping at pc/2 costs a factor two in the exponential constant. -/
theorem halfSpace_origin_subcritical_normalized {d : ℕ} (i : Fin d)
    {A B b : ℝ} (hA : 0 < A) (hB : 0 < B) (hb : 0 < b)
    (criticalArm : HalfSpaceCriticalArmInput i A)
    (pioneers : HalfSpacePioneerNormalizedInput i B b)
    (p : unitInterval) (hp : p ≤ criticalPoint d) (n : ℕ) (hn : 1 ≤ n) :
    halfSpaceArmProbability p i (n : ℤ) ≤ ENNReal.ofReal
      ((8 * A * B + Real.exp (b / 3)) / (n : ℝ) ^ 3 *
        Real.exp (-(b / 6) * Real.sqrt ((criticalPoint d : ℝ) - (p : ℝ)) * (n : ℝ))) := by
  let pHalf : unitInterval := ⟨(criticalPoint d : ℝ) / 2, by
    constructor
    · exact div_nonneg (criticalPoint d).2.1 (by norm_num)
    · linarith [(criticalPoint d).2.2]⟩
  have hHalfLE : pHalf ≤ criticalPoint d := by
    change (criticalPoint d : ℝ) / 2 ≤ (criticalPoint d : ℝ)
    linarith [(criticalPoint d).2.1]
  let q := max p pHalf
  have hpq : p ≤ q := le_max_left _ _
  have hqLower : (criticalPoint d : ℝ) / 2 ≤ (q : ℝ) :=
    show (pHalf : ℝ) ≤ (q : ℝ) from le_max_right _ _
  have hqpc : q ≤ criticalPoint d := max_le hp hHalfLE
  have hgap : Real.sqrt ((criticalPoint d : ℝ) - (p : ℝ)) ≤
      2 * Real.sqrt ((criticalPoint d : ℝ) - (q : ℝ)) := by
    by_cases hcase : pHalf ≤ p
    · dsimp only [q]
      rw [max_eq_left hcase]
      linarith [Real.sqrt_nonneg ((criticalPoint d : ℝ) - (p : ℝ))]
    · have hq : q = pHalf := max_eq_right (le_of_not_ge hcase)
      rw [hq]
      apply Real.sqrt_le_iff.mpr
      refine ⟨by positivity, ?_⟩
      rw [mul_pow, Real.sq_sqrt (sub_nonneg.mpr hHalfLE)]
      dsimp [pHalf]
      linarith [p.2.1, (criticalPoint d).2.1]
  calc
    _ ≤ halfSpaceArmProbability q i (n : ℤ) := halfSpaceArmProbability_mono hpq i _
    _ ≤ _ := halfSpace_origin_subcritical_midrange_normalized i hA hB hb
      criticalArm pioneers q hqLower hqpc n hn
    _ ≤ _ := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
      (decay_of_sqrt_comparison hb.le (Nat.cast_nonneg n) hgap) (by positivity))

/-- Literal STANDARD source expansion12 input over its stated parameter range.
The p factor is retained; no depth-zero statement is assumed. -/
def HalfSpacePioneerExponentialInput {d : ℕ} (i : Fin d) (B b : ℝ) : Prop :=
  ∀ p : unitInterval, (criticalPoint d : ℝ) / 2 ≤ (p : ℝ) → p ≤ criticalPoint d →
    WeightedPositiveHeightPioneerDecay p i B b

/-- Normalize the literal cited input using the separately proved division
lemma, retaining its explicit cost 2B/pc and the classical pc>0 input. -/
lemma halfSpacePioneerNormalizedInput_of_weighted {d : ℕ} (i : Fin d)
    {B b : ℝ} (hB : 0 < B) (hpc : 0 < (criticalPoint d : ℝ))
    (pioneers : HalfSpacePioneerExponentialInput i B b) :
    HalfSpacePioneerNormalizedInput i (2 * B / (criticalPoint d : ℝ)) b := by
  intro p m hm hplo hp
  exact positiveHeightPioneerDecay_of_weighted p i hB hpc hplo
    (pioneers p hplo hp) m hm

/-- NEW source Step1 from literal cited L1 and p-weighted L2. All scales n>=1,
odd midpoint cuts and all p<=pc are included; no new arm estimate is a premise. -/
theorem halfSpace_origin_subcritical {d : ℕ} (i : Fin d)
    {A B b : ℝ} (hA : 0 < A) (hB : 0 < B) (hb : 0 < b)
    (hpc : 0 < (criticalPoint d : ℝ))
    (criticalArm : HalfSpaceCriticalArmInput i A)
    (pioneers : HalfSpacePioneerExponentialInput i B b)
    (p : unitInterval) (hp : p ≤ criticalPoint d) (n : ℕ) (hn : 1 ≤ n) :
    halfSpaceArmProbability p i (n : ℤ) ≤ ENNReal.ofReal
      ((8 * A * (2 * B / (criticalPoint d : ℝ)) + Real.exp (b / 3)) / (n : ℝ) ^ 3 *
        Real.exp (-(b / 6) * Real.sqrt ((criticalPoint d : ℝ) - (p : ℝ)) * (n : ℝ))) :=
  halfSpace_origin_subcritical_normalized i hA (by positivity) hb criticalArm
    (halfSpacePioneerNormalizedInput_of_weighted i hB hpc pioneers) p hp n hn

/-- Real-probability form of the proved literal-source deduction. -/
theorem halfSpace_origin_subcritical_real {d : ℕ} (i : Fin d)
    {A B b : ℝ} (hA : 0 < A) (hB : 0 < B) (hb : 0 < b)
    (hpc : 0 < (criticalPoint d : ℝ))
    (criticalArm : HalfSpaceCriticalArmInput i A)
    (pioneers : HalfSpacePioneerExponentialInput i B b)
    (p : unitInterval) (hp : p ≤ criticalPoint d) (n : ℕ) (hn : 1 ≤ n) :
    (percolation d p).real (connectionToSetEvent {z | 0 ≤ z i} 0 {z | (n : ℤ) ≤ z i}) ≤
      (8 * A * (2 * B / (criticalPoint d : ℝ)) + Real.exp (b / 3)) / (n : ℝ) ^ 3 *
        Real.exp (-(b / 6) * Real.sqrt ((criticalPoint d : ℝ) - (p : ℝ)) * (n : ℝ)) := by
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (halfSpace_origin_subcritical i hA hB hb hpc criticalArm pioneers p hp n hn)
  have hnonneg : 0 ≤
      (8 * A * (2 * B / (criticalPoint d : ℝ)) + Real.exp (b / 3)) / (n : ℝ) ^ 3 *
        Real.exp (-(b / 6) * Real.sqrt ((criticalPoint d : ℝ) - (p : ℝ)) * (n : ℝ)) := by positivity
  rw [ENNReal.toReal_ofReal hnonneg] at h
  exact h

/-- The source's uniform-positive-constants formulation for origin arms,
conditional only on the named cited inputs and classical pc>0. -/
theorem halfSpace_origin_subcritical_constants {d : ℕ} (i : Fin d)
    {A B b : ℝ} (hA : 0 < A) (hB : 0 < B) (hb : 0 < b)
    (hpc : 0 < (criticalPoint d : ℝ))
    (criticalArm : HalfSpaceCriticalArmInput i A)
    (pioneers : HalfSpacePioneerExponentialInput i B b) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (p : unitInterval), p ≤ criticalPoint d →
      ∀ n : ℕ, 1 ≤ n → halfSpaceArmProbability p i (n : ℤ) ≤ ENNReal.ofReal
        (C / (n : ℝ) ^ 3 * Real.exp (-c * Real.sqrt ((criticalPoint d : ℝ) - (p : ℝ)) * (n : ℝ))) := by
  refine ⟨8 * A * (2 * B / (criticalPoint d : ℝ)) + Real.exp (b / 3), b / 6,
    by positivity, by positivity, ?_⟩
  intro p hp n hn
  exact halfSpace_origin_subcritical i hA hB hb hpc criticalArm pioneers p hp n hn

end NearCritical
