module

public import NearCritical.FiniteTwoPhaseSlabDifferential
public import NearCritical.TwoPhaseSlabExhaustion
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! Lower-rate monotonicity for the actual mixed slab law. Finite Russo
positivity and closed-interval continuity suffice, including rates zero and
one. The full-profile limit keeps q, interface, top and all guards fixed. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Set Finset BernoulliCalculus
open scoped Classical ENNReal

private lemma twoPhase_row_opening_nonneg {d : ℕ} (U : Finset (Vertex d))
    (i : Fin d) (n : ℤ) (x : Vertex d) (j : ℤ) (e : internalBondSet U)
    (η : internalBondSet U → Bool) :
    0 ≤ finiteSlabRowObservable U i 0 n x j (forceOpen e η) -
      finiteSlabRowObservable U i 0 n x j η := by
  have hle : BK.ConfigLE η (forceOpen e η) := by
    intro f hf
    by_cases h : f = e <;> simp [forceOpen_eq_update, h, hf]
  apply sub_nonneg.mpr
  unfold finiteSlabRowObservable
  apply Finset.sum_le_sum
  intro y _
  by_cases hy : y i = j
  · simp only [ite_eq_left hy]
    by_cases hη : η ∈ finiteSlabLocalConnectionEvent U i 0 n x y
    · have hopen := finiteSlabLocalConnectionEvent_increasing U i 0 n x y hle hη
      simp [hη,hopen]
    · simp only [ite_eq_right hη]
      split_ifs <;> norm_num
  · simp only [ite_eq_right hy,le_refl]

private lemma twoPhase_row_deriv_nonneg {d : ℕ} (q : unitInterval)
    (U : Finset (Vertex d)) (i : Fin d) (m n : ℤ) (x : Vertex d) (j : ℤ)
    {t : ℝ} (ht : 0 ≤ t) (ht1 : t < 1) :
    0 ≤ deriv (fun s => finiteTwoPhaseSlabRowExpectation (q : ℝ) s U i m n x j) t := by
  rw [(finiteTwoPhaseSlabRowExpectation_russo (q : ℝ) t ht1.ne U i m n x j).deriv]
  apply mul_nonneg (inv_nonneg.mpr (sub_nonneg.mpr ht1.le))
  apply Finset.sum_nonneg
  intro e _
  unfold finiteExpectationProfile
  apply Finset.sum_nonneg
  intro η _
  apply mul_nonneg (twoPhase_row_opening_nonneg U i n x j e η)
  apply Finset.prod_nonneg
  intro f _
  have hr : 0 ≤ maskProfile (finiteTwoPhaseVariableMask U i m n) (q : ℝ) t f ∧
      maskProfile (finiteTwoPhaseVariableMask U i m n) (q : ℝ) t f ≤ 1 := by
    unfold maskProfile
    split_ifs
    · exact ⟨ht,ht1.le⟩
    · exact q.property
  split_ifs
  · exact hr.1
  · exact sub_nonneg.mpr hr.2

/-- Actual finite cutoff row means increase with the lower-phase rate.
Only interior rates are differentiated; continuity includes both endpoints. -/
theorem finiteTwoPhaseSlabRowMean_mono_lower_parameter {d : ℕ} (q : unitInterval)
    (U : Finset (Vertex d)) (i : Fin d) (m n : ℤ) (x : Vertex d) (j : ℤ)
    {p p' : unitInterval} (hpp' : p ≤ p') :
    finiteTwoPhaseSlabRowMean p q U i m n x j ≤
      finiteTwoPhaseSlabRowMean p' q U i m n x j := by
  have hd := (finiteTwoPhaseSlabRowExpectation_contDiff (1 : WithTop ℕ∞)
    (q : ℝ) U i m n x j).differentiable (by norm_num)
  have hmono : MonotoneOn
      (fun t => finiteTwoPhaseSlabRowExpectation (q : ℝ) t U i m n x j) (Icc (0 : ℝ) 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _) hd.continuous.continuousOn hd.differentiableOn
    intro t ht
    have ht' : t ∈ Ioo (0 : ℝ) 1 := by simpa only [interior_Icc] using ht
    exact twoPhase_row_deriv_nonneg q U i m n x j ht'.1.le ht'.2
  calc
    _ = finiteTwoPhaseSlabRowExpectation (q : ℝ) (p : ℝ) U i m n x j :=
      finiteTwoPhaseSlabRowMean_eq_expectation p q U i m n x j
    _ ≤ finiteTwoPhaseSlabRowExpectation (q : ℝ) (p' : ℝ) U i m n x j :=
      hmono p.property p'.property hpp'
    _ = _ := (finiteTwoPhaseSlabRowMean_eq_expectation p' q U i m n x j).symm

/-- The actual full mixed-slab mass is monotone in p with q, interface,
top, source and target heights unchanged; no summability is needed. -/
theorem twoPhaseSlabPioneerMass_mono_lower_parameter {d : ℕ} (i : Fin d)
    (q : unitInterval) (m n k j : ℤ) {p p' : unitInterval} (hpp' : p ≤ p') :
    twoPhaseSlabPioneerMass i p q m n k j ≤
      twoPhaseSlabPioneerMass i p' q m n k j := by
  simp only [twoPhaseSlabPioneerMass_eq_iSup_finiteRows]
  apply iSup_mono
  intro R
  exact ENNReal.ofReal_le_ofReal
    (finiteTwoPhaseSlabRowMean_mono_lower_parameter q (latticeSupCube d R) i m n
      (Pi.single i k) j hpp')

end NearCritical
