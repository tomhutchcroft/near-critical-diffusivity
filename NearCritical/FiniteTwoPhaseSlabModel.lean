module

public import NearCritical.FiniteSlabPioneer
public import NearCritical.InhomogeneousExpectation
public import NearCritical.TwoPhaseSlab
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! Finite-cutoff model for the source two-phase slab. The upper rate q is
fixed and only the complementary p-bonds vary. The literal full internal-bond
mask includes irrelevant off-slab bonds; no height support or Russo envelope
is asserted here. All connection and nil-path conventions are inherited from
the actual finite slab events. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Set Finset MeasureTheory ProbabilityTheory
open scoped Classical

/-- p is used exactly on internal bonds not wholly in the strict upper phase.
In particular the interface-crossing bond remains variable. -/
def finiteTwoPhaseVariableMask {d : ℕ} (U : Finset (Vertex d)) (i : Fin d)
    (m n : ℤ) : Finset (internalBondSet U) :=
  Finset.univ.filter (fun e => ¬(e.val.1 ∈ finiteHeightSlab i (m+1) n ∧
    bondTip e.val ∈ finiteHeightSlab i (m+1) n))

lemma mem_finiteTwoPhaseVariableMask {d : ℕ} (U : Finset (Vertex d)) (i : Fin d)
    (m n : ℤ) (e : internalBondSet U) :
    e ∈ finiteTwoPhaseVariableMask U i m n ↔
      ¬(e.val.1 ∈ finiteHeightSlab i (m+1) n ∧
        bondTip e.val ∈ finiteHeightSlab i (m+1) n) := by
  simp only [finiteTwoPhaseVariableMask, Finset.mem_filter, Finset.mem_univ, true_and]

/-- Exact profile equality, including off-slab bonds; q is the FIXED argument
and p the VARIABLE argument of maskProfile. -/
lemma finiteTwoPhaseSlabProfile_restrict {d : ℕ} (U : Finset (Vertex d))
    (i : Fin d) (m n : ℤ) (p q : unitInterval) :
    (fun e : internalBondSet U => (twoPhaseSlabProfile i m n p q e.val : ℝ)) =
      maskProfile (finiteTwoPhaseVariableMask U i m n) (q : ℝ) (p : ℝ) := by
  funext e
  by_cases h : e.val.1 ∈ finiteHeightSlab i (m+1) n ∧
      bondTip e.val ∈ finiteHeightSlab i (m+1) n
  · simp [twoPhaseSlabProfile, maskProfile, mem_finiteTwoPhaseVariableMask, h]
  · simp [twoPhaseSlabProfile, maskProfile, mem_finiteTwoPhaseVariableMask, h]

/-- Real p-extension of the literal finite row; no maximum is differentiated. -/
def finiteTwoPhaseSlabRowExpectation {d : ℕ} (q p : ℝ)
    (U : Finset (Vertex d)) (i : Fin d) (m n : ℤ) (x : Vertex d) (j : ℤ) : ℝ :=
  finiteExpectationProfile (maskProfile (finiteTwoPhaseVariableMask U i m n) q p)
    (finiteSlabRowObservable U i 0 n x j)

/-- Actual infinite-profile finite-cutoff row mass. -/
def finiteTwoPhaseSlabRowMean {d : ℕ} (p q : unitInterval)
    (U : Finset (Vertex d)) (i : Fin d) (m n : ℤ) (x : Vertex d) (j : ℤ) : ℝ :=
  ∑ y ∈ U, if y i = j then
    (percolationProfile d (twoPhaseSlabProfile i m n p q)).real
      (finiteSlabConnectionEvent U i 0 n x y) else 0

/-- The extension is a finite sum of products of affine functions of p. -/
theorem finiteTwoPhaseSlabRowExpectation_contDiff {d : ℕ} (r : WithTop ℕ∞)
    (q : ℝ) (U : Finset (Vertex d)) (i : Fin d) (m n : ℤ)
    (x : Vertex d) (j : ℤ) :
    ContDiff ℝ r (fun p => finiteTwoPhaseSlabRowExpectation q p U i m n x j) := by
  unfold finiteTwoPhaseSlabRowExpectation finiteExpectationProfile
  apply ContDiff.sum
  intro η _
  apply contDiff_const.mul
  apply contDiff_prod
  intro e _
  have he : ContDiff ℝ r (fun p : ℝ =>
      maskProfile (finiteTwoPhaseVariableMask U i m n) q p e) := by
    by_cases h : e ∈ finiteTwoPhaseVariableMask U i m n
    · simpa only [maskProfile, if_pos h] using! (contDiff_id : ContDiff ℝ r (fun p : ℝ => p))
    · simpa only [maskProfile, if_neg h] using
        (contDiff_const : ContDiff ℝ r (fun _ : ℝ => q))
  by_cases hη : η e = true
  · simpa only [if_pos hη] using he
  · simpa only [if_neg hη] using contDiff_const.sub he

/-- Exact finite independent product law for the real extension at unit rates. -/
theorem integral_finiteTwoPhaseSlabRowObservable {d : ℕ} (p q : unitInterval)
    (U : Finset (Vertex d)) (i : Fin d) (m n : ℤ) (x : Vertex d) (j : ℤ) :
    (∫ η, finiteSlabRowObservable U i 0 n x j η
      ∂(Measure.pi (fun e : internalBondSet U =>
        bernoulliMeasure true false (twoPhaseSlabProfile i m n p q e.val)))) =
      finiteTwoPhaseSlabRowExpectation (q : ℝ) (p : ℝ) U i m n x j := by
  rw [integral_finite_bernoulliProfile, finiteTwoPhaseSlabProfile_restrict]
  rfl

/-- Actual cutoff-event probability equals its finite profile expectation. -/
lemma finiteTwoPhaseSlabConnectionEvent_probability {d : ℕ} (p q : unitInterval)
    (U : Finset (Vertex d)) (i : Fin d) (m n : ℤ) (x y : Vertex d) :
    (percolationProfile d (twoPhaseSlabProfile i m n p q)).real
        (finiteSlabConnectionEvent U i 0 n x y) =
      finiteExpectationProfile
        (maskProfile (finiteTwoPhaseVariableMask U i m n) (q : ℝ) (p : ℝ))
        (fun η => if η ∈ finiteSlabLocalConnectionEvent U i 0 n x y then 1 else 0) := by
  let A := finiteSlabLocalConnectionEvent U i 0 n x y
  let μ := percolationProfile d (twoPhaseSlabProfile i m n p q)
  have hA : MeasurableSet A := (Set.toFinite A).measurableSet
  have hrestrict : Measurable ((internalBondSet U).restrict :
      Configuration d → ((e : internalBondSet U) → Bool)) :=
    Finset.measurable_restrict (internalBondSet U)
  have hmeas : MeasurableSet {ω : Configuration d | (internalBondSet U).restrict ω ∈ A} := by
    convert! hA.preimage hrestrict using 1
  rw [finiteSlabConnectionEvent_eq_preimage]
  calc
    _ = ∫ ω, (if (internalBondSet U).restrict ω ∈ A then (1 : ℝ) else 0) ∂μ := by
      convert! (integral_indicator_one (μ := μ) hmeas).symm using 1
    _ = finiteExpectationProfile
        (fun e : internalBondSet U => (twoPhaseSlabProfile i m n p q e.val : ℝ))
        (fun η => if η ∈ A then 1 else 0) :=
      percolationProfile_cylinder_expectation d (twoPhaseSlabProfile i m n p q)
        (internalBondSet U) (fun η => if η ∈ A then 1 else 0)
    _ = _ := by rw [finiteTwoPhaseSlabProfile_restrict]

private lemma finiteExpectationProfile_finset_sum_model {E Y : Type*} [Fintype E]
    (r : E → ℝ) (s : Finset Y) (g : Y → (E → Bool) → ℝ) :
    finiteExpectationProfile r (fun η => ∑ y ∈ s, g y η) =
      ∑ y ∈ s, finiteExpectationProfile r (g y) := by
  simp only [finiteExpectationProfile, Finset.sum_mul]
  exact Finset.sum_comm

/-- The actual infinite-law finite row is the smooth real p-extension. -/
theorem finiteTwoPhaseSlabRowMean_eq_expectation {d : ℕ} (p q : unitInterval)
    (U : Finset (Vertex d)) (i : Fin d) (m n : ℤ) (x : Vertex d) (j : ℤ) :
    finiteTwoPhaseSlabRowMean p q U i m n x j =
      finiteTwoPhaseSlabRowExpectation (q : ℝ) (p : ℝ) U i m n x j := by
  unfold finiteTwoPhaseSlabRowMean finiteTwoPhaseSlabRowExpectation finiteSlabRowObservable
  rw [finiteExpectationProfile_finset_sum_model]
  apply Finset.sum_congr rfl
  intro y _
  by_cases hy : y i = j
  · simp only [if_pos hy]
    exact finiteTwoPhaseSlabConnectionEvent_probability p q U i m n x y
  · simp only [if_neg hy, finiteExpectationProfile, zero_mul, Finset.sum_const_zero]

/-- Exact infinite product cylinder law for the actual finite row count. -/
theorem integral_finiteTwoPhaseSlabRowCount {d : ℕ} (p q : unitInterval)
    (U : Finset (Vertex d)) (i : Fin d) (m n : ℤ) (x : Vertex d) (j : ℤ) :
    (∫ ω, finiteSlabRowCount U i 0 n x j ω
      ∂percolationProfile d (twoPhaseSlabProfile i m n p q)) =
      finiteTwoPhaseSlabRowExpectation (q : ℝ) (p : ℝ) U i m n x j := by
  calc
    _ = finiteExpectationProfile
        (fun e : internalBondSet U => (twoPhaseSlabProfile i m n p q e.val : ℝ))
        (finiteSlabRowObservable U i 0 n x j) := by
      simpa only [finiteSlabRowCount_eq_observable] using
        percolationProfile_cylinder_expectation d (twoPhaseSlabProfile i m n p q)
          (internalBondSet U) (finiteSlabRowObservable U i 0 n x j)
    _ = _ := by rw [finiteTwoPhaseSlabProfile_restrict]; rfl

end NearCritical
