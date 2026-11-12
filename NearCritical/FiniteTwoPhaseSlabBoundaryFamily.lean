module

public import NearCritical.FiniteTwoPhaseSlabModel
public import NearCritical.FiniteSlabDifferential

/-! The weighted finite boundary family for the source mixed slab bootstrap.
Only individual entries are smooth. Its actual finite maximum is never
assumed differentiable, and no cubic or critical-start estimate is input. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Set Finset MeasureTheory
open scoped Classical

def finiteTwoPhaseBoundaryFamily {d : ℕ} (q : unitInterval) (c : ℝ)
    (U : Finset (Vertex d)) (i : Fin d) (m N : ℤ)
    (a : FiniteSlabBoundaryIndex U i 0 N) (p : ℝ) : ℝ :=
  match a with
  | .inl _ => 0
  | .inr (.inl v) =>
      Real.exp (c*Real.sqrt ((criticalPoint d : ℝ)-(q : ℝ))*
        twoPhaseSlabDistance m (v.2.val i) v.1.val) *
      finiteTwoPhaseSlabRowExpectation (q : ℝ) p U i m v.1.val v.2.val v.1.val
  | .inr (.inr v) =>
      Real.exp (c*Real.sqrt ((criticalPoint d : ℝ)-(q : ℝ))*
        twoPhaseSlabDistance m v.1.val v.2.2.val) *
      finiteTwoPhaseSlabRowExpectation (q : ℝ) p U i m v.1.val v.2.1.val.val v.2.2.val

def finiteTwoPhaseBoundaryMaximum {d : ℕ} (q : unitInterval) (c p : ℝ)
    (U : Finset (Vertex d)) (i : Fin d) (m N : ℤ) : ℝ :=
  finiteFamilyMaximum (finiteTwoPhaseBoundaryFamily q c U i m N) p

lemma finiteTwoPhaseBoundaryMaximum_nonneg {d : ℕ} (q : unitInterval) (c p : ℝ)
    (U : Finset (Vertex d)) (i : Fin d) (m N : ℤ) :
    0 ≤ finiteTwoPhaseBoundaryMaximum q c p U i m N :=
  le_finiteFamilyMaximum (finiteTwoPhaseBoundaryFamily q c U i m N) (.inl ()) p

theorem finiteTwoPhaseBoundaryFamily_contDiff {d : ℕ} (order : WithTop ℕ∞)
    (q : unitInterval) (c : ℝ) (U : Finset (Vertex d)) (i : Fin d) (m N : ℤ)
    (a : FiniteSlabBoundaryIndex U i 0 N) :
    ContDiff ℝ order (finiteTwoPhaseBoundaryFamily q c U i m N a) := by
  cases a with
  | inl _ => exact contDiff_const
  | inr a =>
    cases a with
    | inl v =>
      exact contDiff_const.mul (finiteTwoPhaseSlabRowExpectation_contDiff order
        (q : ℝ) U i m v.1.val v.2.val v.1.val)
    | inr v =>
      exact contDiff_const.mul (finiteTwoPhaseSlabRowExpectation_contDiff order
        (q : ℝ) U i m v.1.val v.2.1.val.val v.2.2.val)

private lemma finiteTwoPhaseSlabRowMean_nonneg_model {d : ℕ} (p q : unitInterval)
    (U : Finset (Vertex d)) (i : Fin d) (m n : ℤ) (x : Vertex d) (j : ℤ) :
    0 ≤ finiteTwoPhaseSlabRowMean p q U i m n x j := by
  unfold finiteTwoPhaseSlabRowMean
  apply Finset.sum_nonneg
  intro y _
  split_ifs
  · exact measureReal_nonneg
  · exact le_rfl

lemma finiteTwoPhaseSlabRowExpectation_nonneg {d : ℕ} (p q : unitInterval)
    (U : Finset (Vertex d)) (i : Fin d) (m n : ℤ) (x : Vertex d) (j : ℤ) :
    0 ≤ finiteTwoPhaseSlabRowExpectation (q : ℝ) (p : ℝ) U i m n x j := by
  rw [← finiteTwoPhaseSlabRowMean_eq_expectation]
  exact finiteTwoPhaseSlabRowMean_nonneg_model p q U i m n x j

lemma finiteTwoPhaseBoundaryFamily_nonneg {d : ℕ} (p q : unitInterval) (c : ℝ)
    (U : Finset (Vertex d)) (i : Fin d) (m N : ℤ)
    (a : FiniteSlabBoundaryIndex U i 0 N) :
    0 ≤ finiteTwoPhaseBoundaryFamily q c U i m N a (p : ℝ) := by
  cases a with
  | inl _ => exact le_rfl
  | inr a =>
    cases a with
    | inl v =>
      exact mul_nonneg (Real.exp_nonneg _)
        (finiteTwoPhaseSlabRowExpectation_nonneg p q U i m v.1.val v.2.val v.1.val)
    | inr v =>
      exact mul_nonneg (Real.exp_nonneg _)
        (finiteTwoPhaseSlabRowExpectation_nonneg p q U i m v.1.val v.2.1.val.val v.2.2.val)

/-- Every weighted forward top-target row is a genuine entry of the family. -/
lemma finiteTwoPhase_forward_row_le_boundaryMaximum {d : ℕ} (p q : unitInterval)
    (c : ℝ) (U : Finset (Vertex d)) (i : Fin d) (m N h : ℤ)
    (hh : h ∈ Finset.Icc (0 : ℤ) N) (x : Vertex d) (hx : x ∈ U) :
    Real.exp (c*Real.sqrt ((criticalPoint d : ℝ)-(q : ℝ))*twoPhaseSlabDistance m (x i) h) *
      finiteTwoPhaseSlabRowMean p q U i m h x h ≤
        finiteTwoPhaseBoundaryMaximum q c (p : ℝ) U i m N := by
  rw [finiteTwoPhaseSlabRowMean_eq_expectation]
  exact le_finiteFamilyMaximum (finiteTwoPhaseBoundaryFamily q c U i m N)
    (.inr (.inl (⟨h,hh⟩,⟨x,hx⟩))) (p : ℝ)

/-- Backward top-start rows are included separately; no cutoff stationarity
or identification with a different forward finite row is used. -/
lemma finiteTwoPhase_backward_row_le_boundaryMaximum {d : ℕ} (p q : unitInterval)
    (c : ℝ) (U : Finset (Vertex d)) (i : Fin d) (m N h : ℤ)
    (hh : h ∈ Finset.Icc (0 : ℤ) N) (z : Vertex d) (hzU : z ∈ U)
    (hzh : z i = h) (k : ℤ) (hk : k ∈ Finset.Icc (0 : ℤ) h) :
    Real.exp (c*Real.sqrt ((criticalPoint d : ℝ)-(q : ℝ))*twoPhaseSlabDistance m h k) *
      finiteTwoPhaseSlabRowMean p q U i m h z k ≤
        finiteTwoPhaseBoundaryMaximum q c (p : ℝ) U i m N := by
  rw [finiteTwoPhaseSlabRowMean_eq_expectation]
  exact le_finiteFamilyMaximum (finiteTwoPhaseBoundaryFamily q c U i m N)
    (.inr (.inr ⟨⟨h,hh⟩,(⟨⟨z,hzU⟩,hzh⟩,⟨k,hk⟩)⟩)) (p : ℝ)

end NearCritical
