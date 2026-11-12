module

public import NearCritical.FiniteTwoPhaseSlabWeightedDifferential
public import Mathlib.Analysis.Calculus.Deriv.Mul

/-! Coordinatewise cubic derivatives for the actual finite mixed boundary
family. Only the individual smooth entries are differentiated, never their
finite maximum. -/
@[expose] public section
noncomputable section
namespace NearCritical
open scoped Classical

/-- Every actual weighted boundary coordinate obeys the same cubic estimate.
The dummy coordinate is constant; both physical boundary orientations use
smooth finite rows multiplied by weights independent of the variable p. -/
theorem finiteTwoPhaseBoundaryFamily_deriv_le_cubic {d : ℕ}
    (p q P : unitInterval) (hP : (P : ℝ) < 1) (hpP : p ≤ P) (hqP : q ≤ P)
    (hqpc : q ≤ criticalPoint d) (c : ℝ) (hc : 0 ≤ c)
    (U : Finset (Vertex d)) (i : Fin d) (m N : ℕ)
    (a : FiniteSlabBoundaryIndex U i 0 N) :
    deriv (finiteTwoPhaseBoundaryFamily q c U i m N a) (p : ℝ) ≤
      4*(d : ℝ)*Real.exp c*(m+1 : ℝ)*(N+1 : ℝ)*
        (finiteTwoPhaseBoundaryMaximum q c (p : ℝ) U i m N)^3 := by
  cases a with
  | inl _ =>
    have hM := finiteTwoPhaseBoundaryMaximum_nonneg q c (p : ℝ) U i m N
    change deriv (fun _ : ℝ => 0) (p : ℝ) ≤ _
    rw [deriv_const]
    positivity
  | inr a =>
    cases a with
    | inl v =>
      have hd := (finiteTwoPhaseSlabRowExpectation_contDiff (1 : WithTop ℕ∞)
        (q : ℝ) U i m v.1.val v.2.val v.1.val).differentiable (by norm_num)
      change deriv (fun t : ℝ =>
        Real.exp (c*Real.sqrt ((criticalPoint d : ℝ)-(q : ℝ))*
          twoPhaseSlabDistance m (v.2.val i) v.1.val) *
        finiteTwoPhaseSlabRowExpectation (q : ℝ) t U i m v.1.val v.2.val v.1.val)
          (p : ℝ) ≤ _
      rw [deriv_const_mul _ hd.differentiableAt]
      exact finiteTwoPhase_forward_weighted_deriv_le_cubic p q P hP hpP hqP hqpc c hc
        U i m N v.1.val v.1.property v.2.val v.2.property
    | inr v =>
      have hd := (finiteTwoPhaseSlabRowExpectation_contDiff (1 : WithTop ℕ∞)
        (q : ℝ) U i m v.1.val v.2.1.val.val v.2.2.val).differentiable (by norm_num)
      change deriv (fun t : ℝ =>
        Real.exp (c*Real.sqrt ((criticalPoint d : ℝ)-(q : ℝ))*
          twoPhaseSlabDistance m v.1.val v.2.2.val) *
        finiteTwoPhaseSlabRowExpectation (q : ℝ) t U i m v.1.val v.2.1.val.val v.2.2.val)
          (p : ℝ) ≤ _
      rw [deriv_const_mul _ hd.differentiableAt]
      exact finiteTwoPhase_backward_weighted_deriv_le_cubic p q P hP hpP hqP hqpc c hc
        U i m N v.1.val v.1.property v.2.1.val.val v.2.1.val.property v.2.1.property
          v.2.2.val v.2.2.property

end NearCritical
