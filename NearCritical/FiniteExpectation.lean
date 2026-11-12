module

public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Fintype.Pi

/-! Polynomiality of expectations of arbitrary observables on a finite bond set.
The observable may be the degenerate Dirichlet conductance: it need not itself
be polynomial in the edge variables. This is the polynomiality part of
`pr:expansion_init`; the Russo derivative identity is a separate obligation. -/
@[expose] public section
namespace NearCritical
open Polynomial

section
variable {E : Type*} [Fintype E]

noncomputable def annealedPolynomial (f : (E → Bool) → ℝ) : Polynomial ℝ := by
  classical
  exact ∑ ω : E → Bool, C (f ω) * ∏ e : E, if ω e then X else 1 - X

noncomputable def finiteExpectation (p : ℝ) (f : (E → Bool) → ℝ) : ℝ := by
  classical
  exact ∑ ω : E → Bool, f ω * ∏ e : E, if ω e then p else 1 - p

lemma eval_annealedPolynomial (p : ℝ) (f : (E → Bool) → ℝ) :
    (annealedPolynomial f).eval p = finiteExpectation p f := by
  classical
  simp [annealedPolynomial, finiteExpectation, Polynomial.eval_finsetSum,
    Polynomial.eval_prod, apply_ite]

/-- The finite expectation is a polynomial on all real parameters. -/
theorem finiteExpectation_hasDerivAt (p : ℝ) (f : (E → Bool) → ℝ) :
    HasDerivAt (fun q ↦ finiteExpectation q f)
      ((annealedPolynomial f).derivative.eval p) p := by
  simpa only [eval_annealedPolynomial] using (annealedPolynomial f).hasDerivAt p

end
end NearCritical
