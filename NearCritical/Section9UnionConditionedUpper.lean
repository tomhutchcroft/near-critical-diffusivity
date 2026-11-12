module

public import NearCritical.Section9MeanUpperScale
import Mathlib.Tactic.Linarith

/-! The upper mean rate with the source F13 union conditioning, on each
positive reveal atom. This is not an almost-everywhere conditional-expectation
packaging, and the lower mean inequality remains a separate obligation. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory
open scoped Classical

lemma section9FiniteEndCubes_disjoint {d : ℕ} (i : Fin d) {n : ℕ} (hn : 0 < n) :
    Disjoint (section9FiniteEndCube i n 0) (section9FiniteEndCube i n (2*(n:ℝ))) := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  have hxShape := (Finset.mem_filter.mp hx).2
  have hyShape := (Finset.mem_filter.mp hy).2
  have hu := (hxShape i).2
  have hl := (hyShape i).1
  simp only [ite_true, sub_zero] at hu
  simp only [ite_true] at hl
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  linarith

/-- The literal source F13 is the union of the two revealed heart unions.
Its law agrees with pair conditioning because the source cubes are disjoint. -/
theorem section9FiniteRevealedLaw_eq_union {d : ℕ} (p : unitInterval) (i : Fin d)
    {n : ℕ} (hn : 0 < n) (H₁ H₃ F₁ F₃ : Finset (Vertex d))
    (hpos : percolation d p (section9RevealEvent
      (section9FiniteEndCube i n 0) H₁ (section9FiniteEndCube i n (2*(n:ℝ))) H₃ F₁ F₃) ≠ 0) :
    section9RevealedLaw p (section9FiniteEndCube i n 0) H₁
      (section9FiniteEndCube i n (2*(n:ℝ))) H₃ F₁ F₃ =
    ProbabilityTheory.cond (percolation d p) (section9RevealUnionEvent
      (section9FiniteEndCube i n 0) H₁ (section9FiniteEndCube i n (2*(n:ℝ))) H₃ (F₁ ∪ F₃)) := by
  exact section9RevealedLaw_eq_union_condition p _ H₁ _ H₃ F₁ F₃ hpos
    (section9FiniteEndCubes_disjoint i hn)

/-- Source upper mean scale for the actual F13 union-conditioned law, with a
single constant over all positive scales and all admissible positive atoms. -/
theorem section9UnionConditionalMean_upper_scale {d : ℕ} (hd : 2 ≤ d)
    (h : TwoPointAsymptotics d) :
    ∃ D : ℝ, 0 < D ∧ ∀ (i : Fin d) (n : ℕ), 0 < n →
      ∀ (H₁ H₃ F₁ F₃ A B : Finset (Vertex d)),
      H₁ ⊆ section9FiniteEndCube i n 0 → H₃ ⊆ section9FiniteEndCube i n (2*(n:ℝ)) →
      A ⊆ section9FiniteEndCube i n 0 → B ⊆ section9FiniteEndCube i n (2*(n:ℝ)) →
      percolation d (criticalPoint d) (section9RevealEvent
        (section9FiniteEndCube i n 0) H₁ (section9FiniteEndCube i n (2*(n:ℝ))) H₃ F₁ F₃) ≠ 0 →
      section9PivotalMean
        (ProbabilityTheory.cond (percolation d (criticalPoint d)) (section9RevealUnionEvent
          (section9FiniteEndCube i n 0) H₁ (section9FiniteEndCube i n (2*(n:ℝ))) H₃ (F₁ ∪ F₃)))
        (orientedLatticePairs (section9FiniteMiddle i n))
        (section9FiniteTube i n (-(5:ℝ)/8) (3/8))
        (section9FiniteTube i n (-(3:ℝ)/8) (5/8))
        (section9FiniteEndCube i n 0) F₁ (section9FiniteEndCube i n (2*(n:ℝ))) F₃ A B ≤
        D*(n:ℝ)^((4:ℝ)-(d:ℝ))*(A.card:ℝ)*(B.card:ℝ) := by
  obtain ⟨D,hD,hbound⟩ := section9ConditionalMean_upper_scale hd h
  refine ⟨D,hD,?_⟩
  intro i n hn H₁ H₃ F₁ F₃ A B hH₁ hH₃ hA hB hpos
  rw [← section9FiniteRevealedLaw_eq_union (criticalPoint d) i hn H₁ H₃ F₁ F₃ hpos]
  exact hbound i n hn H₁ H₃ F₁ F₃ A B hH₁ hH₃ hA hB hpos

end NearCritical
