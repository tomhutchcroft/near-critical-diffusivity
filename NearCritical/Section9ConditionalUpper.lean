module

public import NearCritical.Section9UnionExpectation

/-! Upper inequality for the actual conditional-expectation operator in
Section9. Target sets are fixed; no regularity is needed for this direction. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory ProbabilityTheory
open scoped Classical

/-- One positive constant bounds the actual conditional expectation given
F13, uniformly over positive scales and fixed target subsets of the end cubes.
The lower inequality and concentration require additional arguments. -/
theorem section9_condExp_union_upper_scale {d : ℕ} (hd : 2 ≤ d)
    (h : TwoPointAsymptotics d) :
    ∃ D : ℝ, 0 < D ∧ ∀ (i : Fin d) (n : ℕ), 0 < n →
      ∀ (H₁ H₃ A B : Finset (Vertex d)),
      H₁ ⊆ section9FiniteEndCube i n 0 →
      H₃ ⊆ section9FiniteEndCube i n (2*(n:ℝ)) →
      A ⊆ section9FiniteEndCube i n 0 →
      B ⊆ section9FiniteEndCube i n (2*(n:ℝ)) →
      ∀ᵐ ω ∂percolation d (criticalPoint d),
        ((percolation d (criticalPoint d))[
          section9AdaptivePivotalCount
            (orientedLatticePairs (section9FiniteMiddle i n))
            (section9FiniteTube i n (-(5:ℝ)/8) (3/8))
            (section9FiniteTube i n (-(3:ℝ)/8) (5/8))
            (section9FiniteEndCube i n 0) H₁
            (section9FiniteEndCube i n (2*(n:ℝ))) H₃ A B |
          (inferInstance : MeasurableSpace (Finset (Vertex d))).comap
            (fun ζ => heartClusterUnion ζ (section9FiniteEndCube i n 0) H₁ ∪
              heartClusterUnion ζ (section9FiniteEndCube i n (2*(n:ℝ))) H₃)] ω) ≤
          D*(n:ℝ)^((4:ℝ)-(d:ℝ))*(A.card:ℝ)*(B.card:ℝ) := by
  obtain ⟨D,hD,hbound⟩ := section9ConditionalMean_upper_scale hd h
  refine ⟨D,hD,?_⟩
  intro i n hn H₁ H₃ A B hH₁ hH₃ hA hB
  have hCE := section9_condExp_union_adaptive_eq_revealed_mean (criticalPoint d)
    (orientedLatticePairs (section9FiniteMiddle i n))
    (section9FiniteTube i n (-(5:ℝ)/8) (3/8))
    (section9FiniteTube i n (-(3:ℝ)/8) (5/8))
    (section9FiniteEndCube i n 0) H₁
    (section9FiniteEndCube i n (2*(n:ℝ))) H₃ A B hH₁ hH₃
    (section9FiniteEndCubes_disjoint i hn)
  filter_upwards [hCE, section9_ae_pair_reveal_nonzero (criticalPoint d)
    (section9FiniteEndCube i n 0) H₁
    (section9FiniteEndCube i n (2*(n:ℝ))) H₃] with ω hω hpos
  rw [hω]
  exact hbound i n hn H₁ H₃
    (heartClusterUnion ω (section9FiniteEndCube i n 0) H₁)
    (heartClusterUnion ω (section9FiniteEndCube i n (2*(n:ℝ))) H₃)
    A B hH₁ hH₃ hA hB hpos

end NearCritical
