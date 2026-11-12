module

public import NearCritical.Section9UnionConditionedUpper

/-! Almost every realized reveal has a nonzero atom. This permits the actual
fixed-atom upper bound to be applied almost surely. Identifying the resulting
fiber formula with a conditional-expectation operator is a separate statement. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory
open scoped Classical

/-- A countable-valued observation almost surely takes a value whose fiber
has nonzero measure. No measurability assumption on the observation is needed. -/
lemma section9_ae_nonzero_fiber {α β : Type*} [MeasurableSpace α] [Countable β]
    (μ : Measure α) (f : α → β) : ∀ᵐ x ∂μ, μ {y | f y = f x} ≠ 0 := by
  have hall : ∀ a : β, ∀ᵐ x ∂μ, f x = a → μ {y | f y = a} ≠ 0 := by
    intro a
    by_cases ha : μ {y | f y = a} = 0
    · have hout : ∀ᵐ x ∂μ, f x ≠ a := by
        apply ae_iff.mpr
        simpa only [not_not] using ha
      filter_upwards [hout] with x hx
      intro hxa
      exact (hx hxa).elim
    · exact ae_of_all μ (fun _ _ => ha)
  filter_upwards [ae_all_iff.mpr hall] with x hx
  exact hx (f x) rfl

/-- The actual pair reveal has positive atom almost surely. -/
theorem section9_ae_pair_reveal_nonzero {d : ℕ} (p : unitInterval)
    (Q₁ H₁ Q₃ H₃ : Finset (Vertex d)) :
    ∀ᵐ ω ∂percolation d p, percolation d p (section9RevealEvent Q₁ H₁ Q₃ H₃
      (heartClusterUnion ω Q₁ H₁) (heartClusterUnion ω Q₃ H₃)) ≠ 0 := by
  let f : Configuration d → Finset (Vertex d) × Finset (Vertex d) := fun ω =>
    (heartClusterUnion ω Q₁ H₁, heartClusterUnion ω Q₃ H₃)
  filter_upwards [section9_ae_nonzero_fiber (percolation d p) f] with ω hω
  have heq : {ζ | f ζ = f ω} = section9RevealEvent Q₁ H₁ Q₃ H₃
      (heartClusterUnion ω Q₁ H₁) (heartClusterUnion ω Q₃ H₃) := by
    ext ζ
    simp only [f, Prod.mk.injEq, section9RevealEvent, Set.mem_setOf_eq]
  rwa [heq] at hω

/-- The literal source union reveal likewise has nonzero realized atom a.s. -/
theorem section9_ae_union_reveal_nonzero {d : ℕ} (p : unitInterval)
    (Q₁ H₁ Q₃ H₃ : Finset (Vertex d)) :
    ∀ᵐ ω ∂percolation d p, percolation d p (section9RevealUnionEvent Q₁ H₁ Q₃ H₃
      (heartClusterUnion ω Q₁ H₁ ∪ heartClusterUnion ω Q₃ H₃)) ≠ 0 := by
  let f : Configuration d → Finset (Vertex d) := fun ω =>
    heartClusterUnion ω Q₁ H₁ ∪ heartClusterUnion ω Q₃ H₃
  filter_upwards [section9_ae_nonzero_fiber (percolation d p) f] with ω hω
  simpa only [f, section9RevealUnionEvent] using hω

/-- Almost-sure source union-fiber upper mean, uniformly over all target
subsets of the source cubes. Atom positivity is derived, not a hypothesis. -/
theorem section9_ae_union_fiber_mean_upper {d : ℕ} (hd : 2 ≤ d)
    (h : TwoPointAsymptotics d) :
    ∃ D : ℝ, 0 < D ∧ ∀ (i : Fin d) (n : ℕ), 0 < n →
      ∀ (H₁ H₃ : Finset (Vertex d)),
      H₁ ⊆ section9FiniteEndCube i n 0 → H₃ ⊆ section9FiniteEndCube i n (2*(n:ℝ)) →
      ∀ᵐ ω ∂percolation d (criticalPoint d),
      let F₁ := heartClusterUnion ω (section9FiniteEndCube i n 0) H₁
      let F₃ := heartClusterUnion ω (section9FiniteEndCube i n (2*(n:ℝ))) H₃
      ∀ (A B : Finset (Vertex d)),
      A ⊆ section9FiniteEndCube i n 0 → B ⊆ section9FiniteEndCube i n (2*(n:ℝ)) →
      section9PivotalMean
        (ProbabilityTheory.cond (percolation d (criticalPoint d)) (section9RevealUnionEvent
          (section9FiniteEndCube i n 0) H₁ (section9FiniteEndCube i n (2*(n:ℝ))) H₃ (F₁ ∪ F₃)))
        (orientedLatticePairs (section9FiniteMiddle i n))
        (section9FiniteTube i n (-(5:ℝ)/8) (3/8))
        (section9FiniteTube i n (-(3:ℝ)/8) (5/8))
        (section9FiniteEndCube i n 0) F₁ (section9FiniteEndCube i n (2*(n:ℝ))) F₃ A B ≤
        D*(n:ℝ)^((4:ℝ)-(d:ℝ))*(A.card:ℝ)*(B.card:ℝ) := by
  obtain ⟨D,hD,hbound⟩ := section9UnionConditionalMean_upper_scale hd h
  refine ⟨D,hD,?_⟩
  intro i n hn H₁ H₃ hH₁ hH₃
  filter_upwards [section9_ae_pair_reveal_nonzero (criticalPoint d)
    (section9FiniteEndCube i n 0) H₁ (section9FiniteEndCube i n (2*(n:ℝ))) H₃] with ω hω
  dsimp only
  intro A B hA hB
  exact hbound i n hn H₁ H₃ _ _ A B hH₁ hH₃ hA hB hω

end NearCritical
