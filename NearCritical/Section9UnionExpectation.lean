module

public import NearCritical.Section9RevealedExpectation

/-! Conditional expectation given the literal source F13 union observation.
Fixed target sets and disjoint reveal cubes are explicit. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory ProbabilityTheory
open scoped Classical

lemma measurable_section9UnionObservation {d : ℕ} (Q₁ H₁ Q₃ H₃ : Finset (Vertex d))
    (hH₁ : H₁ ⊆ Q₁) (hH₃ : H₃ ⊆ Q₃) :
    Measurable (fun ω : Configuration d =>
      heartClusterUnion ω Q₁ H₁ ∪ heartClusterUnion ω Q₃ H₃) :=
  (measurable_section9HeartObservation Q₁ H₁ hH₁).union_finset
    (measurable_section9HeartObservation Q₃ H₃ hH₃)

/-- The actual adaptive pivot count conditioned on the literal F13 observation
has the actual frozen-F mean. Realized atom positivity is derived a.s. -/
theorem section9_condExp_union_adaptive_eq_revealed_mean {d : ℕ} (p : unitInterval)
    (E : Finset (Vertex d × Vertex d)) (L R Q₁ H₁ Q₃ H₃ A B : Finset (Vertex d))
    (hH₁ : H₁ ⊆ Q₁) (hH₃ : H₃ ⊆ Q₃) (hdis : Disjoint Q₁ Q₃) :
    (percolation d p)[section9AdaptivePivotalCount E L R Q₁ H₁ Q₃ H₃ A B |
      (inferInstance : MeasurableSpace (Finset (Vertex d))).comap
        (fun ω => heartClusterUnion ω Q₁ H₁ ∪ heartClusterUnion ω Q₃ H₃)] =ᵐ[percolation d p]
      fun ω => section9PivotalMean
        (section9RevealedLaw p Q₁ H₁ Q₃ H₃
          (heartClusterUnion ω Q₁ H₁) (heartClusterUnion ω Q₃ H₃))
        E L R Q₁ (heartClusterUnion ω Q₁ H₁) Q₃ (heartClusterUnion ω Q₃ H₃) A B := by
  have h := section9_condExp_eq_fiber_integral (percolation d p)
    (fun ω => heartClusterUnion ω Q₁ H₁ ∪ heartClusterUnion ω Q₃ H₃)
    (measurable_section9UnionObservation Q₁ H₁ Q₃ H₃ hH₁ hH₃)
    (section9AdaptivePivotalCount E L R Q₁ H₁ Q₃ H₃ A B)
    (integrable_section9AdaptivePivotalCount (percolation d p) E L R Q₁ H₁ Q₃ H₃ A B hH₁ hH₃)
  filter_upwards [h, section9_ae_pair_reveal_nonzero p Q₁ H₁ Q₃ H₃] with ω hω hpos
  rw [hω]
  have hfiber : {z : Configuration d |
      heartClusterUnion z Q₁ H₁ ∪ heartClusterUnion z Q₃ H₃ =
        heartClusterUnion ω Q₁ H₁ ∪ heartClusterUnion ω Q₃ H₃} =
      section9RevealUnionEvent Q₁ H₁ Q₃ H₃
        (heartClusterUnion ω Q₁ H₁ ∪ heartClusterUnion ω Q₃ H₃) := rfl
  rw [hfiber, ← section9RevealedLaw_eq_union_condition p Q₁ H₁ Q₃ H₃
    (heartClusterUnion ω Q₁ H₁) (heartClusterUnion ω Q₃ H₃) hpos hdis]
  exact integral_section9AdaptivePivotalCount_revealed p E L R Q₁ H₁
    (heartClusterUnion ω Q₁ H₁) Q₃ H₃ (heartClusterUnion ω Q₃ H₃) A B hH₁ hH₃

end NearCritical
