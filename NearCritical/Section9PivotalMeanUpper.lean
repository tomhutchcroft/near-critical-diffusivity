module

public import NearCritical.Section9ConditionalPivots
public import NearCritical.Section9PivotalBK

/-! Section 9 conditional mean upper bound reduced to actual two-point sums.
Spatial summation and uniform source constants are not asserted here. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory Set
open scoped Classical BigOperators

/-- Ordinary finite-target connections are bounded by unrestricted two-point
probabilities. Domain restrictions are removed only in the upper-bound direction. -/
theorem connectionToSet_probability_le_twoPoint_sum {d : ℕ} (p : unitInterval)
    (S : Set (Vertex d)) (x : Vertex d) (A : Finset (Vertex d)) :
    (percolation d p).real (connectionToSetEvent S x (A : Set (Vertex d))) ≤
      ∑ y ∈ A, twoPoint d p x y := by
  have hsub : connectionToSetEvent S x (A : Set (Vertex d)) ⊆
      ⋃ y ∈ A, connectionEvent x y := by
    rintro ω ⟨_, y, hyA, _, hr⟩
    have hgraph : restrictedGraph ω S ≤ openGraph ω := by
      intro u v huv
      exact huv.1
    have hopen : (openGraph ω).Reachable x y := hr.mono hgraph
    exact Set.mem_iUnion.mpr ⟨y, Set.mem_iUnion.mpr ⟨hyA, hopen⟩⟩
  exact (measureReal_mono (μ := percolation d p) hsub (measure_ne_top _ _)).trans
    (measureReal_biUnion_finset_le A (connectionEvent x))

/-- Actual Bernoulli fixed-deletion mean, bounded by the double arm sum over
both orientations of the supplied candidate set. -/
theorem section9PivotalMean_le_twoPoint_sums {d : ℕ} (p : unitInterval)
    (E : Finset (Vertex d × Vertex d)) (L R Q₁ F₁ Q₃ F₃ A B : Finset (Vertex d)) :
    section9PivotalMean (percolation d p) E L R Q₁ F₁ Q₃ F₃ A B ≤
      ∑ e ∈ E, (∑ x ∈ A, twoPoint d p e.1 x) * (∑ y ∈ B, twoPoint d p e.2 y) := by
  unfold section9PivotalMean
  rw [integral_section9PivotalCount]
  apply Finset.sum_le_sum
  intro e _
  apply (sprinklingPivotalPair_probability_le p L R Q₁ F₁ Q₃ F₃ A B e).trans
  exact mul_le_mul
    (connectionToSet_probability_le_twoPoint_sum p (L : Set (Vertex d)) e.1 A)
    (connectionToSet_probability_le_twoPoint_sum p (R : Set (Vertex d)) e.2 B)
    ENNReal.toReal_nonneg (Finset.sum_nonneg (fun _ _ => ENNReal.toReal_nonneg))

/-- Literal revealed-law mean upper bound by unrestricted two-point sums.
The source's n-dependent numerical estimate remains a geometric summation. -/
theorem section9ConditionalPivotalMean_le_twoPoint_sums {d : ℕ} (p : unitInterval)
    (E : Finset (Vertex d × Vertex d)) (L R Q₁ H₁ F₁ Q₃ H₃ F₃ A B : Finset (Vertex d))
    (hH₁ : H₁ ⊆ Q₁) (hH₃ : H₃ ⊆ Q₃)
    (hLQ₃ : Disjoint L Q₃) (hRQ₁ : Disjoint R Q₁)
    (hpos : percolation d p (section9RevealEvent Q₁ H₁ Q₃ H₃ F₁ F₃) ≠ 0) :
    section9PivotalMean (section9RevealedLaw p Q₁ H₁ Q₃ H₃ F₁ F₃)
      E L R Q₁ F₁ Q₃ F₃ A B ≤
        ∑ e ∈ E, (∑ x ∈ A, twoPoint d p e.1 x) * (∑ y ∈ B, twoPoint d p e.2 y) := by
  rw [section9RevealedLaw_pivotalMean p E L R Q₁ H₁ F₁ Q₃ H₃ F₃ A B
    hH₁ hH₃ hLQ₃ hRQ₁ hpos]
  exact section9PivotalMean_le_twoPoint_sums p E L R Q₁ F₁ Q₃ F₃ A B

end NearCritical
