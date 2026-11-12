module
public import NearCritical.Section9PivotalMeanLower
public import NearCritical.Section9MeanUpperScale

/-! The literal two-sided source pivotal mean under the actual heart law. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory

/-- Source prop.mean.pivAB for the actual canonical count. The upper constant
is uniform before r, while the lower constant and threshold follow the fixed
regularity radius. All domain guards are derived from the actual source faces. -/
theorem section9_source_pivotal_mean_paper_bound {d : ℕ} (hd : 9 ≤ d)
    (asymptotics : TwoPointAsymptotics d) (rectangle : RestrictedRectangleLowerInput d)
    (reimer : FiniteBernoulliBKRInput) :
    ∃ C : ℝ, 0 < C ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ r : ℕ, 1 ≤ r →
      ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, 16*(r+1) ≤ N ∧
      ∀ (i : Fin d) (n : ℕ), N ≤ n →
      ∀ (H₁ H₃ F₁ F₃ boundary₁ boundary₃ A B : Finset (Vertex d)),
      H₁ ⊆ section9FiniteEndCube i n 0 → H₃ ⊆ section9FiniteEndCube i n (2*(n : ℝ)) →
      percolation d (criticalPoint d) (section9RevealEvent
        (section9FiniteEndCube i n 0) H₁ (section9FiniteEndCube i n (2*(n : ℝ))) H₃ F₁ F₃) ≠ 0 →
      (∀ x ∈ A, x ∈ section8ExtensionPositiveFaceCore i n) →
      (∀ x ∈ A, sourceRegularPoint F₁ (section8ExtensionSmallCube i n) boundary₁ r δ x) →
      (∀ y ∈ B, y ∈ section8ExtensionNegativeFaceCore i n) →
      (∀ y ∈ B, sourceRegularPoint F₃ ((section8ExtensionSmallCube i n).image
        (affineReflection (Pi.single i (2*(n : ℤ))))) boundary₃ r δ y) →
      let L := section9FiniteTube i n (-(5 : ℝ)/8) (3/8)
      let R := section9FiniteTube i n (-(3 : ℝ)/8) (5/8)
      let Q₁ := section9FiniteEndCube i n 0
      let Q₃ := section9FiniteEndCube i n (2*(n : ℝ))
      let ν := section9RevealedLaw (criticalPoint d) Q₁ H₁ Q₃ H₃ F₁ F₃
      let m := section9PivotalMean ν (orientedLatticePairs (section9FiniteMiddle i n))
        L R Q₁ F₁ Q₃ F₃ A B
      c*(n : ℝ)^((4 : ℝ)-(d : ℝ))*(A.card : ℝ)*(B.card : ℝ) ≤ m ∧
      m ≤ C*(n : ℝ)^((4 : ℝ)-(d : ℝ))*(A.card : ℝ)*(B.card : ℝ) := by
  obtain ⟨C,hC,hupper⟩ := section9ConditionalMean_upper_scale (by omega : 2 ≤ d) asymptotics
  obtain ⟨δ,hδ,hlower⟩ := section9_source_pivotal_mean_lower hd asymptotics rectangle reimer
  refine ⟨C,hC,δ,hδ,?_⟩
  intro r hr
  obtain ⟨c,hc,N,hN,hbound⟩ := hlower r hr
  refine ⟨c,hc,N,hN,?_⟩
  intro i n hn H₁ H₃ F₁ F₃ boundary₁ boundary₃ A B hH₁ hH₃ hpos hA hAreg hB hBreg
    L R Q₁ Q₃ ν m
  constructor
  · exact hbound i n hn H₁ H₃ F₁ F₃ boundary₁ boundary₃ A B
      hH₁ hH₃ hpos hA hAreg hB hBreg
  · exact hupper i n (by omega : 0 < n) H₁ H₃ F₁ F₃ A B hH₁ hH₃
      (fun x hx => (Finset.mem_filter.mp (hA x hx)).1)
      (fun y hy => (Finset.mem_filter.mp (hB y hy)).1) hpos

end NearCritical
