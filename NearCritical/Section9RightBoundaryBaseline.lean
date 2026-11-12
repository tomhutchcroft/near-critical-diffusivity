module
public import NearCritical.Section8RightUniqueExtension
public import NearCritical.Section9UniqueTargetDisjoint

/-! Actual source baseline for the avoidance lower bound. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory
open scoped Classical BigOperators

/-- Summing actual unique-boundary events gives the source connection baseline.
No connection-probability estimate is supplied as a premise. -/
theorem section9_right_regular_boundary_baseline {d : ℕ} (hd : 9 ≤ d)
    (asymptotics : TwoPointAsymptotics d) (rectangle : RestrictedRectangleLowerInput d) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ r : ℕ, 1 ≤ r → ∃ c : ℝ, 0 < c ∧
      ∀ (i : Fin d) (n : ℕ), 16*(r+1) ≤ n →
      ∀ (H₁ H₃ F₁ F₃ boundary B : Finset (Vertex d)) (z : Vertex d),
      H₁ ⊆ section9FiniteEndCube i n 0 → H₃ ⊆ section9FiniteEndCube i n (2*(n : ℝ)) →
      percolation d (criticalPoint d) (section9RevealEvent
        (section9FiniteEndCube i n 0) H₁ (section9FiniteEndCube i n (2*(n : ℝ))) H₃ F₁ F₃) ≠ 0 →
      z ∈ section8ExtensionMiddleCore i n →
      (∀ y ∈ B, y ∈ section8ExtensionNegativeFaceCore i n) →
      (∀ y ∈ B, sourceRegularPoint F₃ ((section8ExtensionSmallCube i n).image
        (affineReflection (Pi.single i (2*(n : ℤ))))) boundary r δ y) →
      let Q₁ := section9FiniteEndCube i n 0
      let Q₃ := section9FiniteEndCube i n (2*(n : ℝ))
      let T := section9FiniteTube i n (-(3 : ℝ)/8) (5/8)
      let ν := section9RevealedLaw (criticalPoint d) Q₁ H₁ Q₃ H₃ F₁ F₃
      c*(n : ℝ)^((2 : ℝ)-(d : ℝ))*(B.card : ℝ) ≤
        ν.real {ω | (sprinklingUnexploredCluster ω T Q₃ F₃ z ∩ B).Nonempty} := by
  obtain ⟨δ,hδ,hright⟩ := section8_source_right_unique_extension hd asymptotics rectangle
  refine ⟨δ,hδ,?_⟩
  intro r hr
  obtain ⟨c,hc,hbound⟩ := hright r hr
  refine ⟨c,hc,?_⟩
  intro i n hn H₁ H₃ F₁ F₃ boundary B z hH₁ hH₃ hpos hz hface hregular Q₁ Q₃ T ν
  let f := affineReflection (Pi.single i (2*(n : ℤ)))
  have hinv (v : Vertex d) : f (f v) = v := by simp [f,affineReflection]
  have hzr : f z ∈ section8ExtensionMiddleCore i n := by
    rw [← section8_reflection_middle_core i n]
    exact Finset.mem_image.mpr ⟨z,hz,rfl⟩
  have hBT : B ⊆ T := by
    intro y hy
    have himage : y ∈ (section8ExtensionPositiveFaceCore i n).image f := by
      rw [section8_reflection_positive_face_core i n]
      exact hface y hy
    obtain ⟨x,hx,hxy⟩ := Finset.mem_image.mp himage
    obtain ⟨_,hsegment,_⟩ := section8_extension_source_geometry i n r hn hx hzr
    have hxI : x ∈ section8OutwardSegment x i r :=
      (section8_mem_outward_segment x x i r).mpr ⟨0,Nat.zero_le _,by simp⟩
    have hxt := hsegment hxI
    change y ∈ section9FiniteTube i n (-(3 : ℝ)/8) (5/8)
    rw [← (section8_reflection_source_tubes i n).1]
    exact Finset.mem_image.mpr ⟨x,hxt,hxy⟩
  have hBW : B ⊆ F₃ ∩ boundary := fun y hy => (hregular y hy).1
  letI : IsProbabilityMeasure ν := section9RevealedLaw_isProbability
    (criticalPoint d) Q₁ H₁ Q₃ H₃ F₁ F₃ hpos
  have hsum := section9_unique_target_probability_sum_le ν T Q₃ F₃
    (F₃ ∩ boundary) B z hBT hBW
  calc
    _ = ∑ y ∈ B, c*(n : ℝ)^((2 : ℝ)-(d : ℝ)) := by
      simp only [Finset.sum_const,nsmul_eq_mul]; ring
    _ ≤ ∑ y ∈ B, ν.real
        (section9AvoidanceEvent T T Q₃ F₃ {z} ((F₃ ∩ boundary) \ {y}) y) := by
      apply Finset.sum_le_sum
      intro y hy
      exact hbound i n hn H₁ H₃ F₁ F₃ boundary y z hH₁ hH₃ hpos (hface y hy) hz (hregular y hy)
    _ ≤ _ := hsum

end NearCritical
