module
public import NearCritical.Section8UniqueExtension
public import NearCritical.Section8ReflectionGeometry
public import NearCritical.AffineReflectionRegularity
public import NearCritical.AffineReflectionHeart
public import NearCritical.Section9PivotalSwap

/-! Actual unique extension from the negative face of the third source cube. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory
open scoped Classical

/-- The actual source unique-extension lower bound on the right. The regular
point lies on the exact negative predecessor-outside face; both energies use
the reflected actual small cube and full supplied boundary. The constants are
the same as those of the positive-face theorem, with delta fixed before r. -/
theorem section8_source_right_unique_extension {d : ℕ} (hd : 9 ≤ d)
    (asymptotics : TwoPointAsymptotics d) (rectangle : RestrictedRectangleLowerInput d) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ r : ℕ, 1 ≤ r → ∃ c : ℝ, 0 < c ∧
      ∀ (i : Fin d) (n : ℕ), 16*(r+1) ≤ n →
      ∀ (H₁ H₃ F₁ F₃ boundary : Finset (Vertex d)) (y z : Vertex d),
      H₁ ⊆ section9FiniteEndCube i n 0 → H₃ ⊆ section9FiniteEndCube i n (2*(n : ℝ)) →
      percolation d (criticalPoint d) (section9RevealEvent
        (section9FiniteEndCube i n 0) H₁ (section9FiniteEndCube i n (2*(n : ℝ))) H₃ F₁ F₃) ≠ 0 →
      y ∈ section8ExtensionNegativeFaceCore i n → z ∈ section8ExtensionMiddleCore i n →
      sourceRegularPoint F₃ ((section8ExtensionSmallCube i n).image
        (affineReflection (Pi.single i (2*(n : ℤ))))) boundary r δ y →
      let Q₁ := section9FiniteEndCube i n 0
      let Q₃ := section9FiniteEndCube i n (2*(n : ℝ))
      let T := section9FiniteTube i n (-(3 : ℝ)/8) (5/8)
      let ν := section9RevealedLaw (criticalPoint d) Q₁ H₁ Q₃ H₃ F₁ F₃
      c*(n : ℝ)^((2 : ℝ)-(d : ℝ)) ≤
        ν.real (section9AvoidanceEvent T T Q₃ F₃ {z} ((F₃ ∩ boundary) \ {y}) y) := by
  obtain ⟨δ,hδ,hleft⟩ := section8_source_unique_extension hd asymptotics rectangle
  refine ⟨δ,hδ,?_⟩
  intro r hr
  obtain ⟨K,hK,hbound⟩ := hleft r hr
  refine ⟨K,hK,?_⟩
  intro i n hn H₁ H₃ F₁ F₃ boundary y z hH₁ hH₃ hpos hy hz hreg Q₁ Q₃ T ν
  let c : Vertex d := Pi.single i (2*(n : ℤ))
  let f := affineReflection c
  let L := section9FiniteTube i n (-(5 : ℝ)/8) (3/8)
  let E := section9RevealEvent Q₁ H₁ Q₃ H₃ F₁ F₃
  let A := section9AvoidanceEvent T T Q₃ F₃ {z} ((F₃ ∩ boundary) \ {y}) y
  let νr := section9RevealedLaw (criticalPoint d) Q₁ (H₃.image f) Q₃ (H₁.image f)
    (F₃.image f) (F₁.image f)
  let Aleft := section9AvoidanceEvent L L Q₁ (F₃.image f) {f z}
    (((F₃.image f) ∩ (boundary.image f)) \ {f y}) (f y)
  have hinv (v : Vertex d) : f (f v) = v := by simp [f,affineReflection]
  have hdouble (S : Finset (Vertex d)) : (S.image f).image f = S := by
    have hcomp : f ∘ f = id := by
      funext v
      exact hinv v
    rw [Finset.image_image,hcomp,Finset.image_id]
  have hQ₁ : Q₁.image f = Q₃ := (section8_reflection_source_cubes i n).1
  have hQ₃ : Q₃.image f = Q₁ := (section8_reflection_source_cubes i n).2
  have hT : T.image f = L := (section8_reflection_source_tubes i n).2
  have hH₃r : H₃.image f ⊆ Q₁ := by
    rw [← hQ₃]
    exact Finset.image_subset_image hH₃
  have hH₁r : H₁.image f ⊆ Q₃ := by
    rw [← hQ₁]
    exact Finset.image_subset_image hH₁
  have hposr : percolation d (criticalPoint d)
      (section9RevealEvent Q₁ (H₃.image f) Q₃ (H₁.image f) (F₃.image f) (F₁.image f)) ≠ 0 := by
    have hpre : percolation d (criticalPoint d) (affineReflectConfiguration c ⁻¹' E) =
        percolation d (criticalPoint d) E := by
      rw [← Measure.map_apply (measurable_affineReflectConfiguration c)
        (measurableSet_section9RevealEvent Q₁ H₁ Q₃ H₃ F₁ F₃ hH₁ hH₃),
        percolation_map_affineReflection]
    have hp : percolation d (criticalPoint d) (affineReflectConfiguration c ⁻¹' E) ≠ 0 := by
      rwa [hpre]
    change percolation d (criticalPoint d)
      (affineReflectConfiguration c ⁻¹' section9RevealEvent Q₁ H₁ Q₃ H₃ F₁ F₃) ≠ 0 at hp
    rw [affineReflection_reveal_preimage,hQ₁,hQ₃,
      section9RevealEvent_swap Q₃ (H₁.image f) Q₁ (H₃.image f) (F₁.image f) (F₃.image f)] at hp
    exact hp
  have hyr : f y ∈ section8ExtensionPositiveFaceCore i n := by
    have himage : y ∈ (section8ExtensionPositiveFaceCore i n).image f := by
      rw [section8_reflection_positive_face_core i n]
      exact hy
    obtain ⟨v,hv,hvy⟩ := Finset.mem_image.mp himage
    simpa only [← hvy,hinv] using hv
  have hzr : f z ∈ section8ExtensionMiddleCore i n := by
    have hh : f z ∈ (section8ExtensionMiddleCore i n).image f := Finset.mem_image.mpr ⟨z,hz,rfl⟩
    rw [section8_reflection_middle_core i n] at hh
    exact hh
  have hregr : sourceRegularPoint (F₃.image f) (section8ExtensionSmallCube i n)
      (boundary.image f) r δ (f y) := by
    have hh := (sourceRegularPoint_affineReflection c F₃
      ((section8ExtensionSmallCube i n).image f) boundary r δ y).mpr hreg
    rw [hdouble] at hh
    exact hh
  have hlower := hbound i n hn (H₃.image f) (H₁.image f) (F₃.image f) (F₁.image f)
    (boundary.image f) (f y) (f z) hH₃r hH₁r hposr hyr hzr hregr
  change K*(n : ℝ)^((2 : ℝ)-(d : ℝ)) ≤ νr.real Aleft at hlower
  have hpreA : affineReflectConfiguration c ⁻¹' A = Aleft := by
    dsimp only [A]
    rw [affineReflection_avoidance_preimage]
    change section9AvoidanceEvent (T.image f) (T.image f) (Q₃.image f) (F₃.image f)
      (({z} : Finset (Vertex d)).image f) (((F₃ ∩ boundary) \ {y}).image f) (f y) = Aleft
    simp only [hT,hQ₃,Finset.image_sdiff (F₃ ∩ boundary) {y} f.injective,
      Finset.image_inter F₃ boundary f.injective,Finset.image_singleton,Aleft]
  have hA : MeasurableSet A :=
    (measurableSet_sprinklingUnexploredCluster_hits T Q₃ F₃ {z} y).inter
      (measurableSet_sprinklingUnexploredCluster_hits T Q₃ F₃ ((F₃ ∩ boundary) \ {y}) y).compl
  have hp := congrArg ENNReal.toReal (affineReflection_revealed_probability (criticalPoint d) c
    Q₁ H₁ Q₃ H₃ F₁ F₃ hH₁ hH₃ A hA)
  change (section9RevealedLaw (criticalPoint d) (Q₁.image f) (H₁.image f)
    (Q₃.image f) (H₃.image f) (F₁.image f) (F₃.image f)).real
      (affineReflectConfiguration c ⁻¹' A) = ν.real A at hp
  rw [hQ₁,hQ₃,hpreA,section9RevealedLaw_swap (criticalPoint d)
    Q₃ (H₁.image f) Q₁ (H₃.image f) (F₁.image f) (F₃.image f)] at hp
  exact hlower.trans_eq hp

end NearCritical
