module
public import NearCritical.Section9SourceOpenedTargets
public import NearCritical.Section9OpenedTargetLabelTransport
public import NearCritical.Section9OpenedTargetMonotonicity
public import NearCritical.Section9NearCriticalSprinkleParameter

@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory
open scoped Classical

/-- The source opened-target bound at the exact near-critical parameter in the
uniform-label coupling conditioned on the critical reveal. -/
theorem section9_source_many_opened_pivotal_targets_uniform_labels {d : ℕ} (hd : 9 ≤ d)
    (asymptotics : TwoPointAsymptotics d) (rectangle : RestrictedRectangleLowerInput d)
    (reimer : FiniteBernoulliBKRInput) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ r : ℕ, 1 ≤ r → ∀ ε : ℝ, 0 < ε →
      ∃ cSize : ℝ, 0 < cSize ∧ ∀ m : ℕ, ∃ Lambda : ℝ, 0 < Lambda ∧
      ∀ CB KA : ℝ, 0 < CB → 0 < KA →
      ∃ N : ℕ, 16*(r+1) ≤ N ∧ ∀ (i : Fin d) (n : ℕ), N ≤ n →
      ∃ p : unitInterval, (p : ℝ) = (criticalPoint d : ℝ) + Lambda/(n : ℝ)^2 ∧
      ∀ {ι : Type*} (I : Finset ι) (targets : ι → Finset (Vertex d))
        (H₁ H₃ F₁ F₃ boundary₁ boundary₃ A : Finset (Vertex d)),
      let B := I.biUnion targets
      H₁ ⊆ section9FiniteEndCube i n 0 → H₃ ⊆ section9FiniteEndCube i n (2*(n : ℝ)) →
      percolation d (criticalPoint d) (section9RevealEvent
        (section9FiniteEndCube i n 0) H₁ (section9FiniteEndCube i n (2*(n : ℝ))) H₃ F₁ F₃) ≠ 0 →
      (∀ x ∈ A, x ∈ section8ExtensionPositiveFaceCore i n) →
      (∀ x ∈ A, sourceRegularPoint F₁ (section8ExtensionSmallCube i n) boundary₁ r δ x) →
      (∀ y ∈ B, y ∈ section8ExtensionNegativeFaceCore i n) →
      (∀ y ∈ B, sourceRegularPoint F₃ ((section8ExtensionSmallCube i n).image
        (affineReflection (Pi.single i (2*(n : ℤ))))) boundary₃ r δ y) →
      Set.PairwiseDisjoint (I : Set ι) targets →
      (A.card : ℝ) ≤ KA*(n : ℝ)^2 →
      (∀ j ∈ I, ((targets j).card : ℝ) ≤ CB*(n : ℝ)^2) →
      cSize*(n : ℝ)^2 ≤ (A.card : ℝ) → cSize*(n : ℝ)^2 ≤ (B.card : ℝ) →
      cSize*(n : ℝ)^((d : ℝ)-2) ≤ (A.card : ℝ)*(B.card : ℝ) →
      let L := section9FiniteTube i n (-(5 : ℝ)/8) (3/8)
      let R := section9FiniteTube i n (-(3 : ℝ)/8) (5/8)
      let Q₁ := section9FiniteEndCube i n 0
      let Q₃ := section9FiniteEndCube i n (2*(n : ℝ))
      let E := orientedLatticePairs (section9FiniteMiddle i n)
      let labels := Measure.infinitePi fun _ : Bond d => (volume : Measure unitInterval)
      1-ε ≤ (ProbabilityTheory.cond labels ((labelConfiguration (criticalPoint d)) ⁻¹'
        section9RevealEvent Q₁ H₁ Q₃ H₃ F₁ F₃)).real
        {u | (m : ℝ) < ((I.filter fun j =>
          (sprinkledPivotalPairs (labelConfiguration (criticalPoint d) u) (labelConfiguration p u)
            E L R Q₁ F₁ Q₃ F₃ A (targets j)).Nonempty).card : ℝ)} := by
  obtain ⟨δ,hδ,hmain⟩ := section9_source_many_opened_pivotal_targets hd asymptotics rectangle reimer
  refine ⟨δ,hδ,?_⟩
  intro r hr ε hε
  obtain ⟨cSize,hSize,hmain⟩ := hmain r hr ε hε
  refine ⟨cSize,hSize,?_⟩
  intro m
  obtain ⟨Lambda,hLambda,hmain⟩ := hmain m
  refine ⟨Lambda,hLambda,?_⟩
  intro CB KA hCB hKA
  obtain ⟨N,hN,hmain⟩ := hmain CB KA hCB hKA
  obtain ⟨N',_,hparam⟩ := section9_critical_eventual_sprinkle_parameter hd
    ⟨0, by omega⟩ asymptotics Lambda hLambda
  refine ⟨max N N',hN.trans (le_max_left _ _),?_⟩
  intro i n hn
  obtain ⟨q,hp,hq⟩ := hparam n ((le_max_right _ _).trans hn)
  refine ⟨orParameter (criticalPoint d) q,hp,?_⟩
  intro ι I targets H₁ H₃ F₁ F₃ boundary₁ boundary₃ A B hH₁ hH₃ hpos
    hA hAreg hB hBreg hdis hAc hBc hAsize hBsize hAB L R Q₁ Q₃ E labels
  have h := hmain i n ((le_max_left _ _).trans hn) q hq
    I targets H₁ H₃ F₁ F₃ boundary₁ boundary₃ A
    hH₁ hH₃ hpos hA hAreg hB hBreg hdis hAc hBc hAsize hBsize hAB
  exact h.trans_eq (section9_opened_target_label_probability_eq
    (criticalPoint d) q Q₁ H₁ Q₃ H₃ F₁ F₃ hH₁ hH₃ I targets E L R A m)

/-- The same bound holds at every admissible larger enriched parameter. -/
theorem section9_source_many_opened_pivotal_targets_uniform_labels_of_le {d : ℕ} (hd : 9 ≤ d)
    (asymptotics : TwoPointAsymptotics d) (rectangle : RestrictedRectangleLowerInput d)
    (reimer : FiniteBernoulliBKRInput) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ r : ℕ, 1 ≤ r → ∀ ε : ℝ, 0 < ε →
      ∃ cSize : ℝ, 0 < cSize ∧ ∀ m : ℕ, ∃ Lambda : ℝ, 0 < Lambda ∧
      ∀ CB KA : ℝ, 0 < CB → 0 < KA →
      ∃ N : ℕ, 16*(r+1) ≤ N ∧ ∀ (i : Fin d) (n : ℕ), N ≤ n →
      ∀ p : unitInterval, (criticalPoint d : ℝ) + Lambda/(n : ℝ)^2 ≤ (p : ℝ) →
      ∀ {ι : Type*} (I : Finset ι) (targets : ι → Finset (Vertex d))
        (H₁ H₃ F₁ F₃ boundary₁ boundary₃ A : Finset (Vertex d)),
      let B := I.biUnion targets
      H₁ ⊆ section9FiniteEndCube i n 0 → H₃ ⊆ section9FiniteEndCube i n (2*(n : ℝ)) →
      percolation d (criticalPoint d) (section9RevealEvent
        (section9FiniteEndCube i n 0) H₁ (section9FiniteEndCube i n (2*(n : ℝ))) H₃ F₁ F₃) ≠ 0 →
      (∀ x ∈ A, x ∈ section8ExtensionPositiveFaceCore i n) →
      (∀ x ∈ A, sourceRegularPoint F₁ (section8ExtensionSmallCube i n) boundary₁ r δ x) →
      (∀ y ∈ B, y ∈ section8ExtensionNegativeFaceCore i n) →
      (∀ y ∈ B, sourceRegularPoint F₃ ((section8ExtensionSmallCube i n).image
        (affineReflection (Pi.single i (2*(n : ℤ))))) boundary₃ r δ y) →
      Set.PairwiseDisjoint (I : Set ι) targets →
      (A.card : ℝ) ≤ KA*(n : ℝ)^2 →
      (∀ j ∈ I, ((targets j).card : ℝ) ≤ CB*(n : ℝ)^2) →
      cSize*(n : ℝ)^2 ≤ (A.card : ℝ) → cSize*(n : ℝ)^2 ≤ (B.card : ℝ) →
      cSize*(n : ℝ)^((d : ℝ)-2) ≤ (A.card : ℝ)*(B.card : ℝ) →
      let L := section9FiniteTube i n (-(5 : ℝ)/8) (3/8)
      let R := section9FiniteTube i n (-(3 : ℝ)/8) (5/8)
      let Q₁ := section9FiniteEndCube i n 0
      let Q₃ := section9FiniteEndCube i n (2*(n : ℝ))
      let E := orientedLatticePairs (section9FiniteMiddle i n)
      let labels := Measure.infinitePi fun _ : Bond d => (volume : Measure unitInterval)
      1-ε ≤ (ProbabilityTheory.cond labels ((labelConfiguration (criticalPoint d)) ⁻¹'
        section9RevealEvent Q₁ H₁ Q₃ H₃ F₁ F₃)).real
        {u | (m : ℝ) < ((I.filter fun j =>
          (sprinkledPivotalPairs (labelConfiguration (criticalPoint d) u) (labelConfiguration p u)
            E L R Q₁ F₁ Q₃ F₃ A (targets j)).Nonempty).card : ℝ)} := by
  obtain ⟨δ,hδ,hmain⟩ :=
    section9_source_many_opened_pivotal_targets_uniform_labels hd asymptotics rectangle reimer
  refine ⟨δ,hδ,?_⟩
  intro r hr ε hε
  obtain ⟨cSize,hSize,hmain⟩ := hmain r hr ε hε
  refine ⟨cSize,hSize,?_⟩
  intro m
  obtain ⟨Lambda,hLambda,hmain⟩ := hmain m
  refine ⟨Lambda,hLambda,?_⟩
  intro CB KA hCB hKA
  obtain ⟨N,hN,hmain⟩ := hmain CB KA hCB hKA
  refine ⟨N,hN,?_⟩
  intro i n hn p hp
  obtain ⟨p₀,hp₀,hmain⟩ := hmain i n hn
  have hp₀p : p₀ ≤ p := by
    change (p₀ : ℝ) ≤ (p : ℝ)
    rw [hp₀]
    exact hp
  intro ι I targets H₁ H₃ F₁ F₃ boundary₁ boundary₃ A B hH₁ hH₃ hpos
    hA hAreg hB hBreg hdis hAc hBc hAsize hBsize hAB L R Q₁ Q₃ E labels
  have h := hmain I targets H₁ H₃ F₁ F₃ boundary₁ boundary₃ A
    hH₁ hH₃ hpos hA hAreg hB hBreg hdis hAc hBc hAsize hBsize hAB
  let reveal := section9RevealEvent Q₁ H₁ Q₃ H₃ F₁ F₃
  have hrev : MeasurableSet reveal :=
    measurableSet_section9RevealEvent Q₁ H₁ Q₃ H₃ F₁ F₃ hH₁ hH₃
  have hmass : labels ((labelConfiguration (criticalPoint d)) ⁻¹' reveal) ≠ 0 := by
    rw [← Measure.map_apply (measurable_labelConfiguration (criticalPoint d)) hrev]
    change (Measure.map (labelConfiguration (criticalPoint d))
      (Measure.infinitePi fun _ : Bond d => (volume : Measure unitInterval))) reveal ≠ 0
    rw [map_labelConfiguration]
    exact hpos
  letI : IsProbabilityMeasure (ProbabilityTheory.cond labels
      ((labelConfiguration (criticalPoint d)) ⁻¹' reveal)) :=
    ProbabilityTheory.cond_isProbabilityMeasure hmass
  refine h.trans (measureReal_mono ?_ (measure_ne_top _ _))
  intro u hu
  have hcount := section9_opened_target_count_mono
    (labelConfiguration (criticalPoint d) u) (labelConfiguration_mono hp₀p u)
    I targets E L R Q₁ F₁ Q₃ F₃ A
  exact lt_of_lt_of_le (α := ℝ) hu (Nat.cast_le.mpr hcount)

end NearCritical
