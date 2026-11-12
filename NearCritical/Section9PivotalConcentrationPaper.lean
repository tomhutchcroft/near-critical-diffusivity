module
public import NearCritical.Section9PivotalMeanPaper
public import NearCritical.Section9SourcePivotalConcentration

/-! The literal critical source sprinkling proposition: actual mean scale
and concentration together, before the independent opening step. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory

private theorem concentration_paper_regular_mono {d : ℕ}
    (F S boundary : Finset (Vertex d)) (r : ℕ) (δ δ' : ℝ) (x : Vertex d)
    (hle : δ ≤ δ') (h : sourceRegularPoint F S boundary r δ x) :
    sourceRegularPoint F S boundary r δ' x :=
  ⟨h.1,h.2.1.trans hle,h.2.2.trans hle⟩

/-- Literal critical prop.sprinkling.AB under the actual outer-heart law.
One common regularity tolerance supplies both the actual mean sandwich and
the actual relative interval probability. -/
theorem section9_source_pivotal_concentration_paper_bound {d : ℕ} (hd : 9 ≤ d)
    (asymptotics : TwoPointAsymptotics d) (rectangle : RestrictedRectangleLowerInput d)
    (reimer : FiniteBernoulliBKRInput) :
    ∃ C : ℝ, 0 < C ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ r : ℕ, 1 ≤ r →
      ∃ cMean : ℝ, 0 < cMean ∧ ∀ ε : ℝ, 0 < ε →
      ∃ cSize : ℝ, 0 < cSize ∧ ∃ N : ℕ, 16*(r+1) ≤ N ∧
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
      cSize*(n : ℝ)^2 ≤ (A.card : ℝ) → cSize*(n : ℝ)^2 ≤ (B.card : ℝ) →
      cSize*(n : ℝ)^((d : ℝ)-2) ≤ (A.card : ℝ)*(B.card : ℝ) →
      let L := section9FiniteTube i n (-(5 : ℝ)/8) (3/8)
      let R := section9FiniteTube i n (-(3 : ℝ)/8) (5/8)
      let Q₁ := section9FiniteEndCube i n 0
      let Q₃ := section9FiniteEndCube i n (2*(n : ℝ))
      let ν := section9RevealedLaw (criticalPoint d) Q₁ H₁ Q₃ H₃ F₁ F₃
      let E := orientedLatticePairs (section9FiniteMiddle i n)
      let M := section9PivotalMean ν E L R Q₁ F₁ Q₃ F₃ A B
      cMean*(n : ℝ)^((4 : ℝ)-(d : ℝ))*(A.card : ℝ)*(B.card : ℝ) ≤ M ∧
      M ≤ C*(n : ℝ)^((4 : ℝ)-(d : ℝ))*(A.card : ℝ)*(B.card : ℝ) ∧
      1-ε ≤ ν.real {ω | M/2 ≤ section9PivotalCount E L R Q₁ F₁ Q₃ F₃ A B ω ∧
        section9PivotalCount E L R Q₁ F₁ Q₃ F₃ A B ω ≤ 3*M/2} := by
  obtain ⟨C,hC,δM,hδM,hmean⟩ := section9_source_pivotal_mean_paper_bound hd asymptotics rectangle reimer
  obtain ⟨δP,hδP,hprob⟩ := section9_source_pivotal_concentration hd asymptotics rectangle reimer
  let δ := min δM δP
  refine ⟨C,hC,δ,lt_min hδM hδP,?_⟩
  intro r hr
  obtain ⟨c,hc,NM,hNM,hmeanr⟩ := hmean r hr
  refine ⟨c,hc,?_⟩
  intro ε hε
  obtain ⟨cSize,hcSize,NP,hNP,hprobr⟩ := hprob r hr ε hε
  let N := max NM NP
  refine ⟨cSize,hcSize,N,hNM.trans (le_max_left _ _),?_⟩
  intro i n hn H₁ H₃ F₁ F₃ boundary₁ boundary₃ A B hH₁ hH₃ hpos hA hAreg hB hBreg hAc hBc hAB
    L R Q₁ Q₃ ν E M
  have hAM (x : Vertex d) (hx : x ∈ A) :
      sourceRegularPoint F₁ (section8ExtensionSmallCube i n) boundary₁ r δM x :=
    concentration_paper_regular_mono _ _ _ r δ δM x (min_le_left _ _) (hAreg x hx)
  have hBM (y : Vertex d) (hy : y ∈ B) : sourceRegularPoint F₃
      ((section8ExtensionSmallCube i n).image (affineReflection (Pi.single i (2*(n : ℤ)))))
      boundary₃ r δM y :=
    concentration_paper_regular_mono _ _ _ r δ δM y (min_le_left _ _) (hBreg y hy)
  have hAP (x : Vertex d) (hx : x ∈ A) :
      sourceRegularPoint F₁ (section8ExtensionSmallCube i n) boundary₁ r δP x :=
    concentration_paper_regular_mono _ _ _ r δ δP x (min_le_right _ _) (hAreg x hx)
  have hBP (y : Vertex d) (hy : y ∈ B) : sourceRegularPoint F₃
      ((section8ExtensionSmallCube i n).image (affineReflection (Pi.single i (2*(n : ℤ)))))
      boundary₃ r δP y :=
    concentration_paper_regular_mono _ _ _ r δ δP y (min_le_right _ _) (hBreg y hy)
  have hm := hmeanr i n ((le_max_left NM NP).trans hn) H₁ H₃ F₁ F₃ boundary₁ boundary₃ A B
    hH₁ hH₃ hpos hA hAM hB hBM
  have hp := hprobr i n ((le_max_right NM NP).trans hn) H₁ H₃ F₁ F₃ boundary₁ boundary₃ A B
    hH₁ hH₃ hpos hA hAP hB hBP hAc hBc hAB
  exact ⟨hm.1,hm.2,hp⟩

end NearCritical
