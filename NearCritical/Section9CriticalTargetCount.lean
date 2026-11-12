module
public import NearCritical.Section9PivotalConcentrationPaper
public import NearCritical.Section9TargetFamilySecondMoment
public import NearCritical.Section9TargetPivotUnion

/-! Actual critical target count from the source mean, interval and moments. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory
open scoped Classical BigOperators

/-- Many target families have an actual canonical critical pivotal pair.
The regularity threshold is fixed before r, and cSize/c0 before CB/KA.
No moment, probability or favorable target-count estimate is assumed. -/
theorem section9_source_many_critical_pivotal_targets {d : ℕ} (hd : 9 ≤ d)
    (asymptotics : TwoPointAsymptotics d) (rectangle : RestrictedRectangleLowerInput d)
    (reimer : FiniteBernoulliBKRInput) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ r : ℕ, 1 ≤ r → ∀ ε : ℝ, 0 < ε →
      ∃ cSize : ℝ, 0 < cSize ∧ ∃ c0 : ℝ, 0 < c0 ∧
      ∀ CB KA : ℝ, 0 < CB → 0 < KA →
      ∃ N : ℕ, 16*(r+1) ≤ N ∧ ∀ (i : Fin d) (n : ℕ), N ≤ n →
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
      let ν := section9RevealedLaw (criticalPoint d) Q₁ H₁ Q₃ H₃ F₁ F₃
      let E := orientedLatticePairs (section9FiniteMiddle i n)
      1-ε ≤ ν.real {ω | c0*(n : ℝ)^((4 : ℝ)-(d : ℝ))*(A.card : ℝ)*(B.card : ℝ) ≤
        ((section9PivotalTargets I E L R Q₁ F₁ Q₃ F₃ A targets ω).card : ℝ)} := by
  obtain ⟨C,hC,δ,hδ,hpaper⟩ := section9_source_pivotal_concentration_paper_bound
    hd asymptotics rectangle reimer
  obtain ⟨K₂,hK₂,hsecond⟩ := section9_source_target_family_second_moment_upper hd asymptotics
  refine ⟨δ,hδ,?_⟩
  intro r hr ε hε
  obtain ⟨cMean,hcMean,hpaperε⟩ := hpaper r hr
  obtain ⟨cSize,hSize,NC,hNC,hcritical⟩ := hpaperε (ε/2) (by positivity)
  let c0 := ε*cMean^2/(8*K₂)
  have hc0 : 0 < c0 := div_pos (mul_pos hε (sq_pos_of_pos hcMean)) (mul_pos (by norm_num) hK₂)
  refine ⟨cSize,hSize,c0,hc0,?_⟩
  intro CB KA hCB hKA
  obtain ⟨NM,hNM,hM₂⟩ := hsecond CB KA hCB hKA
  let N := max NC NM
  refine ⟨N,hNC.trans (le_max_left _ _),?_⟩
  intro i n hn ι I targets H₁ H₃ F₁ F₃ boundary₁ boundary₃ A B hH₁ hH₃ hpos
    hA hAreg hB hBreg hdis hAc hBc hAsize hBsize hAB L R Q₁ Q₃ ν E
  have hnC : NC ≤ n := (le_max_left NC NM).trans hn
  have hnM : NM ≤ n := (le_max_right NC NM).trans hn
  have hn1 : 1 ≤ n := hNM.trans hnM
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hAQ : A ⊆ Q₁ := fun x hx => (Finset.mem_filter.mp (hA x hx)).1
  have htargetsQ (j : ι) (hj : j ∈ I) : targets j ⊆ Q₃ := by
    intro y hy
    exact (Finset.mem_filter.mp (hB y (Finset.mem_biUnion.mpr ⟨j,hj,hy⟩))).1
  letI : IsProbabilityMeasure ν := section9RevealedLaw_isProbability (criticalPoint d)
    Q₁ H₁ Q₃ H₃ F₁ F₃ hpos
  let F := (n : ℝ)^((4 : ℝ)-(d : ℝ))*(A.card : ℝ)*(B.card : ℝ)
  let Ni := fun j ω => section9PivotalCount E L R Q₁ F₁ Q₃ F₃ A (targets j) ω
  let M₁ := fun ω => ∑ j ∈ I, Ni j ω
  let M₂ := fun ω => ∑ j ∈ I, (Ni j ω)^2
  let M₀ := fun ω => ((section9PivotalTargets I E L R Q₁ F₁ Q₃ F₃ A targets ω).card : ℝ)
  let M := section9PivotalMean ν E L R Q₁ F₁ Q₃ F₃ A B
  let Good : Set (Configuration d) := {ω | M/2 ≤ section9PivotalCount E L R Q₁ F₁ Q₃ F₃ A B ω ∧
    section9PivotalCount E L R Q₁ F₁ Q₃ F₃ A B ω ≤ 3*M/2}
  let τ := (2*K₂/ε)*F
  let Bad : Set (Configuration d) := {ω | τ ≤ M₂ ω}
  let Success : Set (Configuration d) := {ω |
    c0*(n : ℝ)^((4 : ℝ)-(d : ℝ))*(A.card : ℝ)*(B.card : ℝ) ≤ M₀ ω}
  have hapos : 0 < (A.card : ℝ) := (mul_pos hSize (pow_pos hn0 2)).trans_le hAsize
  have hbpos : 0 < (B.card : ℝ) := (mul_pos hSize (pow_pos hn0 2)).trans_le hBsize
  have hF : 0 < F := mul_pos (mul_pos (Real.rpow_pos_of_pos hn0 _) hapos) hbpos
  have hτ : 0 < τ := mul_pos (div_pos (mul_pos (by norm_num) hK₂) hε) hF
  obtain ⟨hmean,_hupper,hGood⟩ := hcritical i n hnC H₁ H₃ F₁ F₃ boundary₁ boundary₃ A B
    hH₁ hH₃ hpos hA hAreg hB hBreg hAsize hBsize hAB
  have hmeanF : cMean*F ≤ M := by convert hmean using 1 <;> dsimp only [F] <;> ring
  have hGoodProb : 1-ε/2 ≤ ν.real Good := hGood
  have hM₂int : Integrable M₂ ν := integrable_finsetSum I (fun j _ =>
    integrable_section9PivotalCount_sq ν E L R Q₁ F₁ Q₃ F₃ A (targets j))
  have hM₂nonneg (ω : Configuration d) : 0 ≤ M₂ ω := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hM₂bound : (∫ ω, M₂ ω ∂ν) ≤ K₂*F := by
    have hh := hM₂ i n hnM I targets H₁ H₃ F₁ F₃ A hH₁ hH₃ hpos hAQ htargetsQ hdis hAc hBc
    convert hh using 1 <;> dsimp only [F] <;> ring
  have hMarkov := mul_meas_ge_le_integral_of_nonneg (Filter.Eventually.of_forall hM₂nonneg) hM₂int τ
  have hBadProb : ν.real Bad ≤ ε/2 := by
    apply (mul_le_mul_iff_right₀ hτ).mp
    have hτeq : τ*(ε/2) = K₂*F := by
      dsimp only [τ]
      field_simp [ne_of_gt hε]
      <;> ring
    rw [hτeq]
    exact hMarkov.trans hM₂bound
  have hcover : Good ⊆ Success ∪ Bad := by
    intro ω hω
    by_cases hb : τ ≤ M₂ ω
    · exact Or.inr hb
    apply Or.inl
    have hglobal := section9_pivotal_count_le_target_sum I E L R Q₁ F₁ Q₃ F₃ A B targets
      (Finset.Subset.refl B) ω
    have hM₁lower : (cMean/2)*F ≤ M₁ ω := by
      change section9PivotalCount E L R Q₁ F₁ Q₃ F₃ A B ω ≤ M₁ ω at hglobal
      nlinarith only [hmeanF,hω.1,hglobal]
    have hsq : ((cMean/2)*F)^2 ≤ (M₁ ω)^2 :=
      pow_le_pow_left₀ (by positivity) hM₁lower 2
    have hcs := section9_distinct_targets_moment_bound I E L R Q₁ F₁ Q₃ F₃ A targets ω
    change (M₁ ω)^2 ≤ M₀ ω*M₂ ω at hcs
    have hτbound : M₂ ω ≤ τ := (lt_of_not_ge hb).le
    have hcombined := hsq.trans (hcs.trans
      (mul_le_mul_of_nonneg_left hτbound (Nat.cast_nonneg _)))
    have htarget : c0*F ≤ M₀ ω := by
      apply (mul_le_mul_iff_right₀ hτ).mp
      convert hcombined using 1 <;> dsimp only [c0,τ] <;>
        field_simp [ne_of_gt hε,ne_of_gt hK₂] <;> ring
    change c0*(n : ℝ)^((4 : ℝ)-(d : ℝ))*(A.card : ℝ)*(B.card : ℝ) ≤ M₀ ω
    convert htarget using 1 <;> dsimp only [F] <;> ring
  have hprobCover := (measureReal_mono (μ := ν) hcover (measure_ne_top _ _)).trans
    (measureReal_union_le Success Bad)
  change 1-ε ≤ ν.real Success
  linarith only [hGoodProb,hBadProb,hprobCover]

end NearCritical
