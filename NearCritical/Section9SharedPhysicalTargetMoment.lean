module
public import NearCritical.Section9SharedOrientedTargetMoment
public import NearCritical.Section9PhysicalTargetOverlap
public import NearCritical.Section9MeanUpperScale
public import NearCritical.Section9FiniteLocalIntegrability

/-! Actual physical shared-target moment, including reversal aliases. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory
open scoped Classical BigOperators

/-- Actual physical overlap is bounded using SAME-oriented overlap plus the
actual first moment. No orientation injectivity or independence is assumed. -/
theorem section9_source_shared_physical_target_moment_upper {d : ℕ} (hd : 9 ≤ d)
    (asymptotics : TwoPointAsymptotics d) (r : ℕ) (hr : 1 ≤ r) (δ : ℝ) (hδ : 0 ≤ δ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (i : Fin d) (n : ℕ), 2 ≤ n →
      ∀ {ι : Type*} (I : Finset ι) (targets : ι → Finset (Vertex d))
        (H₁ H₃ F₁ F₃ boundary₃ A : Finset (Vertex d)),
      H₁ ⊆ section9FiniteEndCube i n 0 → H₃ ⊆ section9FiniteEndCube i n (2*(n : ℝ)) →
      percolation d (criticalPoint d) (section9RevealEvent
        (section9FiniteEndCube i n 0) H₁ (section9FiniteEndCube i n (2*(n : ℝ))) H₃ F₁ F₃) ≠ 0 →
      A ⊆ section9FiniteEndCube i n 0 → Set.PairwiseDisjoint (I : Set ι) targets →
      (∀ j ∈ I, ∀ b ∈ targets j, b ∈ section8ExtensionNegativeFaceCore i n) →
      (∀ j ∈ I, ∀ b ∈ targets j, sourceRegularPoint F₃
        ((section8ExtensionSmallCube i n).image (affineReflection (Pi.single i (2*(n : ℤ)))))
        boundary₃ r δ b) →
      let B := I.biUnion targets
      let L := section9FiniteTube i n (-(5 : ℝ)/8) (3/8)
      let R := section9FiniteTube i n (-(3 : ℝ)/8) (5/8)
      let Q₁ := section9FiniteEndCube i n 0
      let Q₃ := section9FiniteEndCube i n (2*(n : ℝ))
      let E := orientedLatticePairs (section9FiniteMiddle i n)
      let ν := section9RevealedLaw (criticalPoint d) Q₁ H₁ Q₃ H₃ F₁ F₃
      ∀ bond : (Vertex d × Vertex d) → Bond d,
      (∀ e ∈ E, s((bond e).1,bondTip (bond e)) = s(e.1,e.2)) →
      (∫ ω, (∑ j ∈ I, ∑ k ∈ I.erase j,
        (((sprinklingPivotalPairs ω E L R Q₁ F₁ Q₃ F₃ A (targets j)).image bond ∩
          (sprinklingPivotalPairs ω E L R Q₁ F₁ Q₃ F₃ A (targets k)).image bond).card : ℝ)) ∂ν) ≤
        K*(n : ℝ)^((4 : ℝ)-(d : ℝ))*(A.card : ℝ)*(B.card : ℝ) := by
  obtain ⟨Kw,hKw,hshared⟩ := section9_source_shared_oriented_target_moment_upper
    hd asymptotics r hr δ hδ
  obtain ⟨Cmean,hCmean,hmean⟩ := section9ConditionalMean_upper_scale (by omega : 2 ≤ d) asymptotics
  refine ⟨2*Kw+Cmean,by positivity,?_⟩
  intro i n hn ι I targets H₁ H₃ F₁ F₃ boundary₃ A hH₁ hH₃ hpos hA hdis hface hregular
    B L R Q₁ Q₃ E ν bond hbond
  have hn0 : 0 < n := by omega
  letI : IsProbabilityMeasure ν := section9RevealedLaw_isProbability (criticalPoint d)
    Q₁ H₁ Q₃ H₃ F₁ F₃ hpos
  let Pi := fun ω j => sprinklingPivotalPairs ω E L R Q₁ F₁ Q₃ F₃ A (targets j)
  let Wp := fun ω : Configuration d => ∑ j ∈ I, ∑ k ∈ I.erase j,
    (((Pi ω j).image bond ∩ (Pi ω k).image bond).card : ℝ)
  let Wo := fun ω : Configuration d => ∑ j ∈ I, ∑ k ∈ I.erase j,
    ((Pi ω j ∩ Pi ω k).card : ℝ)
  let M₁ := fun ω : Configuration d => ∑ j ∈ I, ((Pi ω j).card : ℝ)
  let U := sprinklingAvailableBonds L Q₁ F₁ ∪ sprinklingAvailableBonds R Q₃ F₃
  have hfamily (ω θ : Configuration d) (hagree : ∀ b ∈ U, ω b = θ b) : Pi ω = Pi θ := by
    funext j
    ext e
    have hL : ∀ b ∈ sprinklingAvailableBonds L Q₁ F₁, ω b = θ b :=
      fun b hb => hagree b (Finset.mem_union_left _ hb)
    have hR : ∀ b ∈ sprinklingAvailableBonds R Q₃ F₃, ω b = θ b :=
      fun b hb => hagree b (Finset.mem_union_right _ hb)
    simp only [Pi,sprinklingPivotalPairs,Finset.mem_filter,
      sprinklingPivotalPair_iff_of_available_agree L R Q₁ F₁ Q₃ F₃ A (targets j) ω θ hL hR e]
  have hiP : Integrable Wp ν := by
    apply section9_finite_local_integrable ν U Wp
    intro ω θ hagree
    exact congrArg (fun P : ι → Finset (Vertex d × Vertex d) =>
      ∑ j ∈ I, ∑ k ∈ I.erase j, (((P j).image bond ∩ (P k).image bond).card : ℝ))
      (hfamily ω θ hagree)
  have hiO : Integrable Wo ν := by
    apply section9_finite_local_integrable ν U Wo
    intro ω θ hagree
    exact congrArg (fun P : ι → Finset (Vertex d × Vertex d) =>
      ∑ j ∈ I, ∑ k ∈ I.erase j, ((P j ∩ P k).card : ℝ)) (hfamily ω θ hagree)
  have hiSingle (j : ι) : Integrable (fun ω => ((Pi ω j).card : ℝ)) ν :=
    integrable_section9PivotalCount ν E L R Q₁ F₁ Q₃ F₃ A (targets j)
  have hiM : Integrable M₁ ν := integrable_finsetSum I (fun j _ => hiSingle j)
  have hpoint (ω : Configuration d) : Wp ω ≤ 2*Wo ω+M₁ ω :=
    section9_shared_physical_pivot_overlap_le I (Pi ω) bond
      (fun j _ e he => hbond e (Finset.mem_filter.mp he).1)
  have htargets (j : ι) (hj : j ∈ I) : targets j ⊆ Q₃ :=
    fun y hy => (Finset.mem_filter.mp (hface j hj y hy)).1
  have hMbound : (∫ ω, M₁ ω ∂ν) ≤
      Cmean*(n : ℝ)^((4 : ℝ)-(d : ℝ))*(A.card : ℝ)*(B.card : ℝ) := by
    rw [integral_finsetSum I (fun j _ => hiSingle j)]
    have hcard : (∑ j ∈ I, ((targets j).card : ℝ)) = (B.card : ℝ) := by
      exact_mod_cast (Finset.card_biUnion hdis).symm
    calc
      _ ≤ ∑ j ∈ I, Cmean*(n : ℝ)^((4 : ℝ)-(d : ℝ))*(A.card : ℝ)*((targets j).card : ℝ) := by
        apply Finset.sum_le_sum
        intro j hj
        exact hmean i n hn0 H₁ H₃ F₁ F₃ A (targets j) hH₁ hH₃ hA (htargets j hj) hpos
      _ = _ := by rw [← Finset.mul_sum,hcard]
  have hObound : (∫ ω, Wo ω ∂ν) ≤
      Kw*(n : ℝ)^((4 : ℝ)-(d : ℝ))*(A.card : ℝ)*(B.card : ℝ) :=
    hshared i n hn I targets H₁ H₃ F₁ F₃ boundary₃ A hH₁ hH₃ hpos hA hdis hface hregular
  calc
    _ ≤ ∫ ω, 2*Wo ω+M₁ ω ∂ν := integral_mono hiP ((hiO.const_mul 2).add hiM) hpoint
    _ = 2*(∫ ω, Wo ω ∂ν)+(∫ ω, M₁ ω ∂ν) := by
      rw [integral_add (hiO.const_mul 2) hiM,integral_const_mul]
    _ ≤ 2*(Kw*(n : ℝ)^((4 : ℝ)-(d : ℝ))*(A.card : ℝ)*(B.card : ℝ))+
        Cmean*(n : ℝ)^((4 : ℝ)-(d : ℝ))*(A.card : ℝ)*(B.card : ℝ) :=
      add_le_add (mul_le_mul_of_nonneg_left hObound (by norm_num)) hMbound
    _ = _ := by ring

end NearCritical
