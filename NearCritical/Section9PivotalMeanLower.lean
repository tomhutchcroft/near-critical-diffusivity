module
public import NearCritical.Section9ActualFiberAveraging
public import NearCritical.Section9GoodEnergyExpectation
public import NearCritical.Section9UniqueMiddleNumerator

/-! Actual source pivotal mean lower bound, assembled without fiber division. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory
open scoped Classical BigOperators

private theorem mean_lower_regular_mono {d : ℕ} (F S boundary : Finset (Vertex d))
    (r : ℕ) (δ δ' : ℝ) (x : Vertex d) (hle : δ ≤ δ')
    (h : sourceRegularPoint F S boundary r δ x) : sourceRegularPoint F S boundary r δ' x :=
  ⟨h.1,h.2.1.trans hle,h.2.2.trans hle⟩

private theorem mean_lower_unique_integrable {d : ℕ}
    (μ : Measure (Configuration d)) [IsFiniteMeasure μ]
    (E : Finset (Vertex d × Vertex d)) (L R Q₁ F₁ Q₃ F₃ W B : Finset (Vertex d))
    (x : Vertex d) : Integrable
      (fun ω => ((section9UniqueLeftPivotalPairs ω E L R Q₁ F₁ Q₃ F₃ W B x).card : ℝ)) μ := by
  let T := sprinklingAvailableBonds L Q₁ F₁ ∪ sprinklingAvailableBonds R Q₃ F₃
  apply section9_finite_local_integrable μ T
  intro ω θ hagree
  have heqL := sprinklingUnexploredCluster_eq_of_available_agree L Q₁ F₁ ω θ
    (fun b hb => hagree b (Finset.mem_union_left _ hb))
  have heqR := sprinklingUnexploredCluster_eq_of_available_agree R Q₃ F₃ ω θ
    (fun b hb => hagree b (Finset.mem_union_right _ hb))
  have hp : section9UniqueLeftPivotalPairs ω E L R Q₁ F₁ Q₃ F₃ W B x =
      section9UniqueLeftPivotalPairs θ E L R Q₁ F₁ Q₃ F₃ W B x := by
    ext e
    simp only [section9UniqueLeftPivotalPairs,sprinklingPivotalPairs,Finset.mem_filter,
      sprinklingPivotalPair,heqL e.1,heqR e.2]
  exact congrArg (fun S : Finset (Vertex d × Vertex d) => (S.card : ℝ)) hp

/-- Source prop.mean.pivAB for the actual canonical pivotal count and actual
positive outer-heart reveal law. The common regularity threshold is fixed
before r; all scale and lower-bound constants are uniform in the source data. -/
theorem section9_source_pivotal_mean_lower {d : ℕ} (hd : 9 ≤ d)
    (asymptotics : TwoPointAsymptotics d) (rectangle : RestrictedRectangleLowerInput d)
    (reimer : FiniteBernoulliBKRInput) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ r : ℕ, 1 ≤ r → ∃ cMean : ℝ, 0 < cMean ∧
      ∃ N : ℕ, 16*(r+1) ≤ N ∧ ∀ (i : Fin d) (n : ℕ), N ≤ n →
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
      cMean*(n : ℝ)^((4 : ℝ)-(d : ℝ))*(A.card : ℝ)*(B.card : ℝ) ≤
        ∫ ω, section9PivotalCount (orientedLatticePairs (section9FiniteMiddle i n))
          L R Q₁ F₁ Q₃ F₃ A B ω ∂ν := by
  obtain ⟨U,hU,δR,hδR,haverage⟩ := section9_source_actual_fiber_energy_bound
    hd asymptotics rectangle reimer
  obtain ⟨δL,hδL,hnumerator⟩ := section9_source_unique_middle_numerator_lower hd asymptotics rectangle
  obtain ⟨Kd,hKd,hdenominator⟩ := section9_source_good_exit_energy_moment_upper hd asymptotics
  let δ := min δL δR
  refine ⟨δ,lt_min hδL hδR,?_⟩
  intro r hr
  obtain ⟨c,hc,K,hK,havg⟩ := haverage r hr
  obtain ⟨a,ha,N,hN,hnum⟩ := hnumerator r hr c hc K hK
  let cMean := a^2/(U*(Kd+1))
  have hKdpos : 0 < Kd+1 := by linarith
  have hcMean : 0 < cMean := div_pos (sq_pos_of_pos ha) (mul_pos hU hKdpos)
  refine ⟨cMean,hcMean,N,hN,?_⟩
  intro i n hn H₁ H₃ F₁ F₃ boundary₁ boundary₃ A B hH₁ hH₃ hpos hA hAreg hB hBreg L R Q₁ Q₃ ν
  have hnScale : 16*(r+1) ≤ n := hN.trans hn
  have hn1 : 1 ≤ n := by omega
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  let W := F₁ ∩ boundary₁
  let E := orientedLatticePairs (section9FiniteMiddle i n)
  let g := fun x ω => ((section9UniqueLeftPivotalPairs ω E L R Q₁ F₁ Q₃ F₃ W B x).card : ℝ)
  letI : IsProbabilityMeasure ν := section9RevealedLaw_isProbability (criticalPoint d)
    Q₁ H₁ Q₃ H₃ F₁ F₃ hpos
  have hBregR (y : Vertex d) (hy : y ∈ B) : sourceRegularPoint F₃
      ((section8ExtensionSmallCube i n).image (affineReflection (Pi.single i (2*(n : ℤ)))))
      boundary₃ r δR y :=
    mean_lower_regular_mono _ _ _ r δ δR y (min_le_right _ _) (hBreg y hy)
  have hmidpos : 0 < ((section8ExtensionMiddleCore i n).card : ℝ) :=
    (div_pos (pow_pos hn0 d) (by positivity)).trans_le (section9_middle_core_card_lower i n hn1)
  obtain ⟨z₀,hz₀⟩ := Finset.card_pos.mp
    (show 0 < (section8ExtensionMiddleCore i n).card by exact_mod_cast hmidpos)
  have hsingle (x : Vertex d) (hx : x ∈ A) :
      cMean*(B.card : ℝ)*(n : ℝ)^((4 : ℝ)-(d : ℝ)) ≤ ∫ ω, g x ω ∂ν := by
    have hxFace := hA x hx
    have hgeom := section8_extension_source_geometry i n r hnScale hxFace hz₀
    have hxI : x ∈ section8OutwardSegment x i r :=
      (section8_mem_outward_segment x x i r).mpr ⟨0,by omega,by simp⟩
    have hxL : x ∈ L := hgeom.2.1 hxI
    have hxReg : sourceRegularPoint F₁ (section8ExtensionSmallCube i n) boundary₁ r δL x :=
      mean_lower_regular_mono _ _ _ r δ δL x (min_le_left _ _) (hAreg x hx)
    let cluster := fun ω => sprinklingUnexploredCluster ω L Q₁ F₁ x
    let X := fun C : Finset (Vertex d) => if C ∩ W = {x} then
      max (c-K*(n : ℝ)^((4 : ℝ)-(d : ℝ))*((section9ExitFace i n ∩ C).card : ℝ)) 0 *
        ((C ∩ section8ExtensionMiddleCore i n).card : ℝ) else 0
    let X₁ := fun ω => actualUniqueMiddleCount ω L Q₁ F₁ W x (section8ExtensionMiddleCore i n)
    let X₂ := fun ω => (n : ℝ)^((4 : ℝ)-(d : ℝ))*X₁ ω*
      ((cluster ω ∩ section9ExitFace i n).card : ℝ)
    let Num := fun ω => max (c*X₁ ω-K*X₂ ω) 0
    let s := (B.card : ℝ)*(n : ℝ)^((2 : ℝ)-(d : ℝ))
    have hs : 0 ≤ s := mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg hn0.le _)
    have hXeq (ω : Configuration d) : X (cluster ω) = Num ω := by
      by_cases hu : cluster ω ∩ W = {x}
      · dsimp only [cluster] at hu
        dsimp only [X,Num,X₁,X₂,actualUniqueMiddleCount,cluster]
        simp only [if_pos hu]
        rw [Finset.inter_comm (section9ExitFace i n) (sprinklingUnexploredCluster ω L Q₁ F₁ x),
          max_mul_of_nonneg _ _ (Nat.cast_nonneg _),zero_mul]
        congr 1 <;> ring
      · dsimp only [cluster] at hu
        simp [X,Num,X₁,X₂,actualUniqueMiddleCount,cluster,hu]
    have hnumActual := hnum i n hn H₁ H₃ F₁ F₃ boundary₁ x hH₁ hH₃ hpos hxFace hxReg
    change a*(n : ℝ)^2 ≤ ∫ ω, Num ω ∂ν at hnumActual
    have hnumLower : a*(n : ℝ)^2 ≤ ∫ ω, X (cluster ω) ∂ν :=
      hnumActual.trans_eq (integral_congr_ae (ae_of_all _ (fun ω => (hXeq ω).symm)))
    have havgActual := havg i n hnScale H₁ H₃ F₁ F₃ boundary₃ B W x
      hH₁ hH₃ hpos hxL hB hBregR
    change (s/U)*(∫ ω, X (cluster ω) ∂ν)^2 ≤
      (∫ ω, section9GoodExitEnergy i n F₃ (cluster ω) ∂ν)*(∫ ω, g x ω ∂ν) at havgActual
    have hdenActual := hdenominator i n hn1 H₁ H₃ F₁ F₃ x hH₁ hH₃ hpos hxL
    have hdenUpper : (∫ ω, section9GoodExitEnergy i n F₃ (cluster ω) ∂ν) ≤
        (Kd+1)*(n : ℝ)^2 :=
      hdenActual.trans (mul_le_mul_of_nonneg_right (by linarith : Kd ≤ Kd+1) (sq_nonneg _))
    have hg0 : 0 ≤ ∫ ω, g x ω ∂ν := integral_nonneg fun _ => Nat.cast_nonneg _
    have hsq : (a*(n : ℝ)^2)^2 ≤ (∫ ω, X (cluster ω) ∂ν)^2 :=
      pow_le_pow_left₀ (by positivity) hnumLower 2
    have hcombined := (mul_le_mul_of_nonneg_left hsq (div_nonneg hs hU.le)).trans
      (havgActual.trans (mul_le_mul_of_nonneg_right hdenUpper hg0))
    have hdivide : ((s/U)*a^2*(n : ℝ)^2)/(Kd+1) ≤ ∫ ω, g x ω ∂ν := by
      apply (div_le_iff₀ hKdpos).mpr
      apply (mul_le_mul_iff_right₀ (pow_pos hn0 2)).mp
      convert hcombined using 1 <;> ring
    have hpower : (n : ℝ)^((2 : ℝ)-(d : ℝ))*(n : ℝ)^2 =
        (n : ℝ)^((4 : ℝ)-(d : ℝ)) := by
      rw [← Real.rpow_natCast (n : ℝ) 2,← Real.rpow_add hn0]
      congr 1 <;> norm_num <;> ring
    calc
      _ = ((s/U)*a^2*(n : ℝ)^2)/(Kd+1) := by
        rw [← hpower]
        dsimp only [cMean,s]
        field_simp [ne_of_gt hU,ne_of_gt hKdpos]
        <;> ring
      _ ≤ _ := hdivide
  have hgi (x : Vertex d) : Integrable (g x) ν :=
    mean_lower_unique_integrable ν E L R Q₁ F₁ Q₃ F₃ W B x
  have hsumLower : (A.card : ℝ)*(cMean*(B.card : ℝ)*(n : ℝ)^((4 : ℝ)-(d : ℝ))) ≤
      ∫ ω, ∑ x ∈ A, g x ω ∂ν := by
    rw [integral_finsetSum A (fun x _ => hgi x)]
    calc
      _ = ∑ _x ∈ A, cMean*(B.card : ℝ)*(n : ℝ)^((4 : ℝ)-(d : ℝ)) := by
        rw [Finset.sum_const,nsmul_eq_mul]
      _ ≤ _ := Finset.sum_le_sum hsingle
  have hsumUpper : (∫ ω, ∑ x ∈ A, g x ω ∂ν) ≤
      ∫ ω, section9PivotalCount E L R Q₁ F₁ Q₃ F₃ A B ω ∂ν := by
    apply integral_mono (integrable_finsetSum A (fun x _ => hgi x))
      (integrable_section9PivotalCount ν E L R Q₁ F₁ Q₃ F₃ A B)
    intro ω
    exact section9_unique_left_pivotal_count_le ω E L R Q₁ F₁ Q₃ F₃ W A B
  convert hsumLower.trans hsumUpper using 1 <;> ring

end NearCritical
