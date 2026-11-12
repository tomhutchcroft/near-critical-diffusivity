module
public import NearCritical.Section8UniqueExtension
public import NearCritical.Section9MiddleCoreCardLower

/-! The actual unique-left middle count and its source first moment. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory
open scoped Classical BigOperators

/-- Actual middle mass, counted only when the full W intersection is {x}. -/
def actualUniqueMiddleCount {d : ℕ} (ω : Configuration d)
    (L Q F W : Finset (Vertex d)) (x : Vertex d) (Z : Finset (Vertex d)) : ℝ :=
  if sprinklingUnexploredCluster ω L Q F x ∩ W = {x} then
    ((sprinklingUnexploredCluster ω L Q F x ∩ Z).card : ℝ) else 0

private theorem unique_middle_avoidance_iff {d : ℕ} (ω : Configuration d)
    (L Q F W : Finset (Vertex d)) (x z : Vertex d) (hxL : x ∈ L) (hxW : x ∈ W) :
    ω ∈ section9AvoidanceEvent L L Q F {z} (W \ {x}) x ↔
      sprinklingUnexploredCluster ω L Q F x ∩ W = {x} ∧
        z ∈ sprinklingUnexploredCluster ω L Q F x := by
  let C := sprinklingUnexploredCluster ω L Q F x
  have hxC : x ∈ C := root_mem_sprinklingUnexploredCluster ω L Q F hxL
  constructor
  · rintro ⟨hhit,hnon⟩
    have hunique : C ∩ W = {x} := by
      ext y
      constructor
      · intro hy
        obtain ⟨hyC,hyW⟩ := Finset.mem_inter.mp hy
        have hyx : y = x := by
          by_contra hyNot
          exact hnon ⟨y,Finset.mem_inter.mpr
            ⟨hyC,Finset.mem_sdiff.mpr ⟨hyW,by simpa only [Finset.mem_singleton] using hyNot⟩⟩⟩
        exact Finset.mem_singleton.mpr hyx
      · intro hy
        have hyx : y = x := Finset.mem_singleton.mp hy
        subst y
        exact Finset.mem_inter.mpr ⟨hxC,hxW⟩
    obtain ⟨y,hy⟩ := hhit
    obtain ⟨hyC,hyZ⟩ := Finset.mem_inter.mp hy
    have hyz : y = z := Finset.mem_singleton.mp hyZ
    exact ⟨hunique,hyz ▸ hyC⟩
  · rintro ⟨hunique,hzC⟩
    refine ⟨⟨z,Finset.mem_inter.mpr ⟨hzC,Finset.mem_singleton_self z⟩⟩,?_⟩
    rintro ⟨y,hy⟩
    obtain ⟨hyC,hyRest⟩ := Finset.mem_inter.mp hy
    obtain ⟨hyW,hyNot⟩ := Finset.mem_sdiff.mp hyRest
    apply hyNot
    rw [← hunique]
    exact Finset.mem_inter.mpr ⟨hyC,hyW⟩

/-- Exact first-moment identity for the actual count under any finite law.
Root membership supplies the distinguished W point, including zero-length paths. -/
theorem integral_actualUniqueMiddleCount {d : ℕ}
    (μ : Measure (Configuration d)) [IsFiniteMeasure μ]
    (L Q F W : Finset (Vertex d)) (x : Vertex d) (Z : Finset (Vertex d))
    (hxL : x ∈ L) (hxW : x ∈ W) :
    (∫ ω, actualUniqueMiddleCount ω L Q F W x Z ∂μ) =
      ∑ z ∈ Z, μ.real (section9AvoidanceEvent L L Q F {z} (W \ {x}) x) := by
  let E := fun z : Vertex d => section9AvoidanceEvent L L Q F {z} (W \ {x}) x
  have hE (z : Vertex d) : MeasurableSet (E z) :=
    (measurableSet_sprinklingUnexploredCluster_hits L Q F {z} x).inter
      (measurableSet_sprinklingUnexploredCluster_hits L Q F (W \ {x}) x).compl
  have hcount (ω : Configuration d) : actualUniqueMiddleCount ω L Q F W x Z =
      ∑ z ∈ Z, (E z).indicator (fun _ => (1 : ℝ)) ω := by
    let C := sprinklingUnexploredCluster ω L Q F x
    have hm (z : Vertex d) : ω ∈ E z ↔ C ∩ W = {x} ∧ z ∈ C :=
      unique_middle_avoidance_iff ω L Q F W x z hxL hxW
    change (if C ∩ W = {x} then ((C ∩ Z).card : ℝ) else 0) = _
    by_cases hu : C ∩ W = {x}
    · have hfilter : Z.filter (fun z => z ∈ C) = C ∩ Z := by
        ext z
        simp only [Finset.mem_filter,Finset.mem_inter,and_comm]
      simp only [actualUniqueMiddleCount,hu,if_pos,Set.indicator_apply,Pi.one_apply,hm,true_and]
      rw [Finset.sum_boole,hfilter]
    · simp only [actualUniqueMiddleCount,hu,if_neg,Set.indicator_apply,Pi.one_apply,hm,false_and,
        ite_false,Finset.sum_const_zero]
  simp_rw [hcount]
  rw [integral_finsetSum _ (fun z _ => (integrable_const (1 : ℝ)).indicator (hE z))]
  apply Finset.sum_congr rfl
  intro z _
  have hone : (fun _ : Configuration d => (1 : ℝ)) = (1 : Configuration d → ℝ) := by
    funext ω
    simp only [Pi.one_apply]
  rw [hone]
  exact integral_indicator_one (μ := μ) (hE z)

/-- Actual source X1 has expectation at least cX*n², uniformly in source
scale and revealed data. Delta is fixed before r. Both the unique-extension
probabilities and the volume lower bound are proved ingredients. -/
theorem section9_source_unique_middle_first_moment_lower {d : ℕ} (hd : 9 ≤ d)
    (asymptotics : TwoPointAsymptotics d) (rectangle : RestrictedRectangleLowerInput d) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ r : ℕ, 1 ≤ r → ∃ cX : ℝ, 0 < cX ∧
      ∀ (i : Fin d) (n : ℕ), 16*(r+1) ≤ n →
      ∀ (H₁ H₃ F₁ F₃ boundary : Finset (Vertex d)) (x : Vertex d),
      H₁ ⊆ section9FiniteEndCube i n 0 → H₃ ⊆ section9FiniteEndCube i n (2*(n : ℝ)) →
      percolation d (criticalPoint d) (section9RevealEvent
        (section9FiniteEndCube i n 0) H₁ (section9FiniteEndCube i n (2*(n : ℝ))) H₃ F₁ F₃) ≠ 0 →
      x ∈ section8ExtensionPositiveFaceCore i n →
      sourceRegularPoint F₁ (section8ExtensionSmallCube i n) boundary r δ x →
      let L := section9FiniteTube i n (-(5 : ℝ)/8) (3/8)
      let Q₁ := section9FiniteEndCube i n 0
      let Q₃ := section9FiniteEndCube i n (2*(n : ℝ))
      let ν := section9RevealedLaw (criticalPoint d) Q₁ H₁ Q₃ H₃ F₁ F₃
      cX*(n : ℝ)^2 ≤ ∫ ω,
        actualUniqueMiddleCount ω L Q₁ F₁ (F₁ ∩ boundary) x (section8ExtensionMiddleCore i n) ∂ν := by
  obtain ⟨δ,hδ,hext⟩ := section8_source_unique_extension hd asymptotics rectangle
  refine ⟨δ,hδ,?_⟩
  intro r hr
  obtain ⟨c,hc,hbound⟩ := hext r hr
  refine ⟨c/(8 : ℝ)^d,div_pos hc (by positivity),?_⟩
  intro i n hn H₁ H₃ F₁ F₃ boundary x hH₁ hH₃ hpos hx hreg L Q₁ Q₃ ν
  have hn1 : 1 ≤ n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  letI : IsProbabilityMeasure ν := section9RevealedLaw_isProbability (criticalPoint d)
    Q₁ H₁ Q₃ H₃ F₁ F₃ hpos
  have hcard := section9_middle_core_card_lower i n hn1
  have hcardPos : 0 < ((section8ExtensionMiddleCore i n).card : ℝ) :=
    (div_pos (pow_pos hnR d) (by positivity)).trans_le hcard
  have hcardNat : 0 < (section8ExtensionMiddleCore i n).card := by exact_mod_cast hcardPos
  obtain ⟨z,hz⟩ := Finset.card_pos.mp hcardNat
  have hgeom := section8_extension_source_geometry i n r hn hx hz
  have hxI : x ∈ section8OutwardSegment x i r := by
    apply (section8_mem_outward_segment x x i r).mpr
    exact ⟨0,by omega,by simp⟩
  have hxL : x ∈ L := hgeom.2.1 hxI
  have hxW : x ∈ F₁ ∩ boundary := hreg.1
  rw [integral_actualUniqueMiddleCount ν L Q₁ F₁ (F₁ ∩ boundary) x
    (section8ExtensionMiddleCore i n) hxL hxW]
  have hp : (n : ℝ)^d*(n : ℝ)^((2 : ℝ)-(d : ℝ)) = (n : ℝ)^2 := by
    rw [← Real.rpow_natCast (n : ℝ) d,← Real.rpow_add hnR]
    have he : (d : ℝ)+((2 : ℝ)-(d : ℝ)) = 2 := by ring
    rw [he,Real.rpow_two]
  calc
    _ = ((n : ℝ)^d/(8 : ℝ)^d)*(c*(n : ℝ)^((2 : ℝ)-(d : ℝ))) := by
      rw [← hp]
      ring
    _ ≤ ((section8ExtensionMiddleCore i n).card : ℝ)*(c*(n : ℝ)^((2 : ℝ)-(d : ℝ))) :=
      mul_le_mul_of_nonneg_right hcard (mul_nonneg hc.le (Real.rpow_nonneg hnR.le _))
    _ = ∑ _z ∈ section8ExtensionMiddleCore i n, c*(n : ℝ)^((2 : ℝ)-(d : ℝ)) := by
      rw [Finset.sum_const,nsmul_eq_mul]
    _ ≤ _ := Finset.sum_le_sum fun z hz =>
      hbound i n hn H₁ H₃ F₁ F₃ boundary x z hH₁ hH₃ hpos hx hz hreg

end NearCritical
