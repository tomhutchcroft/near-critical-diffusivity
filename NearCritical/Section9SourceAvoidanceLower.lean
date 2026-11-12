module
public import NearCritical.Section9RightBoundaryBaseline
public import NearCritical.Section9RightFreshProbability
public import NearCritical.Section9AvoidanceSeparation
public import NearCritical.Section9AvoidanceBadHit

/-! Actual source lower budget for the fresh-copy avoidance event. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory
open scoped Classical

/-- The actual source baseline minus the derived bad-hit error. All constants
precede the source scale, heart values, and target sets; no desired probability
estimate is supplied as an input. -/
theorem section9_source_avoidance_lower_budget {d : ℕ} (hd : 9 ≤ d)
    (asymptotics : TwoPointAsymptotics d) (rectangle : RestrictedRectangleLowerInput d) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ r : ℕ, 1 ≤ r → ∃ c : ℝ, 0 < c ∧ ∃ K : ℝ, 0 ≤ K ∧
      ∀ (i : Fin d) (n : ℕ), 16*(r+1) ≤ n →
      ∀ (H₁ H₃ F₁ F₃ boundary B C : Finset (Vertex d)) (z : Vertex d),
      H₁ ⊆ section9FiniteEndCube i n 0 → H₃ ⊆ section9FiniteEndCube i n (2*(n : ℝ)) →
      percolation d (criticalPoint d) (section9RevealEvent
        (section9FiniteEndCube i n 0) H₁ (section9FiniteEndCube i n (2*(n : ℝ))) H₃ F₁ F₃) ≠ 0 →
      z ∈ section8ExtensionMiddleCore i n →
      (∀ y ∈ B, y ∈ section8ExtensionNegativeFaceCore i n) →
      (∀ y ∈ B, sourceRegularPoint F₃ ((section8ExtensionSmallCube i n).image
        (affineReflection (Pi.single i (2*(n : ℤ))))) boundary r δ y) →
      let Q₃ := section9FiniteEndCube i n (2*(n : ℝ))
      let R := section9FiniteTube i n (-(3 : ℝ)/8) (5/8)
      let V := section9ExitFace i n ∩ C
      c*(n : ℝ)^((2 : ℝ)-(d : ℝ))*(B.card : ℝ) ≤
        (percolation d (criticalPoint d)).real (section9AvoidanceEvent R R Q₃ F₃ B V z) +
          (B.card : ℝ)*(V.card : ℝ)*K*(n : ℝ)^(6-2*(d : ℝ)) := by
  obtain ⟨δ,hδ,hbaseline⟩ := section9_right_regular_boundary_baseline hd asymptotics rectangle
  obtain ⟨G,hG,green⟩ := criticalSupGreenUpper_of_asymptotics (by omega : 2 ≤ d) asymptotics
  obtain ⟨K,hK,hbad⟩ := section9_avoidance_baseline_le_avoidance_add_bad_hit
    (by omega : 5 ≤ d) hG.le green
  refine ⟨δ,hδ,?_⟩
  intro r hr
  obtain ⟨c,hc,hbase⟩ := hbaseline r hr
  refine ⟨c,hc,K,hK,?_⟩
  intro i n hn H₁ H₃ F₁ F₃ boundary B C z hH₁ hH₃ hpos hz hface hregular Q₃ R V
  have hn0 : 0 < n := by omega
  have hn16 : 16 ≤ n := by omega
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hbaseν := hbase i n hn H₁ H₃ F₁ F₃ boundary B z hH₁ hH₃ hpos hz hface hregular
  have hfresh := section9_source_right_hit_fresh_probability (criticalPoint d)
    i n hn0 H₁ H₃ F₁ F₃ B z hH₁ hH₃ hpos
  dsimp only at hbaseν
  rw [hfresh] at hbaseν
  have hbaseμ : c*(n : ℝ)^((2 : ℝ)-(d : ℝ))*(B.card : ℝ) ≤
      (percolation d (criticalPoint d)).real
        {ω | (sprinklingUnexploredCluster ω R Q₃ F₃ z ∩ B).Nonempty} := hbaseν
  by_cases hB : B = ∅
  · simp only [hB,Finset.card_empty,Nat.cast_zero,mul_zero,zero_mul,add_zero]
    exact measureReal_nonneg
  by_cases hV : V = ∅
  · have he : section9AvoidanceEvent R R Q₃ F₃ B V z =
        {ω | (sprinklingUnexploredCluster ω R Q₃ F₃ z ∩ B).Nonempty} := by
      ext ω
      simp [section9AvoidanceEvent,hV]
    rw [he]
    simpa only [hV,Finset.card_empty,Nat.cast_zero,mul_zero,zero_mul,add_zero] using hbaseμ
  obtain ⟨y₀,hy₀⟩ := Finset.nonempty_iff_ne_empty.mpr hB
  obtain ⟨v₀,hv₀⟩ := Finset.nonempty_iff_ne_empty.mpr hV
  have hsep (y : Vertex d) (hy : y ∈ B) (v : Vertex d) (hv : v ∈ V) :=
    section9_source_avoidance_pair_separation i n hn16 z y v hz (hface y hy)
      (Finset.mem_inter.mp hv).1
  have hzR : z ∈ R := by
    apply (mem_section9FiniteTube i n (-(3 : ℝ)/8) (5/8) (by norm_num) (by norm_num) z).mpr
    have hs := (section8_mem_extension_middle_core i n z).mp hz
    have hzi := hs i
    simp only [ite_true] at hzi
    refine ⟨by linarith,by linarith,?_⟩
    intro j hji
    have hj := hs j
    simp only [hji,ite_false,sub_zero] at hj
    constructor <;> linarith
  exact hbaseμ.trans (hbad R Q₃ F₃ B V z hzR (n : ℝ) hnR
    (fun y hy => (hsep y hy v₀ hv₀).1)
    (fun v hv => (hsep y₀ hy₀ v hv).2.1)
    (fun y hy v hv => (hsep y hy v hv).2.2))

end NearCritical
