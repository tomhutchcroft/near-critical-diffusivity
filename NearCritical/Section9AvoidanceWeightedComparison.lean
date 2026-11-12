module
public import NearCritical.Section9SourceAvoidanceLower
public import NearCritical.Section9AvoidanceHeartComparison

/-! Actual undivided finite weighted comparison for the source avoidance lemma. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory
open scoped Classical BigOperators

/-- The source lower budget and actual last-exit upper bound yield the weighted
comparison. Both powers remain additive; no fiber division or desired weighted
probability estimate is a hypothesis. -/
theorem section9_source_avoidance_weighted_comparison {d : ℕ} (hd : 9 ≤ d)
    (asymptotics : TwoPointAsymptotics d) (rectangle : RestrictedRectangleLowerInput d)
    (reimer : FiniteBernoulliBKRInput) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ r : ℕ, 1 ≤ r → ∃ c : ℝ, 0 < c ∧ ∃ K : ℝ, 0 ≤ K ∧
      ∀ (i : Fin d) (n : ℕ), 16*(r+1) ≤ n →
      ∀ (H₁ H₃ F₁ F₃ boundary B C Z : Finset (Vertex d)) (root : Vertex d),
      H₁ ⊆ section9FiniteEndCube i n 0 → H₃ ⊆ section9FiniteEndCube i n (2*(n : ℝ)) →
      percolation d (criticalPoint d) (section9RevealEvent
        (section9FiniteEndCube i n 0) H₁ (section9FiniteEndCube i n (2*(n : ℝ))) H₃ F₁ F₃) ≠ 0 →
      root ∈ section9FiniteTube i n (-(5 : ℝ)/8) (3/8) →
      C ⊆ section9FiniteTube i n (-(5 : ℝ)/8) (3/8) →
      (∀ y ∈ B, y ∈ section8ExtensionNegativeFaceCore i n) →
      (∀ y ∈ B, sourceRegularPoint F₃ ((section8ExtensionSmallCube i n).image
        (affineReflection (Pi.single i (2*(n : ℤ))))) boundary r δ y) →
      Z ⊆ section8ExtensionMiddleCore i n → Z ⊆ C →
      let Q₁ := section9FiniteEndCube i n 0
      let Q₃ := section9FiniteEndCube i n (2*(n : ℝ))
      let L := section9FiniteTube i n (-(5 : ℝ)/8) (3/8)
      let R := section9FiniteTube i n (-(3 : ℝ)/8) (5/8)
      let V := section9ExitFace i n ∩ C
      let ν := section9RevealedLaw (criticalPoint d) Q₁ H₁ Q₃ H₃ F₁ F₃
      let E : Set (Configuration d) := {ω | sprinklingUnexploredCluster ω L Q₁ F₁ root = C}
      let J := section9AvoidanceLastExitCandidates R C Q₃ F₃
      let w := fun t : (Vertex d × Vertex d) × Bond d =>
        ∑ z ∈ Z, (percolation d (criticalPoint d)).real
          (connectionToSetEvent (R : Set (Vertex d)) z {t.1.1})
      let q := fun t : (Vertex d × Vertex d) × Bond d =>
        ν.real (E ∩ section9AvoidanceEvent (R \ C) R Q₃ F₃ B V t.1.2)
      ν.real E * (c*(n : ℝ)^((2 : ℝ)-(d : ℝ))*(B.card : ℝ) -
        (B.card : ℝ)*(V.card : ℝ)*K*(n : ℝ)^(6-2*(d : ℝ))) * (Z.card : ℝ) ≤
          ∑ t ∈ J, w t*q t := by
  obtain ⟨δ,hδ,hlower⟩ := section9_source_avoidance_lower_budget hd asymptotics rectangle
  refine ⟨δ,hδ,?_⟩
  intro r hr
  obtain ⟨c,hc,K,hK,hlow⟩ := hlower r hr
  refine ⟨c,hc,K,hK,?_⟩
  intro i n hn H₁ H₃ F₁ F₃ boundary B C Z root hH₁ hH₃ hpos hroot hCL hB hregular hZM hZC
    Q₁ Q₃ L R V ν E J w q
  let a : ℝ := c*(n : ℝ)^((2 : ℝ)-(d : ℝ))*(B.card : ℝ)
  let b : ℝ := (B.card : ℝ)*(V.card : ℝ)*K*(n : ℝ)^(6-2*(d : ℝ))
  have hm : 0 ≤ ν.real E := measureReal_nonneg
  have hnR : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hBQ₃ : B ⊆ Q₃ := fun y hy => (Finset.mem_filter.mp (hB y hy)).1
  have hzR (z : Vertex d) (hz : z ∈ Z) : z ∈ R := by
    apply (mem_section9FiniteTube i n (-(3 : ℝ)/8) (5/8) (by norm_num) (by norm_num) z).mpr
    have hs := (section8_mem_extension_middle_core i n z).mp (hZM hz)
    have hi := hs i
    simp only [ite_true] at hi
    refine ⟨by linarith,by linarith,?_⟩
    intro j hji
    have hj := hs j
    simp only [hji,ite_false,sub_zero] at hj
    constructor <;> linarith
  have heach (z : Vertex d) (hz : z ∈ Z) :
      ν.real E*(a-b) ≤ ∑ t ∈ J,
        (percolation d (criticalPoint d)).real
          (connectionToSetEvent (R : Set (Vertex d)) z {t.1.1}) * q t := by
    have hlowz := hlow i n hn H₁ H₃ F₁ F₃ boundary B C z hH₁ hH₃ hpos (hZM hz) hB hregular
    change a ≤ (percolation d (criticalPoint d)).real
      (section9AvoidanceEvent R R Q₃ F₃ B V z)+b at hlowz
    have hmul := mul_le_mul_of_nonneg_left hlowz hm
    have hupper := section9_source_avoidance_heart_fiber_candidate_bound reimer (criticalPoint d)
      i n (by omega : 0 < n) H₁ H₃ F₁ F₃ C B root hH₁ hH₃ hpos
      hroot hCL hBQ₃ (hzR z hz) (hZC hz)
    change ν.real E*(percolation d (criticalPoint d)).real
        (section9AvoidanceEvent R R Q₃ F₃ B V z) ≤
      ∑ t ∈ J, (criticalPoint d : ℝ)*(percolation d (criticalPoint d)).real
        {ω | t.1.1 ∈ sprinklingUnexploredCluster ω R Q₃ F₃ z} * q t at hupper
    calc
      _ ≤ ν.real E*(percolation d (criticalPoint d)).real
          (section9AvoidanceEvent R R Q₃ F₃ B V z) := by nlinarith only [hmul]
      _ ≤ ∑ t ∈ J, (criticalPoint d : ℝ)*(percolation d (criticalPoint d)).real
          {ω | t.1.1 ∈ sprinklingUnexploredCluster ω R Q₃ F₃ z} * q t := hupper
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro t _
        have hdrop : (criticalPoint d : ℝ)*(percolation d (criticalPoint d)).real
            {ω | t.1.1 ∈ sprinklingUnexploredCluster ω R Q₃ F₃ z} ≤
          (percolation d (criticalPoint d)).real
            {ω | t.1.1 ∈ sprinklingUnexploredCluster ω R Q₃ F₃ z} := by
          have hpref : 0 ≤ (percolation d (criticalPoint d)).real
              {ω | t.1.1 ∈ sprinklingUnexploredCluster ω R Q₃ F₃ z} := measureReal_nonneg
          simpa only [one_mul] using mul_le_mul_of_nonneg_right
            (criticalPoint d).property.2 hpref
        have hsub : {ω | t.1.1 ∈ sprinklingUnexploredCluster ω R Q₃ F₃ z} ⊆
            connectionToSetEvent (R : Set (Vertex d)) z {t.1.1} := by
          intro ω ht
          obtain ⟨huR,hreach⟩ := (mem_sprinklingUnexploredCluster ω R Q₃ F₃ z t.1.1).mp ht
          have hle : sprinklingUnexploredGraph ω R Q₃ F₃ ≤ restrictedGraph ω (R : Set (Vertex d)) :=
            fun _ _ h => ⟨h.1,h.2.1,h.2.2.1⟩
          exact ⟨hzR z hz,t.1.1,rfl,huR,hreach.mono hle⟩
        have hrelax := measureReal_mono (μ := percolation d (criticalPoint d)) hsub (measure_ne_top _ _)
        exact mul_le_mul_of_nonneg_right (hdrop.trans hrelax) (by dsimp only [q]; exact measureReal_nonneg)
  calc
    _ = ∑ z ∈ Z, ν.real E*(a-b) := by
      simp only [Finset.sum_const,nsmul_eq_mul]
      dsimp only [a,b]
      ring
    _ ≤ ∑ z ∈ Z, ∑ t ∈ J, (percolation d (criticalPoint d)).real
        (connectionToSetEvent (R : Set (Vertex d)) z {t.1.1}) * q t :=
      Finset.sum_le_sum fun z hz => heach z hz
    _ = _ := by
      dsimp only [w]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro t _
      exact (Finset.sum_mul _ _ _).symm

end NearCritical
