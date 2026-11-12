module
public import NearCritical.Section9AvoidanceGoodComparison
public import NearCritical.Section9DivisionFreeComparison
public import NearCritical.Section9UniqueLeftPivotFiberBound

/-! Actual source good-exit energy comparison, without division by mass or energy. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory
open scoped Classical BigOperators

/-- The actual unique-left fiber count controls the source good-exit energy.
All constants come from the same undivided good weighted comparison; zero
fiber mass, zero target size and zero energy are retained. -/
theorem section9_source_good_energy_bound {d : ℕ} (hd : 9 ≤ d)
    (asymptotics : TwoPointAsymptotics d) (rectangle : RestrictedRectangleLowerInput d)
    (reimer : FiniteBernoulliBKRInput) :
    ∃ U : ℝ, 0 < U ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ r : ℕ, 1 ≤ r → ∃ c : ℝ, 0 < c ∧ ∃ K : ℝ, 0 ≤ K ∧
      ∀ (i : Fin d) (n : ℕ), 16*(r+1) ≤ n →
      ∀ (H₁ H₃ F₁ F₃ boundary B C Z W : Finset (Vertex d)) (root : Vertex d),
      H₁ ⊆ section9FiniteEndCube i n 0 → H₃ ⊆ section9FiniteEndCube i n (2*(n : ℝ)) →
      percolation d (criticalPoint d) (section9RevealEvent
        (section9FiniteEndCube i n 0) H₁ (section9FiniteEndCube i n (2*(n : ℝ))) H₃ F₁ F₃) ≠ 0 →
      root ∈ section9FiniteTube i n (-(5 : ℝ)/8) (3/8) →
      C ⊆ section9FiniteTube i n (-(5 : ℝ)/8) (3/8) →
      (∀ y ∈ B, y ∈ section8ExtensionNegativeFaceCore i n) →
      (∀ y ∈ B, sourceRegularPoint F₃ ((section8ExtensionSmallCube i n).image
        (affineReflection (Pi.single i (2*(n : ℤ))))) boundary r δ y) →
      Z ⊆ section8ExtensionMiddleCore i n → Z ⊆ C → C ∩ W = {root} →
      let Q₁ := section9FiniteEndCube i n 0
      let Q₃ := section9FiniteEndCube i n (2*(n : ℝ))
      let L := section9FiniteTube i n (-(5 : ℝ)/8) (3/8)
      let R := section9FiniteTube i n (-(3 : ℝ)/8) (5/8)
      let V := section9ExitFace i n ∩ C
      let ν := section9RevealedLaw (criticalPoint d) Q₁ H₁ Q₃ H₃ F₁ F₃
      let E : Set (Configuration d) := {ω | sprinklingUnexploredCluster ω L Q₁ F₁ root = C}
      let J := section9AvoidanceGoodLastExitCandidates R C Q₃ F₃ V
      let w := fun t : (Vertex d × Vertex d) × Bond d =>
        ∑ z ∈ Z, (percolation d (criticalPoint d)).real
          (connectionToSetEvent (R : Set (Vertex d)) z {t.1.1})
      let s := (B.card : ℝ)*(n : ℝ)^((2 : ℝ)-(d : ℝ))
      let t := c-K*(n : ℝ)^((4 : ℝ)-(d : ℝ))*(V.card : ℝ)
      let P := ∫ ω in E, ((section9UniqueLeftPivotalPairs ω
        (orientedLatticePairs (section9FiniteMiddle i n)) L R Q₁ F₁ Q₃ F₃ W B root).card : ℝ) ∂ν
      s*ν.real E*(max t 0)^2*(Z.card : ℝ)^2 ≤ U*(∑ j ∈ J, (w j)^2)*P := by
  obtain ⟨G,hG,green⟩ := criticalSupGreenUpper_of_asymptotics (by omega : 2 ≤ d) asymptotics
  let U : ℝ := G*(16 : ℝ)^((d : ℝ)-2)
  have hU : 0 < U := mul_pos hG (Real.rpow_pos_of_pos (by norm_num) _)
  obtain ⟨δ,hδ,hweighted⟩ := section9_source_avoidance_good_weighted_comparison
    hd asymptotics rectangle reimer
  refine ⟨U,hU,δ,hδ,?_⟩
  intro r hr
  obtain ⟨c,hc,K,hK,hbound⟩ := hweighted r hr
  refine ⟨c,hc,K,hK,?_⟩
  intro i n hn H₁ H₃ F₁ F₃ boundary B C Z W root hH₁ hH₃ hpos hroot hCL hB hregular
    hZM hZC hUnique Q₁ Q₃ L R V ν E J w s t P
  let q := fun j : (Vertex d × Vertex d) × Bond d =>
    ν.real (E ∩ section9AvoidanceEvent (R \ C) R Q₃ F₃ B V j.1.2)
  have hnNat : 16 ≤ n := by omega
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hs : 0 ≤ s := mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg hn0.le _)
  have hz : 0 ≤ (Z.card : ℝ) := Nat.cast_nonneg _
  have hm : 0 ≤ ν.real E := measureReal_nonneg
  have hD : 0 ≤ ∑ j ∈ J, (w j)^2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hq (j) (hj : j ∈ J) : 0 ≤ q j ∧ q j ≤ (U*s)*ν.real E := by
    refine ⟨measureReal_nonneg,?_⟩
    have hh := section9_source_candidate_fiber_avoidance_upper (by omega : 2 ≤ d) hG.le green
      i n hnNat H₁ H₃ F₁ F₃ C B V root hH₁ hH₃ hpos hroot hCL hB j
      (Finset.mem_filter.mp hj).1
    change q j ≤ ν.real E*(G*(16 : ℝ)^((d : ℝ)-2)*(B.card : ℝ)*
      (n : ℝ)^((2 : ℝ)-(d : ℝ))) at hh
    convert hh using 1 <;> dsimp [U,s] <;> ring
  have hfactor := section9_avoidance_error_power_factor d (n : ℝ) hn0
  have hT : (c*(n : ℝ)^((2 : ℝ)-(d : ℝ))*(B.card : ℝ) -
      (B.card : ℝ)*(V.card : ℝ)*K*(n : ℝ)^(6-2*(d : ℝ)))*(Z.card : ℝ) =
      s*t*(Z.card : ℝ) := by
    rw [hfactor]
    dsimp [s,t]
    ring
  have hcompare := hbound i n hn H₁ H₃ F₁ F₃ boundary B C Z root
    hH₁ hH₃ hpos hroot hCL hB hregular hZM hZC
  have hweightedActual : ν.real E*(s*t*(Z.card : ℝ)) ≤ ∑ j ∈ J, w j*q j := by
    rw [← hT]
    convert hcompare using 1 <;> ring
  have hmass := section9_mass_energy_comparison J w q (ν.real E) (U*s)
    (s*t*(Z.card : ℝ)) hm (mul_nonneg hU.le hs) hq hweightedActual
  letI : IsProbabilityMeasure ν := section9RevealedLaw_isProbability (criticalPoint d)
    Q₁ H₁ Q₃ H₃ F₁ F₃ hpos
  have hfiber : (∑ j ∈ J, q j) ≤ P :=
    section9_unique_left_pivotal_fiber_bound ν i n (by omega) F₁ F₃ C W B root
      hroot hCL hUnique
  have hP : 0 ≤ P := (Finset.sum_nonneg fun j hj => (hq j hj).1).trans hfiber
  have hfinal := hmass.trans (mul_le_mul_of_nonneg_left hfiber
    (mul_nonneg (mul_nonneg hU.le hs) hD))
  have hmax : max (s*t*(Z.card : ℝ)) 0 = s*(max t 0)*(Z.card : ℝ) := by
    by_cases ht : 0 ≤ t
    · rw [max_eq_left ht,max_eq_left (mul_nonneg (mul_nonneg hs ht) hz)]
    · have ht0 : t ≤ 0 := le_of_not_ge ht
      rw [max_eq_right ht0,max_eq_right
        (mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hs ht0) hz)]
      ring
  rw [hmax] at hfinal
  by_cases hs0 : s = 0
  · simp only [hs0,zero_mul]
    exact mul_nonneg (mul_nonneg hU.le hD) hP
  have hspos : 0 < s := lt_of_le_of_ne hs (Ne.symm hs0)
  apply (mul_le_mul_iff_left₀ hspos).mp
  convert hfinal using 1 <;> ring

end NearCritical
