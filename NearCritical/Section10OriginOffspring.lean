module

public import NearCritical.Section9SourceOpenedTargets
public import NearCritical.Section10OffspringCount
public import NearCritical.Section10Section9Regularity

/-! The offspring lower bound of `prop.sprinkling.AB.disjoint` under the
UNCONDITIONAL product law, at the origin.

`origin_offspring_failure_le` combines

* `section9_source_many_opened_pivotal_targets` (many opened targets under the
  revealed law; cited inputs: assumption (A), the restricted rectangle lower
  bound, Reimer's inequality),
* `openedTargets_prod_eq` (revealed law = product law for this event),
* `offspringFailure_le` (opened targets are offspring),

into: under `P_{p_c} x P_q`, fewer than `N <= m + 1` offspring occur with
probability at most `eps`. The quantifier structure and the hypotheses on
`A`, the target patches and the revealed sets are those of the Section 9
theorem, with candidates as the index set.
-/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open MeasureTheory
open scoped Classical

lemma translateSites_zero_eq {d : ℕ} (U : Finset (Vertex d)) : translateSites 0 U = U := by
  unfold translateSites
  have h : (fun x : Vertex d => 0 + x) = id := by
    funext x
    exact zero_add x
  rw [h, Finset.image_id]

lemma origin_L_disjoint_far {d n : ℕ} (i : Fin d) :
    Disjoint (section9FiniteTube i n (-(5 : ℝ)/8) (3/8))
      (section9FiniteEndCube i n (2 * (n : ℝ))) := by
  by_cases hn : 0 < n
  · have h := stepL_disjoint_far_cube n (0 : Vertex d) i
    unfold stepL at h
    rw [translateSites_zero_eq, typicalCube_far_eq_endCube hn i] at h
    exact h
  · have hn0 : n = 0 := by omega
    subst hn0
    rw [Finset.disjoint_left]
    intro x hx _
    have h := (mem_section9FiniteTube i 0 _ _ (by norm_num) (by norm_num) x).mp hx
    obtain ⟨h1, h2, _⟩ := h
    simp only [Nat.cast_zero, mul_zero, add_zero] at h1 h2
    linarith

lemma origin_R_disjoint_near {d n : ℕ} (i : Fin d) :
    Disjoint (section9FiniteTube i n (-(3 : ℝ)/8) (5/8)) (section9FiniteEndCube i n 0) := by
  by_cases hn : 0 < n
  · have h := stepR_disjoint_near_cube n (0 : Vertex d) i
    unfold stepR at h
    rw [translateSites_zero_eq, typicalCube_zero_eq_endCube hn i] at h
    exact h
  · have hn0 : n = 0 := by omega
    subst hn0
    rw [Finset.disjoint_left]
    intro x hx _
    have h := (mem_section9FiniteTube i 0 _ _ (by norm_num) (by norm_num) x).mp hx
    obtain ⟨h1, h2, _⟩ := h
    simp only [Nat.cast_zero, mul_zero, add_zero] at h1 h2
    linarith

/-- **Offspring lower bound under the product law** (origin, direction `i`). -/
theorem origin_offspring_failure_le {d : ℕ} (hd : 9 ≤ d)
    (asymptotics : TwoPointAsymptotics d) (rectangle : RestrictedRectangleLowerInput d)
    (reimer : FiniteBernoulliBKRInput) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ r : ℕ, 1 ≤ r → ∀ ε : ℝ, 0 < ε →
      ∃ cSize : ℝ, 0 < cSize ∧ ∀ m : ℕ, ∃ Lambda : ℝ, 0 < Lambda ∧
      ∀ CB KA : ℝ, 0 < CB → 0 < KA →
      ∃ N₀ : ℕ, 16*(r+1) ≤ N₀ ∧ ∀ (i : Fin d) (n : ℕ), N₀ ≤ n →
      ∀ q : unitInterval, Lambda ≤ (q : ℝ)*(n : ℝ)^2 →
      ∀ (cand : Finset (Finset (Vertex d))) (tgt : Finset (Vertex d) → Finset (Vertex d))
        (H₁ H₃ F₁ F₃ boundary₁ boundary₃ A : Finset (Vertex d)),
      H₁ ⊆ section9FiniteEndCube i n 0 → H₃ ⊆ section9FiniteEndCube i n (2*(n : ℝ)) →
      percolation d (criticalPoint d) (section9RevealEvent
        (section9FiniteEndCube i n 0) H₁ (section9FiniteEndCube i n (2*(n : ℝ))) H₃ F₁ F₃) ≠ 0 →
      (∀ x ∈ A, x ∈ section8ExtensionPositiveFaceCore i n) →
      (∀ x ∈ A, sourceRegularPoint F₁ (section8ExtensionSmallCube i n) boundary₁ r δ x) →
      (∀ y ∈ cand.biUnion tgt, y ∈ section8ExtensionNegativeFaceCore i n) →
      (∀ y ∈ cand.biUnion tgt, sourceRegularPoint F₃ ((section8ExtensionSmallCube i n).image
        (affineReflection (Pi.single i (2*(n : ℤ))))) boundary₃ r δ y) →
      Set.PairwiseDisjoint (cand : Set (Finset (Vertex d))) tgt →
      (A.card : ℝ) ≤ KA*(n : ℝ)^2 →
      (∀ c ∈ cand, ((tgt c).card : ℝ) ≤ CB*(n : ℝ)^2) →
      cSize*(n : ℝ)^2 ≤ (A.card : ℝ) → cSize*(n : ℝ)^2 ≤ ((cand.biUnion tgt).card : ℝ) →
      cSize*(n : ℝ)^((d : ℝ)-2) ≤ (A.card : ℝ)*((cand.biUnion tgt).card : ℝ) →
      ∀ N : ℕ, N ≤ m + 1 →
      ((percolation d (criticalPoint d)).prod (percolation d q)).real
        {z : Configuration d × Configuration d |
          ¬ N ≤ (sprinklingOffspring
            (stepView (section9FiniteMiddle i n) (section9FiniteTube i n (-(5 : ℝ)/8) (3/8))
              (section9FiniteTube i n (-(3 : ℝ)/8) (5/8)) (section9FiniteEndCube i n 0) F₁
              (section9FiniteEndCube i n (2*(n : ℝ))) F₃ z).1
            (stepView (section9FiniteMiddle i n) (section9FiniteTube i n (-(5 : ℝ)/8) (3/8))
              (section9FiniteTube i n (-(3 : ℝ)/8) (5/8)) (section9FiniteEndCube i n 0) F₁
              (section9FiniteEndCube i n (2*(n : ℝ))) F₃ z).2.1 A cand tgt
            ((stepView (section9FiniteMiddle i n) (section9FiniteTube i n (-(5 : ℝ)/8) (3/8))
              (section9FiniteTube i n (-(3 : ℝ)/8) (5/8)) (section9FiniteEndCube i n 0) F₁
              (section9FiniteEndCube i n (2*(n : ℝ))) F₃ z).2.2.1 A
              (sprinklingTargetBoundary cand tgt))).card} ≤ ε := by
  obtain ⟨δ, hδ, hmain⟩ :=
    section9_source_many_opened_pivotal_targets.{0} hd asymptotics rectangle reimer
  refine ⟨δ, hδ, ?_⟩
  intro r hr ε hε
  obtain ⟨cSize, hSize, hm⟩ := hmain r hr ε hε
  refine ⟨cSize, hSize, ?_⟩
  intro m
  obtain ⟨Lambda, hLambda, hCB⟩ := hm m
  refine ⟨Lambda, hLambda, ?_⟩
  intro CB KA hCBpos hKApos
  obtain ⟨N₀, hN₀, hrest⟩ := hCB CB KA hCBpos hKApos
  refine ⟨N₀, hN₀, ?_⟩
  intro i n hn q hq cand tgt H₁ H₃ F₁ F₃ boundary₁ boundary₃ A hH₁ hH₃ hpos hAcore hAreg hBcore
    hBreg hpd hAup hTup hAlo hBlo hAB N hN
  have hopen := hrest i n hn q hq cand tgt H₁ H₃ F₁ F₃ boundary₁ boundary₃ A hH₁ hH₃ hpos
    hAcore hAreg hBcore hBreg hpd hAup hTup hAlo hBlo hAB
  have hMR : section9FiniteMiddle i n ⊆ section9FiniteTube i n (-(3 : ℝ)/8) (5/8) := by
    rw [section9FiniteMiddle_eq_inter]
    exact Finset.inter_subset_right
  have hML : section9FiniteMiddle i n ⊆ section9FiniteTube i n (-(5 : ℝ)/8) (3/8) := by
    rw [section9FiniteMiddle_eq_inter]
    exact Finset.inter_subset_left
  have htrans := openedTargets_prod_eq (criticalPoint d) q (section9FiniteMiddle i n)
    (section9FiniteTube i n (-(5 : ℝ)/8) (3/8)) (section9FiniteTube i n (-(3 : ℝ)/8) (5/8))
    (section9FiniteEndCube i n 0) H₁ (section9FiniteEndCube i n (2*(n : ℝ))) H₃ F₁ F₃
    hH₁ hH₃ hpos (origin_L_disjoint_far i) (origin_R_disjoint_near i)
    (Finset.disjoint_of_subset_left hMR (origin_R_disjoint_near i))
    (Finset.disjoint_of_subset_left hML (origin_L_disjoint_far i)) cand tgt A m
  have hopen' : 1 - ε ≤ ((percolation d (criticalPoint d)).prod (percolation d q)).real
      {z : Configuration d × Configuration d | (m : ℝ) < ((cand.filter fun c =>
        (sprinkledPivotalPairs z.1 (sprinkleOrConfiguration z.1 z.2)
          (orientedLatticePairs (section9FiniteMiddle i n))
          (section9FiniteTube i n (-(5 : ℝ)/8) (3/8)) (section9FiniteTube i n (-(3 : ℝ)/8) (5/8))
          (section9FiniteEndCube i n 0) F₁ (section9FiniteEndCube i n (2*(n : ℝ))) F₃ A
          (tgt c)).Nonempty).card : ℝ)} := by
    rw [← htrans]
    exact hopen
  exact offspringFailure_le (criticalPoint d) q _ _ _ _ _ _ _ A cand tgt N m hN hopen'

end NearCritical.Section10
