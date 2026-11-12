module

public import NearCritical.Section10StepOffspring

/-! The offspring lower bound of `prop.sprinkling.AB.disjoint` under the
product law, for a step translated by an arbitrary vector `a`.

`translated_offspring_failure_of_section9`: same constants and quantifier order
as `section9_source_many_opened_pivotal_targets`. The hypotheses are on the
ORIGIN data (revealed sets `F₁, F₃`, source set `A`, and the pulled-back target
patches `translateSites (-a) (tgt c)`); the conclusion is the offspring failure
bound for the step whose tubes, cubes, revealed sets and source set are the
translates by `a`, with the actual candidates and target patches. It is in the
`stepView` form consumed by `NestLayout.moveSuccess_ge`.
-/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open MeasureTheory
open scoped Classical

theorem translated_offspring_failure_of_section9 {d : ℕ} (hd : 9 ≤ d)
    (asymptotics : TwoPointAsymptotics d) (rectangle : RestrictedRectangleLowerInput d)
    (reimer : FiniteBernoulliBKRInput) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ r : ℕ, 1 ≤ r → ∀ ε : ℝ, 0 < ε →
      ∃ cSize : ℝ, 0 < cSize ∧ ∀ m : ℕ, ∃ Lambda : ℝ, 0 < Lambda ∧
      ∀ CB KA : ℝ, 0 < CB → 0 < KA →
      ∃ N₀ : ℕ, 16*(r+1) ≤ N₀ ∧ ∀ (i : Fin d) (n : ℕ), N₀ ≤ n →
      ∀ q : unitInterval, Lambda ≤ (q : ℝ)*(n : ℝ)^2 →
      ∀ (a : Vertex d) (cand : Finset (Finset (Vertex d)))
        (tgt : Finset (Vertex d) → Finset (Vertex d))
        (H₁ H₃ F₁ F₃ boundary₁ boundary₃ A : Finset (Vertex d)),
      H₁ ⊆ section9FiniteEndCube i n 0 → H₃ ⊆ section9FiniteEndCube i n (2*(n : ℝ)) →
      percolation d (criticalPoint d) (section9RevealEvent
        (section9FiniteEndCube i n 0) H₁ (section9FiniteEndCube i n (2*(n : ℝ))) H₃ F₁ F₃) ≠ 0 →
      (∀ x ∈ A, x ∈ section8ExtensionPositiveFaceCore i n) →
      (∀ x ∈ A, sourceRegularPoint F₁ (section8ExtensionSmallCube i n) boundary₁ r δ x) →
      (∀ y ∈ cand.biUnion (fun c => translateSites (-a) (tgt c)),
        y ∈ section8ExtensionNegativeFaceCore i n) →
      (∀ y ∈ cand.biUnion (fun c => translateSites (-a) (tgt c)),
        sourceRegularPoint F₃ ((section8ExtensionSmallCube i n).image
          (affineReflection (Pi.single i (2*(n : ℤ))))) boundary₃ r δ y) →
      Set.PairwiseDisjoint (cand : Set (Finset (Vertex d)))
        (fun c => translateSites (-a) (tgt c)) →
      (A.card : ℝ) ≤ KA*(n : ℝ)^2 →
      (∀ c ∈ cand, ((translateSites (-a) (tgt c)).card : ℝ) ≤ CB*(n : ℝ)^2) →
      cSize*(n : ℝ)^2 ≤ (A.card : ℝ) →
      cSize*(n : ℝ)^2 ≤ ((cand.biUnion (fun c => translateSites (-a) (tgt c))).card : ℝ) →
      cSize*(n : ℝ)^((d : ℝ)-2) ≤
        (A.card : ℝ)*((cand.biUnion (fun c => translateSites (-a) (tgt c))).card : ℝ) →
      ∀ N : ℕ, N ≤ m + 1 →
      ((percolation d (criticalPoint d)).prod (percolation d q)).real
        {z : Configuration d × Configuration d |
          ¬ N ≤ (sprinklingOffspring
            (stepView (translateSites a (section9FiniteMiddle i n))
              (translateSites a (section9FiniteTube i n (-(5 : ℝ)/8) (3/8)))
              (translateSites a (section9FiniteTube i n (-(3 : ℝ)/8) (5/8)))
              (translateSites a (section9FiniteEndCube i n 0)) (translateSites a F₁)
              (translateSites a (section9FiniteEndCube i n (2*(n : ℝ))))
              (translateSites a F₃) z).1
            (stepView (translateSites a (section9FiniteMiddle i n))
              (translateSites a (section9FiniteTube i n (-(5 : ℝ)/8) (3/8)))
              (translateSites a (section9FiniteTube i n (-(3 : ℝ)/8) (5/8)))
              (translateSites a (section9FiniteEndCube i n 0)) (translateSites a F₁)
              (translateSites a (section9FiniteEndCube i n (2*(n : ℝ))))
              (translateSites a F₃) z).2.1 (translateSites a A) cand tgt
            ((stepView (translateSites a (section9FiniteMiddle i n))
              (translateSites a (section9FiniteTube i n (-(5 : ℝ)/8) (3/8)))
              (translateSites a (section9FiniteTube i n (-(3 : ℝ)/8) (5/8)))
              (translateSites a (section9FiniteEndCube i n 0)) (translateSites a F₁)
              (translateSites a (section9FiniteEndCube i n (2*(n : ℝ))))
              (translateSites a F₃) z).2.2.1 (translateSites a A)
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
  intro i n hn q hq a cand tgt H₁ H₃ F₁ F₃ boundary₁ boundary₃ A hH₁ hH₃ hpos hAcore hAreg hBcore
    hBreg hpd hAup hTup hAlo hBlo hAB N hN
  have hopen := hrest i n hn q hq cand (fun c => translateSites (-a) (tgt c)) H₁ H₃ F₁ F₃
    boundary₁ boundary₃ A hH₁ hH₃ hpos hAcore hAreg hBcore hBreg hpd hAup hTup hAlo hBlo hAB
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
    (Finset.disjoint_of_subset_left hML (origin_L_disjoint_far i)) cand
    (fun c => translateSites (-a) (tgt c)) A m
  refine translated_offspring_failure_le (criticalPoint d) q a _ _ _ _ _ _ _ A cand tgt N m hN ?_
  rw [← htrans]
  exact hopen

end NearCritical.Section10
