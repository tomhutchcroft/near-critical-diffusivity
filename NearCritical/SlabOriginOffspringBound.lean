module

public import NearCritical.SlabChartOffspring
public import NearCritical.Section10OriginOffspring

/-! The quantitative Section 9 offspring estimate for the actual slab edge
block and either orientation, with the boundary data in parent coordinates. -/
@[expose] public section
noncomputable section

namespace NearCritical

open MeasureTheory Section10
open scoped Classical

theorem slab_origin_offspring_failure_le {d : ℕ} (hd : 9 ≤ d)
    (asymptotics : TwoPointAsymptotics d) (rectangle : RestrictedRectangleLowerInput d)
    (reimer : FiniteBernoulliBKRInput) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ r : ℕ, 1 ≤ r → ∀ ε : ℝ, 0 < ε →
      ∃ cSize : ℝ, 0 < cSize ∧ ∀ m : ℕ, ∃ Lambda : ℝ, 0 < Lambda ∧
      ∀ CB KA : ℝ, 0 < CB → 0 < KA →
      ∃ N₀ : ℕ, 16*(r+1) ≤ N₀ ∧ ∀ (n : ℕ), N₀ ≤ n →
      ∀ q : unitInterval, Lambda ≤ (q : ℝ)*(n : ℝ)^2 →
      ∀ (R : ℕ) (A : Finset (Bond d)) (e : boxBonds (centeredBox 2 R)) (rev : Bool),
      (∀ b, bondIn (slabTube n e.1.1 e.1.2) b → b ∈ A) →
      let i := Fin.castLE (show 2 ≤ d by omega) e.1.2
      ∀ (cand : Finset (Finset (Vertex d))) (tgt : Finset (Vertex d) → Finset (Vertex d))
        (H₁ H₃ F₁ F₃ boundary₁ boundary₃ S : Finset (Vertex d)),
      H₁ ⊆ section9FiniteEndCube i n 0 → H₃ ⊆ section9FiniteEndCube i n (2*(n : ℝ)) →
      percolation d (criticalPoint d) (section9RevealEvent
        (section9FiniteEndCube i n 0) H₁ (section9FiniteEndCube i n (2*(n : ℝ))) H₃ F₁ F₃) ≠ 0 →
      (∀ x ∈ S, x ∈ section8ExtensionPositiveFaceCore i n) →
      (∀ x ∈ S, sourceRegularPoint F₁ (section8ExtensionSmallCube i n) boundary₁ r δ x) →
      (∀ y ∈ cand.biUnion tgt, y ∈ section8ExtensionNegativeFaceCore i n) →
      (∀ y ∈ cand.biUnion tgt, sourceRegularPoint F₃ ((section8ExtensionSmallCube i n).image
        (affineReflection (Pi.single i (2*(n : ℤ))))) boundary₃ r δ y) →
      Set.PairwiseDisjoint (cand : Set (Finset (Vertex d))) tgt →
      (S.card : ℝ) ≤ KA*(n : ℝ)^2 →
      (∀ c ∈ cand, ((tgt c).card : ℝ) ≤ CB*(n : ℝ)^2) →
      cSize*(n : ℝ)^2 ≤ (S.card : ℝ) → cSize*(n : ℝ)^2 ≤ ((cand.biUnion tgt).card : ℝ) →
      cSize*(n : ℝ)^((d : ℝ)-2) ≤ (S.card : ℝ)*((cand.biUnion tgt).card : ℝ) →
      ∀ N : ℕ, N ≤ m + 1 →
      (rsν d n A R (criticalPoint d) q (Sum.inr e)).real
        {y | ¬ N ≤ (slabStepOffspring (section9FiniteMiddle i n)
          (section9FiniteTube i n (-(5:ℝ)/8) (3/8))
          (section9FiniteTube i n (-(3:ℝ)/8) (5/8))
          (section9FiniteEndCube i n 0) F₁ (section9FiniteEndCube i n (2*(n : ℝ))) F₃ S cand tgt
          (pullbackLayerPair (slabChartBond (show 2 ≤ d by omega) n e.1 rev)
            (slabTubePair n A R e y))).card} ≤ ε := by
  obtain ⟨δ, hδ, hmain⟩ := origin_offspring_failure_le hd asymptotics rectangle reimer
  refine ⟨δ, hδ, ?_⟩
  intro r hr ε hε
  obtain ⟨cSize, hcSize, hm⟩ := hmain r hr ε hε
  refine ⟨cSize, hcSize, ?_⟩
  intro m
  obtain ⟨Lambda, hLambda, hCB⟩ := hm m
  refine ⟨Lambda, hLambda, ?_⟩
  intro CB KA hCBpos hKApos
  obtain ⟨N₀, hN₀, hrest⟩ := hCB CB KA hCBpos hKApos
  refine ⟨N₀, hN₀, ?_⟩
  intro n hn q hq R A e rev hA i cand tgt H₁ H₃ F₁ F₃ boundary₁ boundary₃ S
    hH₁ hH₃ hpos hScore hSreg hBcore hBreg hpd hSup hTup hSlo hBlo hSB N hN
  have hn0 : 0 < n := by omega
  rw [slab_chart_offspring_failure_eq (show 2 ≤ d by omega) hn0 R A e rev (criticalPoint d) q
    (section9FiniteEndCube i n 0) F₁ (section9FiniteEndCube i n (2*(n : ℝ))) F₃ S cand tgt N hA]
  exact hrest i n hn q hq cand tgt H₁ H₃ F₁ F₃ boundary₁ boundary₃ S
    hH₁ hH₃ hpos hScore hSreg hBcore hBreg hpd hSup hTup hSlo hBlo hSB N hN

end NearCritical
