module

public import NearCritical.Section10TranslatedOffspring
public import NearCritical.Section10StepPullback

/-! The offspring bound of `prop.proba.k-nest` for the actual layout.

`actualLayout_offspring_failure`: with the constants and quantifier order of
the Section 9 theorem, for a label with a tube of the actual layout and a
REALISED reveal `G = refineReveal rho₀ S₀ z`, under `P_{p_c} x P_q`:

  `P[ fewer than N offspring ] <= eps`   (`N <= m + 1`),

given the numeric size conditions on the source boundary `A` and the target
boundary `B` at scale `t`, `regularRadius = r` and `regularTolerance <= delta`.
All geometric and regularity hypotheses of the Section 9 theorem are
discharged here. Cited inputs: assumption (A), the restricted rectangle lower
bound, Reimer's inequality; also `0 < p_c < 1`.
-/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open MeasureTheory
open scoped Classical

theorem actualLayout_offspring_failure {D : ℕ} (hd : 9 ≤ D + 1)
    (asymptotics : TwoPointAsymptotics (D + 1))
    (rectangle : RestrictedRectangleLowerInput (D + 1)) (reimer : FiniteBernoulliBKRInput)
    (hp0 : 0 < (criticalPoint (D + 1) : ℝ)) (hp1 : (criticalPoint (D + 1) : ℝ) < 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ r : ℕ, 1 ≤ r → ∀ ε : ℝ, 0 < ε →
      ∃ cSize : ℝ, 0 < cSize ∧ ∀ m : ℕ, ∃ Lambda : ℝ, 0 < Lambda ∧
      ∀ CB KA : ℝ, 0 < CB → 0 < KA →
      ∃ N₀ : ℕ, 16*(r+1) ≤ N₀ ∧
      ∀ (typ : TypicalParameters) (t : ℕ) (ht : 9 ≤ t), N₀ ≤ t →
      typ.regularRadius = r → typ.regularTolerance ≤ δ →
      ∀ q : unitInterval, Lambda ≤ (q : ℝ)*(t : ℝ)^2 →
      ∀ (k : ℕ) (hk : 0 < k) (MOff Mcoal Kdiam M : ℕ) (Λ : NestLayout D (D + 1))
        (hΛ : Λ = actualLayout D typ t ht k hk MOff Mcoal Kdiam M)
        (z : Configuration (D + 1) × Configuration (D + 1)) (ℓ : RouteLabel D)
        (hℓ : HasTube M ℓ) (hsite : ℓ.site ∈ Λ.siteBox) (htarget : ℓ.target ∈ Λ.siteBox)
        (x : Λ.X),
      ((sprinklingTargetBoundary x.1.val
          (Λ.src (refineReveal Λ.ρ₀ Λ.S₀ z) ℓ x.2)).card : ℝ) ≤ KA*(t : ℝ)^2 →
      (∀ c ∈ Λ.fam (refineReveal Λ.ρ₀ Λ.S₀ z) ℓ.target,
        ((Λ.tgt (refineReveal Λ.ρ₀ Λ.S₀ z) ℓ c).card : ℝ) ≤ CB*(t : ℝ)^2) →
      cSize*(t : ℝ)^2 ≤ ((sprinklingTargetBoundary x.1.val
          (Λ.src (refineReveal Λ.ρ₀ Λ.S₀ z) ℓ x.2)).card : ℝ) →
      cSize*(t : ℝ)^2 ≤ ((sprinklingTargetBoundary
          (Λ.fam (refineReveal Λ.ρ₀ Λ.S₀ z) ℓ.target)
          (Λ.tgt (refineReveal Λ.ρ₀ Λ.S₀ z) ℓ)).card : ℝ) →
      cSize*(t : ℝ)^((((D + 1 : ℕ) : ℝ))-2) ≤
        ((sprinklingTargetBoundary x.1.val
          (Λ.src (refineReveal Λ.ρ₀ Λ.S₀ z) ℓ x.2)).card : ℝ) *
        ((sprinklingTargetBoundary (Λ.fam (refineReveal Λ.ρ₀ Λ.S₀ z) ℓ.target)
          (Λ.tgt (refineReveal Λ.ρ₀ Λ.S₀ z) ℓ)).card : ℝ) →
      ∀ N : ℕ, N ≤ m + 1 →
      ((percolation (D + 1) (criticalPoint (D + 1))).prod (percolation (D + 1) q)).real
        {z' | ¬ N ≤ (sprinklingOffspring
          (Λ.view (refineReveal Λ.ρ₀ Λ.S₀ z).1 ℓ z').1.1
          (Λ.view (refineReveal Λ.ρ₀ Λ.S₀ z).1 ℓ z').1.2.1
          (sprinklingTargetBoundary x.1.val (Λ.src (refineReveal Λ.ρ₀ Λ.S₀ z) ℓ x.2))
          (Λ.fam (refineReveal Λ.ρ₀ Λ.S₀ z) ℓ.target) (Λ.tgt (refineReveal Λ.ρ₀ Λ.S₀ z) ℓ)
          (svPivots (Λ.view (refineReveal Λ.ρ₀ Λ.S₀ z).1 ℓ z').1 x.1.val
            (Λ.fam (refineReveal Λ.ρ₀ Λ.S₀ z) ℓ.target)
            (Λ.src (refineReveal Λ.ρ₀ Λ.S₀ z) ℓ x.2)
            (Λ.tgt (refineReveal Λ.ρ₀ Λ.S₀ z) ℓ))).card} ≤ ε := by
  obtain ⟨δ, hδ, hmain⟩ :=
    translated_offspring_failure_of_section9 hd asymptotics rectangle reimer
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
  intro typ t ht hNt hrad htol q hq k hk MOff Mcoal Kdiam M Λ hΛ z ℓ hℓ hsite htarget x
    hAup hTup hAlo hBlo hAB N hN
  subst hΛ
  have ht0 : 0 < t := by omega
  have hH₁ : typicalHeart t (0 : Vertex (D + 1)) typ.heartRatio ⊆
      section9FiniteEndCube (dirOf ℓ) t 0 := by
    rw [← typicalCube_zero_eq_endCube ht0 (dirOf ℓ)]
    exact Finset.filter_subset _ _
  have hH₃ : typicalHeart t (farCenter t (0 : Vertex (D + 1)) (dirOf ℓ)) typ.heartRatio ⊆
      section9FiniteEndCube (dirOf ℓ) t (2 * (t : ℝ)) := by
    rw [← typicalCube_far_eq_endCube ht0 (dirOf ℓ)]
    exact Finset.filter_subset _ _
  have hcsite : siteCenter t ℓ.site = siteCenter t ℓ.site + (0 : Vertex (D + 1)) :=
    (add_zero _).symm
  have hctarget : siteCenter t ℓ.target =
      siteCenter t ℓ.site + farCenter t (0 : Vertex (D + 1)) (dirOf ℓ) := by
    rw [siteCenter_target t hℓ, farCenter_eq_add]
  have hHh₁ : translateSites (siteCenter t ℓ.site)
      (typicalHeart t (0 : Vertex (D + 1)) typ.heartRatio) =
      (actualLayout D typ t ht k hk MOff Mcoal Kdiam M).Hh ℓ.site := by
    show _ = typicalHeart t (siteCenter t ℓ.site) typ.heartRatio
    have h := typicalHeart_translate t (siteCenter t ℓ.site) (0 : Vertex (D + 1)) typ.heartRatio
    rw [add_zero] at h
    exact h.symm
  have hHh₃ : translateSites (siteCenter t ℓ.site)
      (typicalHeart t (farCenter t (0 : Vertex (D + 1)) (dirOf ℓ)) typ.heartRatio) =
      (actualLayout D typ t ht k hk MOff Mcoal Kdiam M).Hh ℓ.target := by
    show _ = typicalHeart t (siteCenter t ℓ.target) typ.heartRatio
    rw [hctarget, typicalHeart_translate]
  have hpos : percolation (D + 1) (criticalPoint (D + 1)) (section9RevealEvent
      (section9FiniteEndCube (dirOf ℓ) t 0)
      (typicalHeart t (0 : Vertex (D + 1)) typ.heartRatio)
      (section9FiniteEndCube (dirOf ℓ) t (2 * (t : ℝ)))
      (typicalHeart t (farCenter t (0 : Vertex (D + 1)) (dirOf ℓ)) typ.heartRatio)
      (translateSites (-(siteCenter t ℓ.site))
        ((actualLayout D typ t ht k hk MOff Mcoal Kdiam M).Fat
          ((actualLayout D typ t ht k hk MOff Mcoal Kdiam M).ρ₀ z) ℓ.site))
      (translateSites (-(siteCenter t ℓ.site))
        ((actualLayout D typ t ht k hk MOff Mcoal Kdiam M).Fat
          ((actualLayout D typ t ht k hk MOff Mcoal Kdiam M).ρ₀ z) ℓ.target))) ≠ 0 := by
    have hact := (actualLayout D typ t ht k hk MOff Mcoal Kdiam M).stepReveal_ne_zero
      (criticalPoint (D + 1)) hp0 hp1 z hsite htarget
    have htr := revealEvent_translate_measure (criticalPoint (D + 1)) (siteCenter t ℓ.site)
      (section9FiniteEndCube (dirOf ℓ) t 0)
      (typicalHeart t (0 : Vertex (D + 1)) typ.heartRatio)
      (section9FiniteEndCube (dirOf ℓ) t (2 * (t : ℝ)))
      (typicalHeart t (farCenter t (0 : Vertex (D + 1)) (dirOf ℓ)) typ.heartRatio)
      (translateSites (-(siteCenter t ℓ.site))
        ((actualLayout D typ t ht k hk MOff Mcoal Kdiam M).Fat
          ((actualLayout D typ t ht k hk MOff Mcoal Kdiam M).ρ₀ z) ℓ.site))
      (translateSites (-(siteCenter t ℓ.site))
        ((actualLayout D typ t ht k hk MOff Mcoal Kdiam M).Fat
          ((actualLayout D typ t ht k hk MOff Mcoal Kdiam M).ρ₀ z) ℓ.target)) hH₁ hH₃
    rw [translateSites_add_neg_cancel, translateSites_add_neg_cancel, hHh₁, hHh₃,
      ← actual_Qsite_eq typ t ht k hk MOff Mcoal Kdiam M ℓ,
      ← actual_Qtarget_eq typ t ht k hk MOff Mcoal Kdiam M hℓ] at htr
    rw [← htr]
    exact hact
  have hAreg : ∀ x' ∈ translateSites (-(siteCenter t ℓ.site))
      (sprinklingTargetBoundary x.1.val
        ((actualLayout D typ t ht k hk MOff Mcoal Kdiam M).src
          (refineReveal (actualLayout D typ t ht k hk MOff Mcoal Kdiam M).ρ₀
            (actualLayout D typ t ht k hk MOff Mcoal Kdiam M).S₀ z) ℓ x.2)),
      sourceRegularPoint (translateSites (-(siteCenter t ℓ.site))
        ((actualLayout D typ t ht k hk MOff Mcoal Kdiam M).Fat
          ((actualLayout D typ t ht k hk MOff Mcoal Kdiam M).ρ₀ z) ℓ.site))
        (section8ExtensionSmallCube (dirOf ℓ) t) (typicalBoundary t (0 : Vertex (D + 1))) r δ
        x' := by
    intro x' hx'
    obtain ⟨y, hy, rfl⟩ := (mem_translateSites_iff _ _ x').mp hx'
    unfold sprinklingTargetBoundary at hy
    obtain ⟨C, _, hyC⟩ := Finset.mem_biUnion.mp hy
    have h := (actualLayout D typ t ht k hk MOff Mcoal Kdiam M).patch_pullback_regular z hsite
      (siteCenter t ℓ.site) 0 hcsite C (dirOf ℓ, true) x.2 _
      ((mem_translateSites _ _ y).mpr hyC)
    rw [← typicalInnerCube_zero_eq_smallCube ht0 (dirOf ℓ), ← hrad]
    exact sourceRegularPoint_mono htol h
  have hBreg : ∀ y ∈ ((actualLayout D typ t ht k hk MOff Mcoal Kdiam M).fam
        (refineReveal (actualLayout D typ t ht k hk MOff Mcoal Kdiam M).ρ₀
          (actualLayout D typ t ht k hk MOff Mcoal Kdiam M).S₀ z) ℓ.target).biUnion
        (fun c => translateSites (-(siteCenter t ℓ.site))
          ((actualLayout D typ t ht k hk MOff Mcoal Kdiam M).tgt
            (refineReveal (actualLayout D typ t ht k hk MOff Mcoal Kdiam M).ρ₀
              (actualLayout D typ t ht k hk MOff Mcoal Kdiam M).S₀ z) ℓ c)),
      sourceRegularPoint (translateSites (-(siteCenter t ℓ.site))
        ((actualLayout D typ t ht k hk MOff Mcoal Kdiam M).Fat
          ((actualLayout D typ t ht k hk MOff Mcoal Kdiam M).ρ₀ z) ℓ.target))
        ((section8ExtensionSmallCube (dirOf ℓ) t).image
          (affineReflection (Pi.single (dirOf ℓ) (2 * (t : ℤ)))))
        (typicalBoundary t (farCenter t (0 : Vertex (D + 1)) (dirOf ℓ))) r δ y := by
    intro y hy
    obtain ⟨c, _, hyc⟩ := Finset.mem_biUnion.mp hy
    obtain ⟨w, hw, rfl⟩ := (mem_translateSites_iff _ _ y).mp hyc
    rw [← typicalInnerCube_far_eq_reflected ht0 (dirOf ℓ), ← hrad]
    rcases Finset.mem_union.mp hw with hw1 | hw1
    · exact sourceRegularPoint_mono htol
        ((actualLayout D typ t ht k hk MOff Mcoal Kdiam M).patch_pullback_regular z htarget
          (siteCenter t ℓ.site) _ hctarget c (dirOf ℓ, false) true _
          ((mem_translateSites _ _ w).mpr hw1))
    · exact sourceRegularPoint_mono htol
        ((actualLayout D typ t ht k hk MOff Mcoal Kdiam M).patch_pullback_regular z htarget
          (siteCenter t ℓ.site) _ hctarget c (dirOf ℓ, false) false _
          ((mem_translateSites _ _ w).mpr hw1))
  have hBcore : ∀ y ∈ ((actualLayout D typ t ht k hk MOff Mcoal Kdiam M).fam
        (refineReveal (actualLayout D typ t ht k hk MOff Mcoal Kdiam M).ρ₀
          (actualLayout D typ t ht k hk MOff Mcoal Kdiam M).S₀ z) ℓ.target).biUnion
        (fun c => translateSites (-(siteCenter t ℓ.site))
          ((actualLayout D typ t ht k hk MOff Mcoal Kdiam M).tgt
            (refineReveal (actualLayout D typ t ht k hk MOff Mcoal Kdiam M).ρ₀
              (actualLayout D typ t ht k hk MOff Mcoal Kdiam M).S₀ z) ℓ c)),
      y ∈ section8ExtensionNegativeFaceCore (dirOf ℓ) t := by
    intro y hy
    obtain ⟨c, _, hyc⟩ := Finset.mem_biUnion.mp hy
    exact actual_tgt_pullback_core typ t ht k hk MOff Mcoal Kdiam M _ hℓ c y hyc
  have h := hrest (dirOf ℓ) t hNt q hq (siteCenter t ℓ.site) _ _ _ _ _ _
    (typicalBoundary t (0 : Vertex (D + 1)))
    (typicalBoundary t (farCenter t (0 : Vertex (D + 1)) (dirOf ℓ))) _ hH₁ hH₃ hpos
    (actual_src_pullback_core typ t ht k hk MOff Mcoal Kdiam M _ ℓ x.2 x.1.val) hAreg hBcore hBreg
    (pairwiseDisjoint_pullback _ _ _
      ((actualLayout D typ t ht k hk MOff Mcoal Kdiam M).tgt_pairwiseDisjoint _ ℓ))
    (by rw [card_pullback]; exact hAup)
    (fun c hc => by rw [card_pullback]; exact hTup c hc)
    (by rw [card_pullback]; exact hAlo)
    (by rw [biUnion_pullback, card_pullback]; exact hBlo)
    (by rw [biUnion_pullback, card_pullback, card_pullback]; exact hAB) N hN
  rw [translateSites_add_neg_cancel, translateSites_add_neg_cancel, translateSites_add_neg_cancel,
    ← actual_Mid_eq typ t ht k hk MOff Mcoal Kdiam M hℓ,
    ← actual_L_eq typ t ht k hk MOff Mcoal Kdiam M hℓ,
    ← actual_R_eq typ t ht k hk MOff Mcoal Kdiam M hℓ,
    ← actual_Qsite_eq typ t ht k hk MOff Mcoal Kdiam M ℓ,
    ← actual_Qtarget_eq typ t ht k hk MOff Mcoal Kdiam M hℓ] at h
  exact h

end NearCritical.Section10
