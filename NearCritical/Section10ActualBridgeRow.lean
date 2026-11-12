module

public import NearCritical.Section10ActualOppositeBridges

/-! The distinct-root row of H3 on a physical tube of the actual layout. -/

@[expose] public section
noncomputable section

namespace NearCritical.Section10

open MeasureTheory Set
open scoped Classical

/-- Summing over all other typical source clusters has uniformly bounded
bridge-intersection probability, on the fresh product law of an actual tube. -/
theorem actualLayout_bridge_row_uniform {D : ℕ} [LinearOrder (Finset (Vertex (D + 1)))]
    (hd : 7 ≤ D + 1) (asymp : TwoPointAsymptotics (D + 1)) (q₀ : ℝ)
    (hp0 : 0 < (criticalPoint (D + 1) : ℝ)) (hp1 : (criticalPoint (D + 1) : ℝ) < 1)
    (typ : TypicalParameters) (hr : 1 ≤ typ.regularRadius) (hb : 0 ≤ typ.boundaryUpper) :
    ∃ K : ℝ, ∀ (t : ℕ) (ht : 9 ≤ t) (k : ℕ) (hk : 0 < k) (MOff Mcoal Kdiam M : ℕ),
      let Λ := actualLayout D typ t ht k hk MOff Mcoal Kdiam M
      ∀ (z : Configuration (D + 1) × Configuration (D + 1)) (ℓ : RouteLabel D),
      let G := refineReveal Λ.ρ₀ Λ.S₀ z
      HasTube M ℓ → ℓ.isStep → ℓ.site ∈ Λ.siteBox → ℓ.target ∈ Λ.siteBox →
      Λ.goodCube G ℓ.site → Λ.goodCube G ℓ.target →
      ∀ (q : unitInterval), (q : ℝ) ≤ q₀ * (t : ℝ)^(-2 : ℝ) →
      ∀ (C : Finset (Vertex (D + 1))), C ∈ Λ.fam G ℓ.site → ∀ a b : Bool,
      let μ := (percolation (D + 1) (criticalPoint (D + 1))).prod (percolation (D + 1) q)
      (∑ E ∈ (Λ.fam G ℓ.site).erase C,
        μ.real {w | Λ.firstGoodSharedTubeMark G ℓ {C} {E} a b w}) ≤ K := by
  let A₀ := 4 * typ.boundaryUpper
  let F₀ := (2:ℝ)^(D+1-6) * typ.countUpper * (8 * typ.boundaryUpper)
  obtain ⟨K, hK⟩ := bridge_intersection_probability_row_uniform
    (ι := Finset (Vertex (D + 1))) (by omega : 5 ≤ D+1) asymp q₀
      typ.regularRadius hr typ.regularTolerance A₀ F₀
  refine ⟨K, ?_⟩
  intro t ht k hk MOff Mcoal Kdiam M Λ z ℓ G hℓ hstep hsite htgt hgood hgood' q hq C hC a b
  let i := dirOf ℓ
  let c := siteCenter t ℓ.site
  let L := section9FiniteTube i t (-(5:ℝ)/8) (3/8)
  let R := section9FiniteTube i t (-(3:ℝ)/8) (5/8)
  let S := section9FiniteMiddle i t
  let Q₁ := section9FiniteEndCube i t 0
  let Q₃ := section9FiniteEndCube i t (2*(t:ℝ))
  let H₁ := typicalHeart t (0 : Vertex (D + 1)) typ.heartRatio
  let H₃ := typicalHeart t (farCenter t (0 : Vertex (D + 1)) i) typ.heartRatio
  let F₁ := translateSites (-c) (Λ.Fat G.1 ℓ.site)
  let F₃ := translateSites (-c) (Λ.Fat G.1 ℓ.target)
  let J := (Λ.fam G ℓ.site).erase C
  let X := translateSites (-c) (Λ.src G ℓ a C)
  let Y := fun E => translateSites (-c) (Λ.src G ℓ b E)
  let B := translateSites (-c) (sprinklingTargetBoundary (Λ.fam G ℓ.target) (Λ.tgt G ℓ))
  have ht0 : 0 < t := by omega
  have hQ₁ : Λ.Q ℓ.site = translateSites c Q₁ := actual_Qsite_eq typ t ht k hk MOff Mcoal Kdiam M ℓ
  have hQ₃ : Λ.Q ℓ.target = translateSites c Q₃ := actual_Qtarget_eq typ t ht k hk MOff Mcoal Kdiam M hℓ
  have hH₁ : H₁ ⊆ Q₁ := by
    dsimp only [H₁,Q₁]
    rw [← typicalCube_zero_eq_endCube ht0 i]
    exact Finset.filter_subset _ _
  have hH₃ : H₃ ⊆ Q₃ := by
    dsimp only [H₃,Q₃]
    rw [← typicalCube_far_eq_endCube ht0 i]
    exact Finset.filter_subset _ _
  have hHh₁ : translateSites c H₁ = Λ.Hh ℓ.site := by
    change translateSites c H₁ = typicalHeart t c typ.heartRatio
    have hh := typicalHeart_translate t c (0 : Vertex (D + 1)) typ.heartRatio
    rw [add_zero] at hh
    exact hh.symm
  have hHh₃ : translateSites c H₃ = Λ.Hh ℓ.target := by
    change translateSites c H₃ = typicalHeart t (siteCenter t ℓ.target) typ.heartRatio
    rw [siteCenter_target t hℓ, farCenter_eq_add, typicalHeart_translate]
  have hpos : percolation (D + 1) (criticalPoint (D + 1))
      (section9RevealEvent Q₁ H₁ Q₃ H₃ F₁ F₃) ≠ 0 := by
    rw [← revealEvent_translate_measure _ c _ _ _ _ _ _ hH₁ hH₃, ← hQ₁, ← hQ₃, hHh₁, hHh₃]
    dsimp only [F₁,F₃]
    rw [translateSites_add_neg_cancel, translateSites_add_neg_cancel]
    exact Λ.stepReveal_ne_zero _ hp0 hp1 z hsite htgt
  have hroot (P : Finset (Finset (Vertex (D + 1)))) (sign : Bool) :
      translateSites (-c) (sprinklingTargetBoundary P (Λ.src G ℓ sign)) ⊆ Q₁ := by
    have hsub : sprinklingTargetBoundary P (Λ.src G ℓ sign) ⊆ Λ.Q ℓ.site := by
      exact Finset.biUnion_subset.mpr fun C _ => typicalRegularPatch_subset_cube _ _ _ _ C _ _
    intro v hv
    rw [hQ₁] at hsub
    exact mem_translateSites_neg c Q₁ (translateSites_mono _ hsub hv)
  have hB : B ⊆ Q₃ := by
    have hsub : sprinklingTargetBoundary (Λ.fam G ℓ.target) (Λ.tgt G ℓ) ⊆ Λ.Q ℓ.target := by
      exact Finset.biUnion_subset.mpr fun C _ => Finset.union_subset
        (typicalRegularPatch_subset_cube _ _ _ _ C _ _) (typicalRegularPatch_subset_cube _ _ _ _ C _ _)
    intro v hv
    rw [hQ₃] at hsub
    exact mem_translateSites_neg c Q₃ (translateSites_mono _ hsub hv)
  have hJsub : J ⊆ Λ.fam G ℓ.site := Finset.erase_subset _ _
  have hdis : (J : Set (Finset (Vertex (D + 1)))).PairwiseDisjoint Y :=
    pairwiseDisjoint_pullback _ _ _ (Λ.src_pairwiseDisjoint G ℓ b J hJsub)
  have hJ : J.biUnion Y ⊆ Q₁ := by
    rw [show J.biUnion Y = translateSites (-c) (sprinklingTargetBoundary J (Λ.src G ℓ b))
      from biUnion_pullback _ _ _]
    exact hroot J b
  have hX : X ⊆ Q₁ := by
    simpa only [sprinklingTargetBoundary, Finset.singleton_biUnion] using hroot {C} a
  let U := typicalInnerCube t (0 : Vertex (D + 1))
  let V := typicalBoundary t (0 : Vertex (D + 1))
  have hreg (E : Finset (Vertex (D + 1))) (s : Bool) :
      ∀ v ∈ translateSites (-c) (Λ.src G ℓ s E),
        sourceRegularPoint F₁ U V typ.regularRadius typ.regularTolerance v := by
    exact Λ.patch_pullback_regular z hsite c 0 (add_zero c).symm E (Λ.dir ℓ,true) s
  have hJreg : ∀ y ∈ J.biUnion Y,
      sourceRegularPoint F₁ U V typ.regularRadius typ.regularTolerance y := by
    intro y hy
    obtain ⟨E, _, hyE⟩ := Finset.mem_biUnion.mp hy
    exact hreg E b y hyE
  have hXc : (X.card:ℝ) ≤ A₀ * (t:ℝ)^(2:ℝ) := by
    rw [show X.card = (Λ.src G ℓ a C).card from card_pullback _ _, Real.rpow_two]
    have htyp := ((mem_typicalClusterFamily _ _ _ _ C).mp hC).2
    refine (htyp.2.2.2.2.2.1 (Λ.dir ℓ,true) a).2.trans_eq ?_
    change typ.boundaryUpper * (2*(t:ℝ))^2 = A₀ * (t:ℝ)^2
    dsimp only [A₀]
    ring
  have hpow :
      (typ.countUpper * (2*(t:ℝ))^(D+1-6)) * (2 * (typ.boundaryUpper * (2*(t:ℝ))^2)) =
        F₀ * (t:ℝ)^(((D+1:ℕ):ℝ)-4) := by
    have he : ((D+1:ℕ):ℝ)-4 = ((D+1-4:ℕ):ℝ) := by
      rw [Nat.cast_sub (by omega)]
      norm_num
    rw [he, Real.rpow_natCast, show D+1-4 = (D+1-6)+2 by omega, pow_add, mul_pow]
    dsimp only [F₀]
    ring
  have hJc : ((J.biUnion Y).card:ℝ) ≤ F₀ * (t:ℝ)^(((D+1:ℕ):ℝ)-4) := by
    rw [show J.biUnion Y = translateSites (-c) (sprinklingTargetBoundary J (Λ.src G ℓ b))
      from biUnion_pullback _ _ _, card_pullback, ← hpow]
    have hcnt : ((Λ.fam G ℓ.site).card:ℝ) ≤ typ.countUpper * (2*(t:ℝ))^(D+1-6) := hgood.2
    have hJcnt : (J.card:ℝ) ≤ ((Λ.fam G ℓ.site).card:ℝ) := by
      exact_mod_cast Finset.card_le_card hJsub
    have hbd : 0 ≤ typ.boundaryUpper * (2*(t:ℝ))^2 := by positivity
    refine (Λ.srcBoundary_card_le G ℓ b J hJsub).trans ?_
    refine (mul_le_mul_of_nonneg_right (hJcnt.trans hcnt) hbd).trans ?_
    exact mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hbd (by norm_num))
      ((Nat.cast_nonneg _).trans hcnt)
  have hBc : (B.card:ℝ) ≤ F₀ * (t:ℝ)^(((D+1:ℕ):ℝ)-4) := by
    rw [show B.card = _ from card_pullback _ _, ← hpow]
    exact Λ.tgtBoundary_card_le G ℓ hgood' hb
  have hLQ : Disjoint L Q₃ := section9FiniteLeftTube_disjoint_third i ht0
  have hRQ : Disjoint R Q₁ := section9FiniteRightTube_disjoint_first i ht0
  have hS₃ : Disjoint S Q₃ := Finset.disjoint_of_subset_left (by
    dsimp only [S]
    rw [section9FiniteMiddle_eq_inter]
    exact Finset.inter_subset_left) hLQ
  have hfresh : Disjoint (clusterRevealBonds Q₁ F₁ ∪ clusterRevealBonds Q₃ F₃)
      ((sprinklingAvailableBonds L Q₁ F₁ ∪ sprinklingAvailableBonds R Q₃ F₃) ∪ internalBondSet S) := by
    refine Finset.disjoint_union_right.mpr ⟨sprinklingAvailableBonds_disjoint_reveals _ _ _ _ _ _ hLQ hRQ, ?_⟩
    apply Finset.disjoint_left.mpr
    intro e he hm
    have hm' := ((mem_internalBondSet S e).mp hm).1
    rcases Finset.mem_union.mp he with he | he
    · exact Finset.disjoint_left.mp (section9FiniteMiddle_disjoint_first i ht0) hm'
        ((mem_clusterRevealBonds Q₁ F₁ e).mp he).1
    · exact Finset.disjoint_left.mp hS₃ hm' ((mem_clusterRevealBonds Q₃ F₃ e).mp he).1
  let μ := (percolation (D + 1) (criticalPoint (D + 1))).prod (percolation (D + 1) q)
  let ν := (section9RevealedLaw (criticalPoint (D + 1)) Q₁ H₁ Q₃ H₃ F₁ F₃).prod (percolation (D + 1) q)
  let P (E : Finset (Vertex (D + 1))) (w : Configuration (D + 1) × Configuration (D + 1)) :=
    (section9SprinklingCluster w.1 w.2 (orientedLatticePairs S) L R Q₁ F₁ Q₃ F₃ X B ∩
      section9SprinklingCluster w.1 w.2 (orientedLatticePairs S) L R Q₁ F₁ Q₃ F₃ (Y E) B).Nonempty
  have hrow : (∑ E ∈ J, ν.real {w | P E w}) ≤ K :=
    hK i t ht0 q hq L R Q₁ F₁ Q₃ F₃ B H₁ H₃ X U V J Y hdis hH₁ hH₃ hLQ hRQ
      hpos (Finset.filter_subset _ _) (Finset.filter_subset _ _) hB hX hJ (hreg C a) hJreg hXc hJc hBc
  have hnoexit : ¬ ℓ.isExit := by
    cases ℓ <;> simp [RouteLabel.isStep, RouteLabel.isExit] at hstep ⊢
  change (∑ E ∈ J, μ.real {w | Λ.firstGoodSharedTubeMark G ℓ {C} {E} a b w}) ≤ K
  refine le_trans (le_of_eq (Finset.sum_congr rfl fun E _ => ?_)) hrow
  have hraw : {w | Λ.firstGoodSharedTubeMark G ℓ {C} {E} a b w} =
      {w | (Λ.firstGoodNestBridge G ℓ {C} a w ∩ Λ.firstGoodNestBridge G ℓ {E} b w).Nonempty} := by
    ext w
    exact Λ.firstGoodSharedTubeMark_iff_raw_of_fresh G ℓ
      (actualLayout_readSet_disjoint D typ t ht k hk MOff Mcoal Kdiam M G.1 ℓ hnoexit) {C} {E} a b w
  have htr := rawBridgeMeet_translate_probability (criticalPoint (D + 1)) q c S L R Q₁ F₁ Q₃ F₃ X (Y E) B
  dsimp only at htr
  change _ = μ.real {w | P E w} at htr
  rw [← actual_Mid_eq typ t ht k hk MOff Mcoal Kdiam M hℓ,
    ← actual_L_eq typ t ht k hk MOff Mcoal Kdiam M hℓ,
    ← actual_R_eq typ t ht k hk MOff Mcoal Kdiam M hℓ, ← hQ₁, ← hQ₃] at htr
  simp only [F₁,F₃,X,Y,B,translateSites_add_neg_cancel] at htr
  rw [hraw]
  simp only [NestLayout.firstGoodNestBridge, sprinklingTargetBoundary, Finset.singleton_biUnion]
  refine htr.trans ?_
  exact (stepReadSet_revealed_probability_eq _ _ S L R Q₁ H₁ F₁ Q₃ H₃ F₃ hH₁ hH₃ hpos hfresh
    (P E) (rawBridgeMeet_readsOnly S L R Q₁ F₁ Q₃ F₃ X (Y E) B)).symm

end NearCritical.Section10
