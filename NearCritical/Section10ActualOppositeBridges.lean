module

public import NearCritical.Section10FirstGoodPersistence
public import NearCritical.Section10BridgeEventTranslation
public import NearCritical.Section10ActualOffspring
public import NearCritical.Section10FreshStep
public import NearCritical.Section10MoveReduction
public import NearCritical.Section10StepCardinality

/-! The separated part of (H3) for the actual shared tube mark. -/

@[expose] public section
noncomputable section

namespace NearCritical.Section10

open MeasureTheory Set
open scoped Classical

/-- Two opposite-sign whole-nest bridges in an actual shared tube satisfy
the separated bridge probability bound under the fresh product law. -/
theorem actualLayout_oppositeBridge_probability {D : ℕ} [LinearOrder (Finset (Vertex (D + 1)))] (hd : 5 ≤ D + 1)
    (asymp : TwoPointAsymptotics (D + 1)) (q₀ A₀ F₀ : ℝ)
    (hp0 : 0 < (criticalPoint (D + 1) : ℝ)) (hp1 : (criticalPoint (D + 1) : ℝ) < 1) :
    ∃ C : ℝ, ∀ (typ : TypicalParameters) (t : ℕ) (ht : 9 ≤ t) (k : ℕ) (hk : 0 < k)
      (MOff Mcoal Kdiam M : ℕ),
      let Λ := actualLayout D typ t ht k hk MOff Mcoal Kdiam M
      ∀ (z : Configuration (D + 1) × Configuration (D + 1)) (ℓ : RouteLabel D),
      let G := refineReveal Λ.ρ₀ Λ.S₀ z
      HasTube M ℓ → ℓ.isStep → ℓ.site ∈ Λ.siteBox → ℓ.target ∈ Λ.siteBox →
      ∀ (q : unitInterval), (q : ℝ) ≤ q₀ * (t : ℝ)^(-2 : ℝ) →
      ∀ (N N' : Finset (Finset (Vertex (D + 1)))) (a b : Bool), a ≠ b →
      ((sprinklingTargetBoundary N (Λ.src G ℓ a)).card : ℝ) ≤ A₀ * (t : ℝ)^(2 : ℝ) →
      ((sprinklingTargetBoundary N' (Λ.src G ℓ b)).card : ℝ) ≤ A₀ * (t : ℝ)^(2 : ℝ) →
      ((sprinklingTargetBoundary (Λ.fam G ℓ.target) (Λ.tgt G ℓ)).card : ℝ) ≤
        F₀ * (t : ℝ)^(((D + 1 : ℕ) : ℝ) - 4) →
      ((percolation (D + 1) (criticalPoint (D + 1))).prod (percolation (D + 1) q)).real
        {w | Λ.firstGoodSharedTubeMark G ℓ N N' a b w} ≤
        C * (t : ℝ)^(6 - ((D + 1 : ℕ) : ℝ)) := by
  obtain ⟨C, hC⟩ := bridge_intersection_probability_separated hd asymp q₀ (1/4) (by norm_num) A₀ F₀
  refine ⟨C, ?_⟩
  intro typ t ht k hk MOff Mcoal Kdiam M Λ z ℓ G hℓ hstep hsite htgt q hq N N' a b hab hXc hYc hBc
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
  let X := translateSites (-c) (sprinklingTargetBoundary N (Λ.src G ℓ a))
  let Y := translateSites (-c) (sprinklingTargetBoundary N' (Λ.src G ℓ b))
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
  have hsep : ∀ x ∈ X, ∀ y ∈ Y, (1/4:ℝ) * (t:ℝ) ≤ latticeDistance x y := by
    intro x hx y hy
    obtain ⟨u, hu, rfl⟩ := (mem_translateSites_iff _ _ x).mp hx
    obtain ⟨v, hv, rfl⟩ := (mem_translateSites_iff _ _ y).mp hy
    obtain ⟨U, _, huU⟩ := Finset.mem_biUnion.mp hu
    obtain ⟨V, _, hvV⟩ := Finset.mem_biUnion.mp hv
    rw [latticeDistance_translate]
    have hh := typicalRegularPatch_opposite_separation (by omega : 2 ≤ D + 1)
      typ t (Λ.center ℓ.site) (Λ.revealConfig G) U V (Λ.dir ℓ,true) a b hab huU hvV
    linarith
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
  let P (w : Configuration (D + 1) × Configuration (D + 1)) :=
    (section9SprinklingCluster w.1 w.2 (orientedLatticePairs S) L R Q₁ F₁ Q₃ F₃ X B ∩
      section9SprinklingCluster w.1 w.2 (orientedLatticePairs S) L R Q₁ F₁ Q₃ F₃ Y B).Nonempty
  have hbound : μ.real {w | P w} ≤ C * (t:ℝ)^(6 - ((D + 1 : ℕ) : ℝ)) := by
    rw [← stepReadSet_revealed_probability_eq _ _ S L R Q₁ H₁ F₁ Q₃ H₃ F₃ hH₁ hH₃ hpos hfresh P
      (rawBridgeMeet_readsOnly S L R Q₁ F₁ Q₃ F₃ X Y B)]
    exact hC i t ht0 q hq L R Q₁ F₁ Q₃ F₃ B H₁ H₃ X Y hH₁ hH₃ hLQ hRQ hpos
      (Finset.filter_subset _ _) (Finset.filter_subset _ _) hB (hroot N a) (hroot N' b) hsep
      (by simpa only [X, card_pullback] using hXc) (by simpa only [Y, card_pullback] using hYc)
      (by simpa only [B, card_pullback] using hBc)
  have htr := rawBridgeMeet_translate_probability (criticalPoint (D + 1)) q c S L R Q₁ F₁ Q₃ F₃ X Y B
  dsimp only at htr
  change _ = μ.real {w | P w} at htr
  rw [← actual_Mid_eq typ t ht k hk MOff Mcoal Kdiam M hℓ,
    ← actual_L_eq typ t ht k hk MOff Mcoal Kdiam M hℓ,
    ← actual_R_eq typ t ht k hk MOff Mcoal Kdiam M hℓ, ← hQ₁, ← hQ₃] at htr
  simp only [F₁,F₃,X,Y,B,translateSites_add_neg_cancel] at htr
  have hnoexit : ¬ ℓ.isExit := by
    cases ℓ <;> simp [RouteLabel.isStep, RouteLabel.isExit] at hstep ⊢
  have he : {w | Λ.firstGoodSharedTubeMark G ℓ N N' a b w} =
      {w | (Λ.firstGoodNestBridge G ℓ N a w ∩ Λ.firstGoodNestBridge G ℓ N' b w).Nonempty} := by
    ext w
    exact Λ.firstGoodSharedTubeMark_iff_raw_of_fresh G ℓ
      (actualLayout_readSet_disjoint D typ t ht k hk MOff Mcoal Kdiam M G.1 ℓ
        hnoexit) N N' a b w
  rw [he]
  exact htr.trans_le hbound

/-- For fixed typicality constants and nest size, the actual opposite-sign
bridge mark has probability at most one fortieth at large source scales. -/
theorem actualLayout_oppositeBridge_small {D : ℕ} [LinearOrder (Finset (Vertex (D + 1)))] (hd : 7 ≤ D + 1)
    (asymp : TwoPointAsymptotics (D + 1)) (q₀ : ℝ)
    (hp0 : 0 < (criticalPoint (D + 1) : ℝ)) (hp1 : (criticalPoint (D + 1) : ℝ) < 1)
    (typ : TypicalParameters) (hb : 0 ≤ typ.boundaryUpper) (k : ℕ) (hk : 0 < k) :
    ∃ T : ℕ, ∀ (t : ℕ) (ht : 9 ≤ t), T ≤ t → ∀ (MOff Mcoal Kdiam M : ℕ),
      let Λ := actualLayout D typ t ht k hk MOff Mcoal Kdiam M
      ∀ (z : Configuration (D + 1) × Configuration (D + 1)) (ℓ : RouteLabel D),
      let G := refineReveal Λ.ρ₀ Λ.S₀ z
      HasTube M ℓ → ℓ.isStep → ℓ.site ∈ Λ.siteBox → ℓ.target ∈ Λ.siteBox →
      Λ.goodCube G ℓ.target →
      ∀ (q : unitInterval), (q : ℝ) ≤ q₀ * (t : ℝ)^(-2 : ℝ) →
      ∀ (N N' : Finset (Finset (Vertex (D + 1)))) (a b : Bool), a ≠ b →
      N ⊆ Λ.fam G ℓ.site → N' ⊆ Λ.fam G ℓ.site → N.card = k → N'.card = k →
      ((percolation (D + 1) (criticalPoint (D + 1))).prod (percolation (D + 1) q)).real
        {w | Λ.firstGoodSharedTubeMark G ℓ N N' a b w} ≤ 1/40 := by
  let A₀ := 4 * (k:ℝ) * typ.boundaryUpper
  let F₀ := (2:ℝ)^(D+1-6) * typ.countUpper * (8 * typ.boundaryUpper)
  obtain ⟨C, hC⟩ := actualLayout_oppositeBridge_probability (by omega : 5 ≤ D+1) asymp q₀ A₀ F₀ hp0 hp1
  obtain ⟨T, hT⟩ := exists_nat_gt (40 * max 0 C)
  refine ⟨T, ?_⟩
  intro t ht hlarge MOff Mcoal Kdiam M Λ z ℓ G hℓ hstep hsite htgt hgood q hq N N' a b hab hN hN' hcard hcard'
  have hsrc (P : Finset (Finset (Vertex (D + 1)))) (s : Bool)
      (hP : P ⊆ Λ.fam G ℓ.site) (hcardP : P.card = k) :
      ((sprinklingTargetBoundary P (Λ.src G ℓ s)).card : ℝ) ≤ A₀ * (t:ℝ)^(2:ℝ) := by
    refine (Λ.srcBoundary_card_le G ℓ s P hP).trans_eq ?_
    change (P.card:ℝ) * (typ.boundaryUpper * (2*(t:ℝ))^2) = _
    rw [hcardP, Real.rpow_two]
    dsimp only [A₀]
    ring
  have hB :
      ((sprinklingTargetBoundary (Λ.fam G ℓ.target) (Λ.tgt G ℓ)).card : ℝ) ≤
        F₀ * (t:ℝ)^(((D+1:ℕ):ℝ)-4) := by
    refine (Λ.tgtBoundary_card_le G ℓ hgood hb).trans_eq ?_
    change (typ.countUpper * (2*(t:ℝ))^(D+1-6)) * (2 * (typ.boundaryUpper * (2*(t:ℝ))^2)) = _
    have he : ((D+1:ℕ):ℝ)-4 = ((D+1-4:ℕ):ℝ) := by
      rw [Nat.cast_sub (by omega)]
      norm_num
    rw [he, Real.rpow_natCast, show D+1-4 = (D+1-6)+2 by omega, pow_add, mul_pow]
    dsimp only [F₀]
    ring
  refine (hC typ t ht k hk MOff Mcoal Kdiam M z ℓ hℓ hstep hsite htgt q hq N N' a b hab
    (hsrc N a hN hcard) (hsrc N' b hN' hcard') hB).trans ?_
  have ht1 : (1:ℝ) ≤ t := by exact_mod_cast (show 1 ≤ t by omega)
  have ht0 : (0:ℝ) < t := zero_lt_one.trans_le ht1
  have hd' : (7:ℝ) ≤ ((D+1:ℕ):ℝ) := by exact_mod_cast hd
  have hlarge' : 40 * max 0 C ≤ (t:ℝ) := hT.le.trans (by exact_mod_cast hlarge)
  calc
    _ ≤ max 0 C * (t:ℝ)^(6-((D+1:ℕ):ℝ)) :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg ht0.le _)
    _ ≤ max 0 C * (t:ℝ)^(-1:ℝ) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le ht1 (by linarith)) (le_max_left _ _)
    _ = max 0 C / (t:ℝ) := by rw [Real.rpow_neg ht0.le, Real.rpow_one, div_eq_mul_inv]
    _ ≤ _ := (div_le_iff₀ ht0).mpr (by linarith)

/-- The actual shared physical step contracts the phase-continuation row
at sufficiently large scale, uniformly in the routes and valid nests. -/
theorem actualLayout_shared_persistence {D : ℕ} [LinearOrder (Finset (Vertex (D + 1)))] (hd : 7 ≤ D + 1)
    (asymp : TwoPointAsymptotics (D + 1)) (q₀ : ℝ)
    (hp0 : 0 < (criticalPoint (D + 1) : ℝ)) (hp1 : (criticalPoint (D + 1) : ℝ) < 1)
    (typ : TypicalParameters) (hb : 0 ≤ typ.boundaryUpper) (k : ℕ) (hk : 0 < k) :
    ∃ T : ℕ, ∀ (t : ℕ) (ht : 9 ≤ t), T ≤ t → ∀ (MOff Mcoal Kdiam M : ℕ),
      let Λ := actualLayout D typ t ht k hk MOff Mcoal Kdiam M
      let p := criticalPoint (D+1)
      ∀ (q : unitInterval), (q:ℝ) ≤ q₀ * (t:ℝ)^(-2:ℝ) →
      ∀ (ρ κ : ℝ) (hκ : 0 < κ), 0 < ρ → ρ ≤ 9/8 →
      ∀ (hs : ∀ (γ : SourceRoute D M) (G : Λ.Φ) (j : ℕ) (x : Λ.X), ρ⁻¹ ≤
        localSuccessProbability p q (Λ.Bl₀ G.1 (routeLab M γ.position j))
          (bitSet G.2 (fun w => Λ.succσ G (routeLab M γ.position j) x
            (Λ.view G.1 (routeLab M γ.position j) w))))
        (hsiteProb : ∀ s, κ⁻¹ ≤ coupledProb p q (Λ.siteEvent s)),
      ∀ (G : Λ.Φ) (γ γ' : SourceRoute D M) (j j' : ℕ) (active active' : ℕ → Bool),
        active j = true → active' j' = true →
        routeLab M γ.position j = routeLab M γ'.position j' →
        HasTube M (routeLab M γ.position j) →
        ∀ x x' : Λ.X, Λ.moveCtx G (routeLab M γ.position j) x →
        Λ.moveCtx G (routeLab M γ'.position j') x' →
        let ℓ := routeLab M γ.position j
        let μ := (percolation (D+1) p).prod (percolation (D+1) q)
        let A (a b : Bool) := {w | Λ.firstGoodSharedTubeMark G ℓ x.1.val x'.1.val a b w}
        let K := usedMaskedKernel active (Λ.firstGoodMaskBase p q ρ κ hκ hs hsiteProb γ G active)
        let K' := usedMaskedKernel active' (Λ.firstGoodMaskBase p q ρ κ hκ hs hsiteProb γ' G active')
        (∫ w, ∑ y : Λ.X × Λ.X, (A y.1.2 y.2.2).indicator
          (fun w => K j x y.1 w * K' j' x' y.2 w) w ∂μ) ≤ 2/3 := by
  obtain ⟨T, hT⟩ := actualLayout_oppositeBridge_small hd asymp q₀ hp0 hp1 typ hb k hk
  refine ⟨T, ?_⟩
  intro t ht htT MOff Mcoal Kdiam M Λ p q hq ρ κ hκ hρ hρ' hs hsiteProb G γ γ' j j' active active'
    hj hj' hlabel hTube x x' hx hx'
  apply Λ.firstGood_shared_persistence_row p q ρ κ hκ hs hsiteProb hρ hρ' G γ γ' j j'
    active active' hj hj' x x' hx hx'
  intro a b hab
  obtain ⟨hstep, _, hsite, htgt, hcard, hN, _, hgood, z, hz⟩ := hx
  rw [← hlabel] at hx'
  obtain ⟨_, _, _, _, hcard', hN', _, _, _⟩ := hx'
  subst G
  exact hT t ht htT MOff Mcoal Kdiam M z (routeLab M γ.position j)
    hTube hstep hsite htgt hgood q hq x.1.val x'.1.val a b hab hN hN' hcard hcard'

end NearCritical.Section10
