module

public import NearCritical.Section10ActualBridgeRow
public import NearCritical.Section10NextNestOccupation
public import NearCritical.Section10StepSizes

/-! The one-child occupation input on the fresh product law of an actual tube. -/

@[expose] public section
noncomputable section

namespace NearCritical.Section10

open MeasureTheory Set
open scoped Classical

/-- The two translated heart reveals have positive mass, and the canonical
step's available bonds and middle bonds are disjoint from their reveals. -/
theorem actualLayout_origin_reveal_data {D : ℕ} (typ : TypicalParameters)
    (t : ℕ) (ht : 9 ≤ t) (k : ℕ) (hk : 0 < k) (MOff Mcoal Kdiam M : ℕ)
    (hp0 : 0 < (criticalPoint (D+1) : ℝ)) (hp1 : (criticalPoint (D+1) : ℝ) < 1) :
    let Λ := actualLayout D typ t ht k hk MOff Mcoal Kdiam M
    ∀ (z : Configuration (D+1) × Configuration (D+1)) (ℓ : RouteLabel D),
    let G := refineReveal Λ.ρ₀ Λ.S₀ z
    HasTube M ℓ → ℓ.site ∈ Λ.siteBox → ℓ.target ∈ Λ.siteBox →
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
    H₁ ⊆ Q₁ ∧ H₃ ⊆ Q₃ ∧
      percolation (D+1) (criticalPoint (D+1)) (section9RevealEvent Q₁ H₁ Q₃ H₃ F₁ F₃) ≠ 0 ∧
      Disjoint (clusterRevealBonds Q₁ F₁ ∪ clusterRevealBonds Q₃ F₃)
        ((sprinklingAvailableBonds L Q₁ F₁ ∪ sprinklingAvailableBonds R Q₃ F₃) ∪ internalBondSet S) := by
  intro Λ z ℓ G hℓ hsite htgt i c L R S Q₁ Q₃ H₁ H₃ F₁ F₃
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
  exact ⟨hH₁,hH₃,hpos,hfresh⟩

/-- A prescribed pair of typical clusters satisfies H1 on the actual
translated physical tube under the independent fresh product law. -/
theorem actualLayout_offspring_hit_probability {D : ℕ} (hd : 2 ≤ D+1)
    (asymp : TwoPointAsymptotics (D+1)) (q₀ : ℝ)
    (hp0 : 0 < (criticalPoint (D+1) : ℝ)) (hp1 : (criticalPoint (D+1) : ℝ) < 1)
    (typ : TypicalParameters) (hb : 0 ≤ typ.boundaryUpper) :
    ∃ C : ℝ, ∀ (t : ℕ) (ht : 9 ≤ t) (k : ℕ) (hk : 0 < k) (MOff Mcoal Kdiam M : ℕ),
      let Λ := actualLayout D typ t ht k hk MOff Mcoal Kdiam M
      ∀ (z : Configuration (D+1) × Configuration (D+1)) (ℓ : RouteLabel D),
      let G := refineReveal Λ.ρ₀ Λ.S₀ z
      HasTube M ℓ → ℓ.site ∈ Λ.siteBox → ℓ.target ∈ Λ.siteBox →
      ∀ (q : unitInterval), (q:ℝ) ≤ q₀ * (t:ℝ)^(-2:ℝ) →
      ∀ (A B : Finset (Vertex (D+1))) (a : Bool),
        A ∈ Λ.fam G ℓ.site → B ∈ Λ.fam G ℓ.target →
        ((percolation (D+1) (criticalPoint (D+1))).prod (percolation (D+1) q)).real
          {w | (sprinkledPivotalPairs w.1 w.2 (orientedLatticePairs (Λ.Mid ℓ))
            (Λ.L ℓ) (Λ.R ℓ) (Λ.Q ℓ.site) (Λ.Fat G.1 ℓ.site)
            (Λ.Q ℓ.target) (Λ.Fat G.1 ℓ.target) (Λ.src G ℓ a A) (Λ.tgt G ℓ B)).Nonempty} ≤
          C * (t:ℝ)^(6-((D+1:ℕ):ℝ)) := by
  let A₀ := 8 * typ.boundaryUpper
  obtain ⟨C, hC⟩ := offspring_probability_upper_scale hd asymp q₀ A₀
  refine ⟨C, ?_⟩
  intro t ht k hk MOff Mcoal Kdiam M Λ z ℓ G hℓ hsite htgt q hq A B a hA hB
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
  let X := translateSites (-c) (Λ.src G ℓ a A)
  let Y := translateSites (-c) (Λ.tgt G ℓ B)
  have ht0 : 0 < t := by omega
  obtain ⟨hH₁,hH₃,hpos,hfresh⟩ :=
    actualLayout_origin_reveal_data typ t ht k hk MOff Mcoal Kdiam M hp0 hp1 z ℓ hℓ hsite htgt
  have hQ₁ : Λ.Q ℓ.site = translateSites c Q₁ := actual_Qsite_eq typ t ht k hk MOff Mcoal Kdiam M ℓ
  have hQ₃ : Λ.Q ℓ.target = translateSites c Q₃ := actual_Qtarget_eq typ t ht k hk MOff Mcoal Kdiam M hℓ
  have hX : X ⊆ Q₁ := by
    have hsub : Λ.src G ℓ a A ⊆ Λ.Q ℓ.site := typicalRegularPatch_subset_cube _ _ _ _ _ _ _
    rw [hQ₁] at hsub
    exact fun u hu => mem_translateSites_neg c Q₁ (translateSites_mono _ hsub hu)
  have hY : Y ⊆ Q₃ := by
    have hsub : Λ.tgt G ℓ B ⊆ Λ.Q ℓ.target :=
      Finset.union_subset (typicalRegularPatch_subset_cube _ _ _ _ _ _ _)
        (typicalRegularPatch_subset_cube _ _ _ _ _ _ _)
    rw [hQ₃] at hsub
    exact fun u hu => mem_translateSites_neg c Q₃ (translateSites_mono _ hsub hu)
  have hYc : (Y.card:ℝ) ≤ A₀ * (t:ℝ)^(2:ℝ) := by
    rw [show Y.card = _ from card_pullback _ _, Real.rpow_two]
    refine (Λ.tgt_card_le G ℓ hB).trans_eq ?_
    change 2 * (typ.boundaryUpper * (2*(t:ℝ))^2) = A₀ * (t:ℝ)^2
    dsimp only [A₀]
    ring
  have hXc : (X.card:ℝ) ≤ A₀ * (t:ℝ)^(2:ℝ) := by
    rw [show X.card = _ from card_pullback _ _, Real.rpow_two]
    have htyp := ((mem_typicalClusterFamily _ _ _ _ A).mp hA).2
    refine (htyp.2.2.2.2.2.1 (Λ.dir ℓ,true) a).2.trans ?_
    change typ.boundaryUpper * (2*(t:ℝ))^2 ≤ A₀ * (t:ℝ)^2
    have hb' : 0 ≤ typ.boundaryUpper * (t:ℝ)^2 := by positivity
    dsimp only [A₀]
    nlinarith only [hb']
  let μ := (percolation (D+1) (criticalPoint (D+1))).prod (percolation (D+1) q)
  let P (w : Configuration (D+1) × Configuration (D+1)) :=
    (section9SprinklingCluster w.1 w.2 (orientedLatticePairs S) L R Q₁ F₁ Q₃ F₃ X Y).Nonempty
  have hr : ReadsOnly (stepReadSet S L R Q₁ F₁ Q₃ F₃) P := by
    intro u v huv
    exact congrArg Finset.Nonempty (rawBridge_readsOnly S L R Q₁ F₁ Q₃ F₃ X Y u v huv)
  have hbound : μ.real {w | P w} ≤ C * (t:ℝ)^(6-((D+1:ℕ):ℝ)) := by
    rw [← stepReadSet_revealed_probability_eq _ _ S L R Q₁ H₁ F₁ Q₃ H₃ F₃ hH₁ hH₃ hpos hfresh P hr]
    simpa only [P, section9SprinklingCluster_nonempty_iff] using
      hC i t ht0 q hq H₁ H₃ F₁ F₃ X Y hH₁ hH₃ hX hY hpos hXc hYc
  have htr := rawBridgeMeet_translate_probability (criticalPoint (D+1)) q c S L R Q₁ F₁ Q₃ F₃ X X Y
  dsimp only at htr
  rw [← actual_Mid_eq typ t ht k hk MOff Mcoal Kdiam M hℓ,
    ← actual_L_eq typ t ht k hk MOff Mcoal Kdiam M hℓ,
    ← actual_R_eq typ t ht k hk MOff Mcoal Kdiam M hℓ, ← hQ₁, ← hQ₃] at htr
  simp only [X,Y,F₁,F₃,translateSites_add_neg_cancel, Finset.inter_self] at htr
  have hactual := htr.trans_le hbound
  simpa only [section9SprinklingCluster_nonempty_iff] using hactual

end NearCritical.Section10
