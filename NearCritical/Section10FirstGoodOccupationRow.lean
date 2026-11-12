module

public import NearCritical.Section10ActualOffspringHit
public import NearCritical.Section10ActualRoute

/-! Occupation of a prescribed cluster in an outgoing first-good nest. -/

@[expose] public section
noncomputable section

namespace NearCritical.Section10.NestLayout

open MeasureTheory Set
open scoped Classical

variable {D d M : ℕ} (Λ : NestLayout D d) [LinearOrder (Finset (Vertex d))]
  (p q : unitInterval) (ρ κ : ℝ) (hκ : 0 < κ)
  (hs : ∀ (γ : SourceRoute D M) (G : Λ.Φ) (t : ℕ) (x : Λ.X), ρ⁻¹ ≤
    localSuccessProbability p q (Λ.Bl₀ G.1 (routeLab M γ.position t))
      (bitSet G.2 (fun z => Λ.succσ G (routeLab M γ.position t) x
        (Λ.view G.1 (routeLab M γ.position t) z))))
  (hsiteProb : ∀ s, κ⁻¹ ≤ coupledProb p q (Λ.siteEvent s))

/-- At fixed reveal, every positive first-good transition picks an
admissible next nest in the raw step view of the fresh bits. -/
theorem firstGood_positive_svNext_of_fresh
    (γ : SourceRoute D M) (G : Λ.Φ) (t : ℕ) (x y : Λ.X)
    (z : Configuration d × Configuration d) :
    let ℓ := routeLab M γ.position t
    Disjoint (Λ.readSet G.1 ℓ) (Λ.S₀ G.1) →
    Λ.moveCtx G ℓ x →
    0 < (Λ.ruleFirstGood M p q ρ κ hκ hs hsiteProb).toNestRule.kernel γ G t x y z →
    y.1 ∈ svNext (Λ.view G.1 ℓ z).1 x.1.val (Λ.fam G ℓ.target)
      (Λ.src G ℓ x.2) (Λ.tgt G ℓ) Λ.k Λ.P := by
  intro ℓ hfresh hctx hpos
  let T := Λ.Bl₀ G.1 ℓ
  let A := bitSet (T := T) G.2 (fun θ => Λ.succσ G ℓ x (Λ.view G.1 ℓ θ))
  let O := fun ξ : T → Bool => Λ.offFirstGood G ℓ x (Λ.view G.1 ℓ (gluePair G.2 ξ))
  change 0 < stepKernel T A O (localSuccessProbability p q T A) y z at hpos
  obtain ⟨hA,hO⟩ := stepKernel_pos T A O _ y z hpos
  let w := gluePair G.2 (T.restrict (layerVal z))
  let v := Λ.view G.1 ℓ w
  have hsucc : Λ.succσ G ℓ x v := hA
  have hv : y ∈ Λ.offFirstGood G ℓ x v := hO
  have hv' := Λ.offFirstGood_subset G ℓ x v hv
  rw [offσ, if_pos ⟨hctx,hsucc.1 hctx⟩] at hv'
  have hnext := (Finset.mem_product.mp hv').1
  have he : v.1 = (Λ.view G.1 ℓ z).1 := by
    apply stepView_readsOnly
    intro e he
    have hr : e ∈ Λ.readSet G.1 ℓ := Finset.mem_union_left _ he
    have hn : e ∉ Λ.S₀ G.1 := fun h => Finset.disjoint_left.mp hfresh hr h
    have hT : e ∈ T := Finset.mem_sdiff.mpr ⟨hr,hn⟩
    change layerVal (gluePair G.2 (T.restrict (layerVal z))) e = layerVal z e
    rw [layerVal_gluePair, dif_neg hn, dif_pos hT]
    rfl
  rw [he] at hnext
  exact hnext

/-- The normalized outgoing mass that contains a specified child is at
most the H1 union bound over incoming representatives, times the row cap. -/
theorem firstGood_child_occupation_row_le (hρ : 0 < ρ) (γ : SourceRoute D M)
    (G : Λ.Φ) (t : ℕ) (x : Λ.X) (C : Finset (Vertex d)) {a : ℝ} :
    let ℓ := routeLab M γ.position t
    let μ := (percolation d p).prod (percolation d q)
    let K := (Λ.ruleFirstGood M p q ρ κ hκ hs hsiteProb).toNestRule.kernel γ G
    Disjoint (Λ.readSet G.1 ℓ) (Λ.S₀ G.1) →
    Λ.moveCtx G ℓ x →
    Λ.Mid ℓ ⊆ Λ.L ℓ →
    Disjoint (Λ.Mid ℓ : Set (Vertex d)) (Λ.Q ℓ.site : Set (Vertex d)) →
    (∀ A ∈ x.1.val, μ.real {z | (sprinkledPivotalPairs z.1 z.2
      (orientedLatticePairs (Λ.Mid ℓ)) (Λ.L ℓ) (Λ.R ℓ)
      (Λ.Q ℓ.site) (Λ.Fat G.1 ℓ.site) (Λ.Q ℓ.target) (Λ.Fat G.1 ℓ.target)
      (Λ.src G ℓ x.2 A) (Λ.tgt G ℓ C)).Nonempty} ≤ a) →
    (∫ z, ∑ y : Λ.X, if C ∈ y.1.val then K t x y z else 0 ∂μ) ≤
      ρ * (x.1.val.card:ℝ) * a := by
  intro ℓ μ K hfresh hctx hML hMQ hrare
  let R := (Λ.ruleFirstGood M p q ρ κ hκ hs hsiteProb).toNestRule
  let F (A : Finset (Vertex d)) := {z : Configuration d × Configuration d |
    (sprinkledPivotalPairs z.1 z.2 (orientedLatticePairs (Λ.Mid ℓ)) (Λ.L ℓ) (Λ.R ℓ)
      (Λ.Q ℓ.site) (Λ.Fat G.1 ℓ.site) (Λ.Q ℓ.target) (Λ.Fat G.1 ℓ.target)
      (Λ.src G ℓ x.2 A) (Λ.tgt G ℓ C)).Nonempty}
  let U := ⋃ A ∈ x.1.val, F A
  have hU : MeasurableSet U := by
    apply Finset.measurableSet_biUnion
    intro A _
    have hloc := rawBridge_readsOnly (Λ.Mid ℓ) (Λ.L ℓ) (Λ.R ℓ)
      (Λ.Q ℓ.site) (Λ.Fat G.1 ℓ.site) (Λ.Q ℓ.target) (Λ.Fat G.1 ℓ.target)
      (Λ.src G ℓ x.2 A) (Λ.tgt G ℓ C)
    have hF : ReadsOnly
        (stepReadSet (Λ.Mid ℓ) (Λ.L ℓ) (Λ.R ℓ) (Λ.Q ℓ.site) (Λ.Fat G.1 ℓ.site)
          (Λ.Q ℓ.target) (Λ.Fat G.1 ℓ.target)) (fun z => z ∈ F A) := by
      intro z z' hz
      change _ = _
      apply propext
      change (_ : Prop) ↔ _
      simp only [F, Set.mem_setOf_eq, ← section9SprinklingCluster_nonempty_iff]
      exact Iff.of_eq (congrArg (fun B : Finset (Vertex d) => B.Nonempty) (hloc z z' hz))
    exact hF.measurableSet
  let T := Λ.Bl₀ G.1 ℓ
  let A : Set (T → Bool) := R.a γ G t x
  let O : (T → Bool) → Finset Λ.X := R.o γ G t x
  let s := localSuccessProbability p q T A
  have hs' : ρ⁻¹ ≤ s := hs γ G t x
  have hs0 : 0 < s := (inv_pos.mpr hρ).trans_le hs'
  have hnon (z : Configuration d × Configuration d) (y : Λ.X) : 0 ≤ K t x y z :=
    stepKernel_nonneg T A O hs0.le y z
  have hcap (z : Configuration d × Configuration d) : (∑ y, K t x y z) ≤ ρ := by
    change (∑ y : Λ.X, stepKernel T A O s y z) ≤ ρ
    rw [stepKernel_sum T A O (R.ho γ G t x)]
    split_ifs
    · rw [one_mul]
      exact (inv_le_comm₀ hs0 hρ).mpr hs'
    · rw [zero_mul]
      exact hρ.le
  have hzero (z : Configuration d × Configuration d) (hz : z ∉ U)
      (y : Λ.X) (hy : C ∈ y.1.val) : K t x y z = 0 := by
    apply le_antisymm _ (hnon z y)
    by_contra! hp
    have hn := Λ.firstGood_positive_svNext_of_fresh p q ρ κ hκ hs hsiteProb
      γ G t x y z hfresh hctx hp
    obtain ⟨_, B, hB, hhit⟩ :=
      svNext_member_has_opened_target z.1 z.2 (Λ.Mid ℓ) (Λ.L ℓ) (Λ.R ℓ)
        (Λ.Q ℓ.site) (Λ.Fat G.1 ℓ.site) (Λ.Q ℓ.target) (Λ.Fat G.1 ℓ.target)
        hML hMQ x.1.val (Λ.fam G ℓ.target) (Λ.src G ℓ x.2) (Λ.tgt G ℓ) hn hy
    exact hz (Set.mem_iUnion.mpr ⟨B, Set.mem_iUnion.mpr ⟨hB, hhit⟩⟩)
  calc
    _ ≤ ∫ z, U.indicator (fun _ => ρ) z ∂μ := by
      refine integral_mono_of_nonneg (Filter.Eventually.of_forall ?_)
        ((integrable_const ρ).indicator hU) (Filter.Eventually.of_forall ?_)
      · intro z
        exact Finset.sum_nonneg fun y _ => by split_ifs; exacts [hnon z y, le_rfl]
      · intro z
        by_cases hz : z ∈ U
        · rw [Set.indicator_of_mem hz]
          refine (Finset.sum_le_sum fun y _ => ?_).trans (hcap z)
          split_ifs
          · exact le_rfl
          · exact hnon z y
        · rw [Set.indicator_of_notMem hz]
          exact Finset.sum_nonpos fun y _ => by
            split_ifs with hy
            · rw [hzero z hz y hy]
            · exact le_rfl
    _ = μ.real U * ρ := by rw [integral_indicator_const _ hU, smul_eq_mul]
    _ ≤ ((x.1.val.card:ℝ)*a) * ρ := by
      refine mul_le_mul_of_nonneg_right ((measureReal_biUnion_finset_le _ _).trans ?_) hρ.le
      calc
        _ ≤ ∑ _B ∈ x.1.val, a := Finset.sum_le_sum hrare
        _ = _ := by simp [nsmul_eq_mul]
    _ = _ := by ring

end NearCritical.Section10.NestLayout

namespace NearCritical.Section10

open MeasureTheory Set
open scoped Classical

/-- A given typical child has outgoing normalized first-good weight of
order t^(6−d) on the actual fresh tube. -/
theorem actualLayout_firstGood_child_row {D : ℕ} [LinearOrder (Finset (Vertex (D+1)))]
    (hd : 2 ≤ D+1) (asymp : TwoPointAsymptotics (D+1)) (q₀ : ℝ)
    (hp0 : 0 < (criticalPoint (D+1) : ℝ)) (hp1 : (criticalPoint (D+1) : ℝ) < 1)
    (typ : TypicalParameters) (hb : 0 ≤ typ.boundaryUpper) :
    ∃ C : ℝ, ∀ (t : ℕ) (ht : 9 ≤ t) (k : ℕ) (hk : 0 < k) (MOff Mcoal Kdiam M : ℕ),
      let Λ := actualLayout D typ t ht k hk MOff Mcoal Kdiam M
      let p := criticalPoint (D+1)
      ∀ (q : unitInterval), (q:ℝ) ≤ q₀ * (t:ℝ)^(-2:ℝ) →
      ∀ (ρ κ : ℝ) (hκ : 0 < κ), 0 < ρ →
      ∀ (hs : ∀ (γ : SourceRoute D M) (G : Λ.Φ) (j : ℕ) (x : Λ.X), ρ⁻¹ ≤
        localSuccessProbability p q (Λ.Bl₀ G.1 (routeLab M γ.position j))
          (bitSet G.2 (fun w => Λ.succσ G (routeLab M γ.position j) x
            (Λ.view G.1 (routeLab M γ.position j) w))))
        (hsiteProb : ∀ s, κ⁻¹ ≤ coupledProb p q (Λ.siteEvent s)),
      ∀ (G : Λ.Φ) (γ : SourceRoute D M) (j : ℕ) (x : Λ.X) (B : Finset (Vertex (D+1))),
      let ℓ := routeLab M γ.position j
      Λ.moveCtx G ℓ x → B ∈ Λ.fam G ℓ.target →
      let K := (Λ.ruleFirstGood M p q ρ κ hκ hs hsiteProb).toNestRule.kernel γ G
      (∫ z, ∑ y : Λ.X, if B ∈ y.1.val then K j x y z else 0
        ∂((percolation (D+1) p).prod (percolation (D+1) q))) ≤
        ρ * (k:ℝ) * (C * (t:ℝ)^(6-((D+1:ℕ):ℝ))) := by
  obtain ⟨C,hC⟩ := actualLayout_offspring_hit_probability hd asymp q₀ hp0 hp1 typ hb
  refine ⟨C, ?_⟩
  intro t ht k hk MOff Mcoal Kdiam M Λ p q hq ρ κ hκ hρ hs hsiteProb G γ j x B ℓ hx hB
  have hctx := hx
  obtain ⟨hstep, hmove, hsite, htgt, hcard, hnest, _, _, z, hz⟩ := hx
  have hTube : HasTube M ℓ := routeLab_hasTube γ.1.1 γ.2 hstep hmove
  have hnoexit : ¬ ℓ.isExit := by
    have he : ∀ l : RouteLabel D, l.isStep → ¬ l.isExit := by
      intro l
      cases l <;> simp [RouteLabel.isStep, RouteLabel.isExit]
    exact he ℓ hstep
  have hM := actual_Mid_eq typ t ht k hk MOff Mcoal Kdiam M hTube
  have hL := actual_L_eq typ t ht k hk MOff Mcoal Kdiam M hTube
  have hQ := actual_Qsite_eq typ t ht k hk MOff Mcoal Kdiam M ℓ
  have hML : Λ.Mid ℓ ⊆ Λ.L ℓ := by
    rw [hM,hL]
    apply translateSites_mono
    rw [section9FiniteMiddle_eq_inter]
    exact Finset.inter_subset_left
  have hMQ : Disjoint (Λ.Mid ℓ) (Λ.Q ℓ.site) := by
    rw [hM,hQ]
    exact (Finset.disjoint_image (add_right_injective _)).mpr
      (section9FiniteMiddle_disjoint_first _ (by omega))
  have hMQ' : Disjoint (Λ.Mid ℓ : Set (Vertex (D+1))) (Λ.Q ℓ.site : Set (Vertex (D+1))) :=
    Set.disjoint_left.mpr (fun _ hu hv => Finset.disjoint_left.mp hMQ hu hv)
  subst G
  have hh := Λ.firstGood_child_occupation_row_le p q ρ κ hκ hs hsiteProb hρ γ
    (refineReveal Λ.ρ₀ Λ.S₀ z) j x B
    (actualLayout_readSet_disjoint D typ t ht k hk MOff Mcoal Kdiam M
      (Λ.ρ₀ z) ℓ hnoexit) hctx hML hMQ'
    (fun A hA => hC t ht k hk MOff Mcoal Kdiam M z ℓ hTube hsite htgt q hq A B x.2 (hnest hA) hB)
  change x.1.val.card = k at hcard
  simpa only [hcard] using hh

end NearCritical.Section10
