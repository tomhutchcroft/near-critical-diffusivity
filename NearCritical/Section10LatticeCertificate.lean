module

public import NearCritical.Section10LatticeHelpers
public import NearCritical.Section10SemanticCertificate

/-! Source `lem.nw.path` for the lattice nest rule.

`NestLayout.certificate`: for an actual configuration pair `z` and a route `γ`
with positive cube weight (all cubes pre-good) and a surviving chain of
`NestLayout.rule`, the supercritical configuration `z.1 OR z.2` lies in
`chemicalChainCertificateEvent`, with cluster pieces of length at most
`2 * diameterUpper * (2t)^2` and bridges of length at most `Kdiam`.

The geometric facts about the layout are hypotheses (to be proved for the
actual tubes): route sites are in the box; half tubes lie in the support, avoid
the far cube, and the source half face lies in the left tube; the bottom face
of level-0 cubes is in the bottom face of the box; exit bonds of top cubes end
in the exit face. `hcount` is the parameter condition `k <= c * l0^(d-6)`.
-/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open scoped Classical

lemma RouteLabel.not_isStart_of_isStep {D : ℕ} {ℓ : RouteLabel D} (h : ℓ.isStep) :
    ¬ ℓ.isStart := by
  cases ℓ <;> simp [RouteLabel.isStep, RouteLabel.isStart] at h ⊢

namespace NestLayout
variable {D d : ℕ} (Λ : NestLayout D d)

theorem certificate [Nontrivial (Fin d × Bool)] (M : ℕ) (hM : 1 ≤ M) (p q : unitInterval)
    (ϱ κ : ℝ) (hκ : 0 < κ)
    (hs : ∀ (γ : SourceRoute D M) (G : Λ.Φ) (t : ℕ) (x : Λ.X), ϱ⁻¹ ≤
      localSuccessProbability p q (Λ.Bl₀ G.1 (routeLab M γ.position t))
        (bitSet G.2 (fun z => Λ.succσ G (routeLab M γ.position t) x
          (Λ.view G.1 (routeLab M γ.position t) z))))
    (hsiteProb : ∀ s, κ⁻¹ ≤ coupledProb p q (Λ.siteEvent s))
    (z : Configuration d × Configuration d) (γ : SourceRoute D M)
    (hw : 0 < (Λ.rule M p q ϱ κ hκ hs hsiteProb).toNestRule.w γ
      ((Λ.rule M p q ϱ κ hκ hs hsiteProb).toNestRule.ρ z))
    (hsurv : ChainSurvives
      ((Λ.rule M p q ϱ κ hκ hs hsiteProb).toNestRule.kernel γ
        ((Λ.rule M p q ϱ κ hκ hs hsiteProb).toNestRule.ρ z)) (2 * M) 0
      ((Λ.rule M p q ϱ κ hκ hs hsiteProb).toNestRule.x₀ γ
        ((Λ.rule M p q ϱ κ hκ hs hsiteProb).toNestRule.ρ z)) z)
    (aC : Vertex d) (r : ℕ) (htopeq : Λ.top = M - 1)
    (hbox : ∀ t, t < 2 * M → (routeLab M γ.position t).site ∈ Λ.siteBox)
    (hcount : (Λ.k : ℝ) ≤ Λ.typ.countLower * (2 * (Λ.t : ℝ)) ^ (d - 6))
    (hQD : ∀ s ∈ Λ.siteBox, (Λ.Q s : Set (Vertex d)) ⊆
      (translateSites aC (chemicalCrossingSupport d r Λ.i₀) : Set (Vertex d)))
    (hgeo : ∀ t, t < 2 * M → ∀ ℓ : RouteLabel D, ℓ = routeLab M γ.position t →
      ℓ.isStep → ℓ.target ≠ ℓ.site →
      (Λ.L ℓ : Set (Vertex d)) ⊆
        (translateSites aC (chemicalCrossingSupport d r Λ.i₀) : Set (Vertex d)) ∧
      (Λ.R ℓ : Set (Vertex d)) ⊆
        (translateSites aC (chemicalCrossingSupport d r Λ.i₀) : Set (Vertex d)) ∧
      Disjoint (Λ.L ℓ : Set (Vertex d)) (typicalCube Λ.t (Λ.center ℓ.target) : Set (Vertex d)) ∧
      Disjoint (Λ.R ℓ : Set (Vertex d)) (typicalCube Λ.t (Λ.center ℓ.site) : Set (Vertex d)) ∧
      ∀ pl : Bool, typicalSplitFace Λ.t (Λ.center ℓ.site) (Λ.dir ℓ, true) pl ⊆ Λ.L ℓ)
    (hbot : ∀ s ∈ Λ.siteBox, s.1 = 0 →
      ∀ pt ∈ typicalFace Λ.t (Λ.center s) (Λ.i₀, false),
        ∃ x ∈ chemicalBottomFace d r Λ.i₀, pt = aC + x)
    (htop : ∀ s ∈ Λ.siteBox, s.1 = M - 1 →
      ∀ y ∈ typicalFace Λ.t (Λ.center s) (Λ.i₀, true),
        ∃ z' ∈ chemicalExitFace d r Λ.i₀, bondTip (y, Λ.i₀) = aC + z') :
    sprinkleOrConfiguration z.1 z.2 ∈ chemicalChainCertificateEvent aC r Λ.i₀
      (2 * (Λ.typ.diameterUpper * (2 * (Λ.t : ℝ)) ^ 2)) (Λ.Kdiam : ℝ) M := by
  have hgoodsite := (Λ.rule M p q ϱ κ hκ hs hsiteProb).weight_pos γ z hw
  have hpre : ∀ t, t < 2 * M →
      IsPreGoodCube Λ.typ Λ.t (Λ.center (routeLab M γ.position t).site) z.1 :=
    fun t ht => hgoodsite _ (routeLab_site γ.position ht).1 (hbox t ht)
  have hmono : ∀ e, z.1 e = true → sprinkleOrConfiguration z.1 z.2 e = true := by
    intro e he
    unfold sprinkleOrConfiguration
    rw [he]
    rfl
  have h0 := routeLab_zero M γ.position
  have hlast := routeLab_last hM γ.position
  have hfam : ∀ t, t < 2 * M →
      Λ.fam (refineReveal Λ.ρ₀ Λ.S₀ z) (routeLab M γ.position t).site =
        typicalClusterFamily Λ.typ Λ.t (Λ.center (routeLab M γ.position t).site) z.1 :=
    fun t ht => Λ.fam_eq z (hbox t ht)
  refine semanticRule_certificate (Λ.rule M p q ϱ κ hκ hs hsiteProb) hM z γ hsurv
    (fun x : Λ.X => (x.1.val : Set (Finset (Vertex d))))
    (fun t C => (clusterFaceBoundary C
      (typicalFace Λ.t (Λ.center (routeLab M γ.position t).site)) : Set (Vertex d)))
    (fun t x => x.1.val.card = Λ.k ∧
      x.1.val ⊆ Λ.fam (refineReveal Λ.ρ₀ Λ.S₀ z) (routeLab M γ.position t).site)
    aC r Λ.i₀ _ _ ?_ ?_ ?_ ?_
  · -- start
    intro y _ hoff
    have hoff' : y ∈ Λ.offσ (refineReveal Λ.ρ₀ Λ.S₀ z) (routeLab M γ.position 0)
        (⟨∅, Finset.empty_mem_powerset _⟩, true)
        (Λ.view (Λ.ρ₀ z) (routeLab M γ.position 0) z) := hoff
    unfold offσ at hoff'
    have hnostep : ¬ (routeLab M γ.position 0).isStep := by
      rw [h0]
      exact fun h => h
    rw [if_neg (fun h => hnostep h.1.1)] at hoff'
    have hstart : Λ.startCtx (refineReveal Λ.ρ₀ Λ.S₀ z) (routeLab M γ.position 0) := by
      refine ⟨by rw [h0]; trivial, hbox 0 (by omega), ?_⟩
      rw [hfam 0 (by omega)]
      have hc := (hpre 0 (by omega)).1
      exact_mod_cast hcount.trans hc
    rw [if_pos hstart] at hoff'
    obtain ⟨_, hcard, hsub⟩ := Finset.mem_filter.mp (Finset.mem_product.mp hoff').1
    have hsite1 : (routeLab M γ.position (0+1)).site = (routeLab M γ.position 0).site := by
      rw [routeLab_next_site γ.position (by omega), h0]
      rfl
    refine ⟨hcard, ?_⟩
    show y.1.val ⊆ Λ.fam (refineReveal Λ.ρ₀ Λ.S₀ z) (routeLab M γ.position (0+1)).site
    rw [hsite1]
    exact hsub
  · -- bottom
    intro y rep hInv hrep
    have hsite1 : (routeLab M γ.position (0+1)).site = (routeLab M γ.position 0).site := by
      rw [routeLab_next_site γ.position (by omega), h0]
      rfl
    have hrepfam : rep ∈ typicalClusterFamily Λ.typ Λ.t
        (Λ.center (routeLab M γ.position 1).site) z.1 := by
      rw [← hfam 1 (by omega)]
      exact hInv.2 hrep
    have htyp := ((mem_typicalClusterFamily _ _ _ _ _).mp hrepfam).2
    obtain ⟨pt, hpt⟩ := htyp.2.1 (Λ.i₀, false)
    have hlevel : (routeLab M γ.position 1).site.1 = 0 := by
      have h := hsite1
      rw [h0] at h
      show (routeLab M γ.position (0+1)).site.1 = 0
      rw [h]
      rfl
    obtain ⟨x, hx, hptx⟩ := hbot _ (hbox 1 (by omega)) hlevel pt (Finset.mem_inter.mp hpt).2
    refine ⟨pt, ?_, x, hx, hptx⟩
    exact Finset.mem_coe.mpr (Finset.mem_biUnion.mpr ⟨(Λ.i₀, false), Finset.mem_univ _, hpt⟩)
  · -- exit
    intro x y hInv hsucc _
    have hsucc' : Λ.succσ (refineReveal Λ.ρ₀ Λ.S₀ z) (routeLab M γ.position (2 * M - 1)) x
        (Λ.view (Λ.ρ₀ z) (routeLab M γ.position (2 * M - 1)) z) := hsucc
    have hT : 2 * M - 1 < 2 * M := by omega
    have hctx : Λ.exitCtx (refineReveal Λ.ρ₀ Λ.S₀ z) (routeLab M γ.position (2 * M - 1)) x := by
      refine ⟨by rw [hlast]; trivial, by rw [hlast, htopeq]; rfl, hbox _ hT, hInv.1, hInv.2⟩
    obtain ⟨rep, hrep, yv, hyv, hyw⟩ := hsucc'.2 hctx
    have hrepfam : rep ∈ typicalClusterFamily Λ.typ Λ.t
        (Λ.center (routeLab M γ.position (2 * M - 1)).site) z.1 := by
      rw [← hfam _ hT]
      exact hInv.2 hrep
    have hrepQ := typicalCluster_subset_cube _ _ _ _ hrepfam
    have hrepD : (rep : Set (Vertex d)) ⊆
        (translateSites aC (chemicalCrossingSupport d r Λ.i₀) : Set (Vertex d)) :=
      fun v hv => hQD _ (hbox _ hT) (Finset.mem_coe.mpr (hrepQ (Finset.mem_coe.mp hv)))
    have hyvbd := typicalRegularPatch_subset_faceBoundary _ _ _ _ _ _ _ hyv
    have hyvrep : yv ∈ rep := by
      unfold exitPatch typicalRegularPatch at hyv
      exact (Finset.mem_inter.mp (Finset.mem_filter.mp hyv).1).1
    obtain ⟨hyface, hopen⟩ := Finset.mem_filter.mp hyw
    have hyface' : yv ∈ typicalFace Λ.t (Λ.center (routeLab M γ.position (2 * M - 1)).site)
        (Λ.i₀, true) := by
      unfold exitPts at hyface
      rw [if_pos (by rw [hlast, htopeq]; exact ⟨trivial, rfl⟩)] at hyface
      exact hyface
    have hlevel : (routeLab M γ.position (2 * M - 1)).site.1 = M - 1 := by
      rw [hlast]
      rfl
    obtain ⟨z', hz', htip⟩ := htop _ (hbox _ hT) hlevel yv hyface'
    have htipD : bondTip (yv, Λ.i₀) ∈
        (translateSites aC (chemicalCrossingSupport d r Λ.i₀) : Set (Vertex d)) := by
      rw [htip]
      unfold translateSites chemicalCrossingSupport
      exact Finset.mem_coe.mpr (Finset.mem_image_of_mem _ (Finset.mem_union_right _ hz'))
    refine ⟨rep, hrep, yv, bondTip (yv, Λ.i₀), Finset.mem_coe.mpr hyvbd, ?_, ⟨z', hz', htip⟩, ?_⟩
    · exact ⟨⟨(yv, Λ.i₀), hopen, Or.inl ⟨rfl, rfl⟩⟩, hrepD (Finset.mem_coe.mpr hyvrep), htipD⟩
    · intro pt hpt
      exact ⟨restrictedGraph z.1 (rep : Set (Vertex d)), restrictedGraph_mono_of_le hmono hrepD,
        typicalCluster_boundary_connection Λ.typ Λ.t _ z.1 hrepfam (Finset.mem_coe.mp hpt)
          hyvbd⟩
  · -- steps
    intro t ht1 ht2 x y hInv hsucc hoff
    have hsucc' : Λ.succσ (refineReveal Λ.ρ₀ Λ.S₀ z) (routeLab M γ.position t) x
        (Λ.view (Λ.ρ₀ z) (routeLab M γ.position t) z) := hsucc
    have hoff' : y ∈ Λ.offσ (refineReveal Λ.ρ₀ Λ.S₀ z) (routeLab M γ.position t) x
        (Λ.view (Λ.ρ₀ z) (routeLab M γ.position t) z) := hoff
    have hstepk := routeLab_isStep γ.position ht1 ht2
    have hnext := routeLab_next_site (M := M) γ.position (t := t) (by omega)
    have htlt : t < 2 * M := by omega
    by_cases hmove : (routeLab M γ.position t).target = (routeLab M γ.position t).site
    · unfold offσ at hoff'
      rw [if_neg (fun h => h.1.2.1 hmove),
        if_neg (fun h => RouteLabel.not_isStart_of_isStep hstepk h.1)] at hoff'
      have hyx : y = x := Finset.mem_singleton.mp hoff'
      subst hyx
      have hsite : (routeLab M γ.position (t+1)).site = (routeLab M γ.position t).site := by
        rw [hnext, hmove]
      refine ⟨⟨hInv.1, ?_⟩, Or.inl ⟨rfl, ?_⟩⟩
      · show y.1.val ⊆ Λ.fam (refineReveal Λ.ρ₀ Λ.S₀ z) (routeLab M γ.position (t+1)).site
        rw [hsite]
        exact hInv.2
      · intro c _
        show (clusterFaceBoundary c (typicalFace Λ.t
            (Λ.center (routeLab M γ.position t).site)) : Set (Vertex d)) ⊆
          (clusterFaceBoundary c (typicalFace Λ.t
            (Λ.center (routeLab M γ.position (t+1)).site)) : Set (Vertex d))
        rw [hsite]
    · have htgtbox : (routeLab M γ.position t).target ∈ Λ.siteBox := by
        rw [← hnext]
        exact hbox (t+1) (by omega)
      have hctx : Λ.moveCtx (refineReveal Λ.ρ₀ Λ.S₀ z) (routeLab M γ.position t) x :=
        ⟨hstepk, hmove, hbox t htlt, htgtbox, hInv.1, hInv.2,
          (Λ.goodCube_iff z (hbox t htlt)).mpr (hpre t htlt),
          (Λ.goodCube_iff z htgtbox).mpr (by
            have h := hpre (t+1) (by omega)
            rw [hnext] at h
            exact h), ⟨z, rfl⟩⟩
      have htyp := hsucc'.1 hctx
      unfold offσ at hoff'
      rw [if_pos ⟨hctx, htyp⟩] at hoff'
      obtain ⟨hycard, rep, hrep, _, hysub⟩ := mem_svNext _ _ _ _ _ (Finset.mem_product.mp hoff').1
      obtain ⟨hLD, hRD, hLQ, hRQ, hsplit⟩ :=
        hgeo t htlt _ rfl hstepk hmove
      have hrepfam : rep ∈ typicalClusterFamily Λ.typ Λ.t
          (Λ.center (routeLab M γ.position t).site) z.1 := by
        rw [← hfam t htlt]
        exact hInv.2 hrep
      have hInv' : y.1.val.card = Λ.k ∧
          y.1.val ⊆ Λ.fam (refineReveal Λ.ρ₀ Λ.S₀ z) (routeLab M γ.position (t+1)).site := by
        refine ⟨hycard, ?_⟩
        rw [hnext]
        exact hysub.trans (svOffOf_subset_cand _ _ _ _ _ _)
      have hdiam : (sprinklingIntrinsicDiameter
          (sprinklingUnexploredGraph z.1 (Λ.L (routeLab M γ.position t))
            (typicalCube Λ.t (Λ.center (routeLab M γ.position t).site))
            (Λ.Fat (Λ.ρ₀ z) (routeLab M γ.position t).site))
          (sprinklingUnexploredGraph z.1 (Λ.R (routeLab M γ.position t))
            (typicalCube Λ.t (Λ.center (routeLab M γ.position t).target))
            (Λ.Fat (Λ.ρ₀ z) (routeLab M γ.position t).target))
          (Λ.src (refineReveal Λ.ρ₀ Λ.S₀ z) (routeLab M γ.position t) x.2 rep)
          (sprinklingTargetBoundary
            (Λ.fam (refineReveal Λ.ρ₀ Λ.S₀ z) (routeLab M γ.position t).target)
            (Λ.tgt (refineReveal Λ.ρ₀ Λ.S₀ z) (routeLab M γ.position t)))
          (svPivots (Λ.view (Λ.ρ₀ z) (routeLab M γ.position t) z).1 x.1.val
            (Λ.fam (refineReveal Λ.ρ₀ Λ.S₀ z) (routeLab M γ.position t).target)
            (Λ.src (refineReveal Λ.ρ₀ Λ.S₀ z) (routeLab M γ.position t) x.2)
            (Λ.tgt (refineReveal Λ.ρ₀ Λ.S₀ z) (routeLab M γ.position t))) : ℝ) ≤
          (Λ.Kdiam : ℝ) := by
        have hA : Λ.src (refineReveal Λ.ρ₀ Λ.S₀ z) (routeLab M γ.position t) x.2 rep ⊆
            sprinklingTargetBoundary x.1.val
              (Λ.src (refineReveal Λ.ρ₀ Λ.S₀ z) (routeLab M γ.position t) x.2) :=
          fun v hv => mem_sprinklingTargetBoundary _ _ hrep hv
        have hK : svDiameter (Λ.view (Λ.ρ₀ z) (routeLab M γ.position t) z).1 x.1.val
            (Λ.fam (refineReveal Λ.ρ₀ Λ.S₀ z) (routeLab M γ.position t).target)
            (Λ.src (refineReveal Λ.ρ₀ Λ.S₀ z) (routeLab M γ.position t) x.2)
            (Λ.tgt (refineReveal Λ.ρ₀ Λ.S₀ z) (routeLab M γ.position t)) ≤ Λ.Kdiam :=
          htyp.2.2.2.2
        exact Nat.cast_le.mpr (le_trans (sprinklingIntrinsicDiameter_mono _ _ hA
          (Finset.Subset.refl _) (Finset.Subset.refl _)) hK)
      have key := typical_step_clause Λ.typ Λ.t (Λ.center (routeLab M γ.position t).site)
        (Λ.center (routeLab M γ.position t).target) hmono
        (translateSites aC (chemicalCrossingSupport d r Λ.i₀) : Set (Vertex d))
        (Λ.L (routeLab M γ.position t)) (Λ.R (routeLab M γ.position t))
        (Λ.Fat (Λ.ρ₀ z) (routeLab M γ.position t).site)
        (Λ.Fat (Λ.ρ₀ z) (routeLab M γ.position t).target) hLD hRD hLQ hRQ
        (hQD _ (hbox t htlt))
        (Λ.src (refineReveal Λ.ρ₀ Λ.S₀ z) (routeLab M γ.position t) x.2)
        (Λ.tgt (refineReveal Λ.ρ₀ Λ.S₀ z) (routeLab M γ.position t))
        (Λ.fam (refineReveal Λ.ρ₀ Λ.S₀ z) (routeLab M γ.position t).target)
        (svPivots (Λ.view (Λ.ρ₀ z) (routeLab M γ.position t) z).1 x.1.val
          (Λ.fam (refineReveal Λ.ρ₀ Λ.S₀ z) (routeLab M γ.position t).target)
          (Λ.src (refineReveal Λ.ρ₀ Λ.S₀ z) (routeLab M γ.position t) x.2)
          (Λ.tgt (refineReveal Λ.ρ₀ Λ.S₀ z) (routeLab M γ.position t)))
        (by
          intro e he
          have he' : e ∈ sprinkledPivotalPairs z.1 (sprinkleOrConfiguration z.1 z.2)
              (orientedLatticePairs (Λ.Mid (routeLab M γ.position t)))
              (Λ.L (routeLab M γ.position t)) (Λ.R (routeLab M γ.position t))
              (Λ.Q (routeLab M γ.position t).site)
              (Λ.Fat (Λ.ρ₀ z) (routeLab M γ.position t).site)
              (Λ.Q (routeLab M γ.position t).target)
              (Λ.Fat (Λ.ρ₀ z) (routeLab M γ.position t).target) _ _ := he
          simp only [sprinkledPivotalPairs, sprinklingPivotalPairs, Finset.mem_filter] at he'
          exact ⟨he'.1.2.2.2.1, he'.2⟩)
        rep hrepfam (typicalCluster_subset_cube _ _ _ _ hrepfam)
        (fun v hv => hsplit x.2 (typicalRegularPatch_subset_splitFace _ _ _ _ _ _ _ hv))
        (typicalRegularPatch_subset_faceBoundary _ _ _ _ _ _ _)
        (fun C => Finset.union_subset
          (typicalRegularPatch_subset_faceBoundary _ _ _ _ _ _ _)
          (typicalRegularPatch_subset_faceBoundary _ _ _ _ _ _ _))
        hdiam (y.1.val : Set (Finset (Vertex d)))
        (fun c' hc' => hysub (Finset.mem_coe.mp hc'))
      refine ⟨hInv', Or.inr ⟨rep, hrep, ?_, key.2⟩⟩
      intro c' hc'
      obtain ⟨u, hu, v, hv, Dg, hDg, hconn⟩ := key.1 c' hc'
      refine ⟨u, hu, v, ?_, Dg, hDg, hconn⟩
      show v ∈ (clusterFaceBoundary c' (typicalFace Λ.t
        (Λ.center (routeLab M γ.position (t+1)).site)) : Set (Vertex d))
      rw [hnext]
      exact hv

end NestLayout
end NearCritical.Section10
