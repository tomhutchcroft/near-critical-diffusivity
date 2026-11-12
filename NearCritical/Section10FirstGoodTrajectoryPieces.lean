module

public import NearCritical.Section10FirstGoodTrajectoryWalk
public import NearCritical.Section10TrajectoryPieces
public import NearCritical.Section10ShortBridgeTrace

/-! Microscopic path of a positive first-good trajectory, with the chosen short
cluster and bridge pieces retained at their physical transition times. -/

@[expose] public section
noncomputable section
namespace NearCritical.Section10.NestLayout

open scoped Classical

variable {D d : ℕ} (Λ : NestLayout D d)

/-- The finite edge set of a short walk in one representative of the nest. -/
def trajectoryClusterPiece (crit : Configuration d) (x : Λ.X)
    (C : Finset (Sym2 (Vertex d))) : Prop :=
  C = ∅ ∨ (C.card : ℝ) ≤ 2 * (Λ.typ.diameterUpper * (2 * (Λ.t : ℝ)) ^ 2) ∧
    ∃ rep ∈ x.1.val, (C : Set (Sym2 (Vertex d))) ⊆
      (restrictedGraph crit (rep : Set (Vertex d))).edgeSet

/-- The finite edge set of a short bridge in the actual sprinkling cluster. -/
def trajectoryBridgePiece (z : Configuration d × Configuration d)
    (ℓ : RouteLabel D) (x : Λ.X) (B : Finset (Sym2 (Vertex d))) : Prop :=
  let G := refineReveal Λ.ρ₀ Λ.S₀ z
  B = ∅ ∨ ℓ.isStep ∧ ℓ.target ≠ ℓ.site ∧ (B.card : ℝ) ≤ Λ.Kdiam ∧
    ∀ e ∈ B, (∀ v ∈ e, v ∈ section9SprinklingCluster z.1
      (sprinkleOrConfiguration z.1 z.2) (orientedLatticePairs (Λ.Mid ℓ))
      (Λ.L ℓ) (Λ.R ℓ) (Λ.Q ℓ.site) (Λ.Fat G.1 ℓ.site) (Λ.Q ℓ.target) (Λ.Fat G.1 ℓ.target)
      (sprinklingTargetBoundary x.1.val (Λ.src G ℓ x.2))
      (sprinklingTargetBoundary (Λ.fam G ℓ.target) (Λ.tgt G ℓ))) ∧
      e ∉ exploredEdgeSet (Λ.Q ℓ.site) (Λ.Fat G.1 ℓ.site) ∪
        exploredEdgeSet (Λ.Q ℓ.target) (Λ.Fat G.1 ℓ.target)

/-- The exit edge is open, normal to the top face, and based in one cluster. -/
def trajectoryExit (z : Configuration d × Configuration d) (x : Λ.X) (v w : Vertex d) : Prop :=
  w = bondTip (v, Λ.i₀) ∧ sprinkleOrConfiguration z.1 z.2 (v, Λ.i₀) = true ∧
    ∃ rep ∈ x.1.val, v ∈ rep

private theorem walk_edge_count_le {V : Type*} [DecidableEq V] {G : SimpleGraph V} {x y : V}
    (w : G.Walk x y) : (w.edges.toFinset.card : ℝ) ≤ w.length := by
  exact_mod_cast w.edges.toFinset_card_le.trans_eq w.length_edges

variable [LinearOrder (Finset (Vertex d))]

set_option maxHeartbeats 1600000 in
theorem firstGood_trajectory_pieces [Nontrivial (Fin d × Bool)] (M : ℕ) (hM : 1 ≤ M)
    (p q : unitInterval)
    (ϱ κ : ℝ) (hκ : 0 < κ)
    (hs : ∀ (γ : SourceRoute D M) (G : Λ.Φ) (t : ℕ) (x : Λ.X), ϱ⁻¹ ≤
      localSuccessProbability p q (Λ.Bl₀ G.1 (routeLab M γ.position t))
        (bitSet G.2 (fun z => Λ.succσ G (routeLab M γ.position t) x
          (Λ.view G.1 (routeLab M γ.position t) z))))
    (hsiteProb : ∀ s, κ⁻¹ ≤ coupledProb p q (Λ.siteEvent s))
    (z : Configuration d × Configuration d) (γ : SourceRoute D M)
    (hw : 0 < (Λ.ruleFirstGood M p q ϱ κ hκ hs hsiteProb).toNestRule.w γ
      ((Λ.ruleFirstGood M p q ϱ κ hκ hs hsiteProb).toNestRule.ρ z))
    (m : ℕ) (hm : m + 2 = 2 * M) (f : Fin (m + 1 + 1) → Λ.X)
    (hf : 0 < trajWeight ((Λ.ruleFirstGood M p q ϱ κ hκ hs hsiteProb).toNestRule.kernel γ ((Λ.ruleFirstGood M p q ϱ κ hκ hs hsiteProb).toNestRule.ρ z)) (m + 1 + 1) 0
      ((Λ.ruleFirstGood M p q ϱ κ hκ hs hsiteProb).toNestRule.x₀ γ ((Λ.ruleFirstGood M p q ϱ κ hκ hs hsiteProb).toNestRule.ρ z)) f z)
    (aC : Vertex d) (r : ℕ) (U : Set (Vertex d)) (htopeq : Λ.top = M - 1)
    (hbox : ∀ t, t < 2 * M → (routeLab M γ.position t).site ∈ Λ.siteBox)
    (hcount : (Λ.k : ℝ) ≤ Λ.typ.countLower * (2 * (Λ.t : ℝ)) ^ (d - 6))
    (hQD : ∀ s ∈ Λ.siteBox, (Λ.Q s : Set (Vertex d)) ⊆
      U)
    (hgeo : ∀ t, t < 2 * M → ∀ ℓ : RouteLabel D, ℓ = routeLab M γ.position t →
      ℓ.isStep → ℓ.target ≠ ℓ.site →
      (Λ.L ℓ : Set (Vertex d)) ⊆
        U ∧
      (Λ.R ℓ : Set (Vertex d)) ⊆
        U ∧
      Disjoint (Λ.L ℓ : Set (Vertex d)) (typicalCube Λ.t (Λ.center ℓ.target) : Set (Vertex d)) ∧
      Disjoint (Λ.R ℓ : Set (Vertex d)) (typicalCube Λ.t (Λ.center ℓ.site) : Set (Vertex d)))
    (hbot : ∀ s ∈ Λ.siteBox, s.1 = 0 →
      ∀ pt ∈ typicalFace Λ.t (Λ.center s) (Λ.i₀, false),
        ∃ x ∈ chemicalBottomFace d r Λ.i₀, pt = aC + x)
    (htop : ∀ s ∈ Λ.siteBox, s.1 = M - 1 →
      ∀ y ∈ typicalFace Λ.t (Λ.center s) (Λ.i₀, true),
        ∃ z' ∈ chemicalExitFace d r Λ.i₀, bondTip (y, Λ.i₀) = aC + z') :
    ∃ pt v w, (∃ x ∈ chemicalBottomFace d r Λ.i₀, pt = aC + x) ∧
      (∃ z' ∈ chemicalExitFace d r Λ.i₀, w = aC + z') ∧
      Λ.trajectoryExit z (f ⟨m, by omega⟩) v w ∧
      (openGraph (sprinkleOrConfiguration z.1 z.2)).Adj v w ∧
      ∃ (W : (restrictedGraph (sprinkleOrConfiguration z.1 z.2) U).Walk pt v) (C B : ℕ → Finset (Sym2 (Vertex d))),
        (∀ j (hj : j ≤ m), Λ.trajectoryClusterPiece z.1 (f ⟨j, by omega⟩) (C j)) ∧
        (∀ j (hj : j < m), Λ.trajectoryBridgePiece z (routeLab M γ.position (j+1))
          (f ⟨j, by omega⟩) (B j)) ∧
        ∀ e ∈ W.edges, (∃ j ≤ m, e ∈ C j) ∨ ∃ j < m, e ∈ B j := by
  have hgoodsite := (Λ.ruleFirstGood M p q ϱ κ hκ hs hsiteProb).weight_pos γ z hw
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
  have hk0 : ∀ t x y z', 0 ≤ ((Λ.ruleFirstGood M p q ϱ κ hκ hs hsiteProb).toNestRule.kernel γ ((Λ.ruleFirstGood M p q ϱ κ hκ hs hsiteProb).toNestRule.ρ z)) t x y z' := fun t x y z' =>
    stepKernel_nonneg _ _ _ (MeasureTheory.integral_nonneg (fun _ => by split_ifs <;> norm_num)) y z'
  have hf' : 0 < ((Λ.ruleFirstGood M p q ϱ κ hκ hs hsiteProb).toNestRule.kernel γ ((Λ.ruleFirstGood M p q ϱ κ hκ hs hsiteProb).toNestRule.ρ z)) 0 ((Λ.ruleFirstGood M p q ϱ κ hκ hs hsiteProb).toNestRule.x₀ γ ((Λ.ruleFirstGood M p q ϱ κ hκ hs hsiteProb).toNestRule.ρ z)) (f 0) z *
      trajWeight ((Λ.ruleFirstGood M p q ϱ κ hκ hs hsiteProb).toNestRule.kernel γ ((Λ.ruleFirstGood M p q ϱ κ hκ hs hsiteProb).toNestRule.ρ z)) (m + 1) 1 (f 0) (Fin.tail f) z := hf
  have hrest0 : 0 ≤ trajWeight ((Λ.ruleFirstGood M p q ϱ κ hκ hs hsiteProb).toNestRule.kernel γ ((Λ.ruleFirstGood M p q ϱ κ hκ hs hsiteProb).toNestRule.ρ z)) (m + 1) 1 (f 0) (Fin.tail f) z :=
    trajWeight_nonneg _ hk0 _ _ _ _ z
  have hk00 : 0 < ((Λ.ruleFirstGood M p q ϱ κ hκ hs hsiteProb).toNestRule.kernel γ ((Λ.ruleFirstGood M p q ϱ κ hκ hs hsiteProb).toNestRule.ρ z)) 0 ((Λ.ruleFirstGood M p q ϱ κ hκ hs hsiteProb).toNestRule.x₀ γ ((Λ.ruleFirstGood M p q ϱ κ hκ hs hsiteProb).toNestRule.ρ z)) (f 0) z := by
    rcases (hk0 0 ((Λ.ruleFirstGood M p q ϱ κ hκ hs hsiteProb).toNestRule.x₀ γ ((Λ.ruleFirstGood M p q ϱ κ hκ hs hsiteProb).toNestRule.ρ z)) (f 0) z).lt_or_eq with h | h
    · exact h
    · rw [← h, zero_mul] at hf'
      exact absurd hf' (lt_irrefl _)
  have hrest : 0 < trajWeight ((Λ.ruleFirstGood M p q ϱ κ hκ hs hsiteProb).toNestRule.kernel γ ((Λ.ruleFirstGood M p q ϱ κ hκ hs hsiteProb).toNestRule.ρ z)) (m + 1) 1 (f 0) (Fin.tail f) z := by
    rcases hrest0.lt_or_eq with h | h
    · exact h
    · rw [← h, mul_zero] at hf'
      exact absurd hf' (lt_irrefl _)
  have hInv1 : ((f 0).1.val.card = Λ.k ∧ (f 0).1.val ⊆ Λ.fam (refineReveal Λ.ρ₀ Λ.S₀ z) (routeLab M γ.position (0+1)).site) := by
    obtain ⟨_, hoffR⟩ := (Λ.ruleFirstGood M p q ϱ κ hκ hs hsiteProb).kernel_pos γ z 0 _ (f 0) hk00
    have hoff := Λ.offFirstGood_subset _ _ _ _ hoffR
    have hoff' : (f 0) ∈ Λ.offσ (refineReveal Λ.ρ₀ Λ.S₀ z) (routeLab M γ.position 0)
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
    show (f 0).1.val ⊆ Λ.fam (refineReveal Λ.ρ₀ Λ.S₀ z) (routeLab M γ.position (0+1)).site
    rw [hsite1]
    exact hsub
  have hbottom : ∀ (y : Λ.X) (rep : Finset (Vertex d)), (y.1.val.card = Λ.k ∧ y.1.val ⊆ Λ.fam (refineReveal Λ.ρ₀ Λ.S₀ z) (routeLab M γ.position (0+1)).site) →
      rep ∈ (y.1.val : Set (Finset (Vertex d))) →
      ∃ pt ∈ (clusterFaceBoundary rep (typicalFace Λ.t (Λ.center (routeLab M γ.position (0+1)).site)) : Set (Vertex d)), ∃ x ∈ chemicalBottomFace d r Λ.i₀, pt = aC + x := by
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
  have hexit : ∀ x y : Λ.X, (1 ≤ 2 * M - 1 ∧ (x.1.val.card = Λ.k ∧ x.1.val ⊆ Λ.fam (refineReveal Λ.ρ₀ Λ.S₀ z) (routeLab M γ.position (2 * M - 1)).site)) →
      0 < ((Λ.ruleFirstGood M p q ϱ κ hκ hs hsiteProb).toNestRule.kernel γ ((Λ.ruleFirstGood M p q ϱ κ hκ hs hsiteProb).toNestRule.ρ z)) (2 * M - 1) x y z →
      ∃ c ∈ (x.1.val : Set (Finset (Vertex d))), ∀ pt ∈ (clusterFaceBoundary c (typicalFace Λ.t (Λ.center (routeLab M γ.position (2 * M - 1)).site)) : Set (Vertex d)),
        ∃ v w, ((∃ z' ∈ chemicalExitFace d r Λ.i₀, w = aC + z') ∧ Λ.trajectoryExit z x v w) ∧
          (openGraph (sprinkleOrConfiguration z.1 z.2)).Adj v w ∧
          ∃ (W : (restrictedGraph (sprinkleOrConfiguration z.1 z.2) U).Walk pt v) (C : Finset (Sym2 (Vertex d))),
            Λ.trajectoryClusterPiece z.1 x C ∧ ∀ e ∈ W.edges, e ∈ C := by
    intro x y hInvT hk
    have hInv := hInvT.2
    obtain ⟨hsucc, _⟩ := (Λ.ruleFirstGood M p q ϱ κ hκ hs hsiteProb).kernel_pos γ z _ x y hk
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
        U :=
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
    refine ⟨rep, hrep, fun pt hpt => ?_⟩
    obtain ⟨W, hW⟩ := (typicalCluster_boundary_connection Λ.typ Λ.t _ z.1 hrepfam
      (Finset.mem_coe.mp hpt) hyvbd).exists_walk
    let U := W.mapLe (restrictedGraph_mono_of_le hmono hrepD)
    refine ⟨yv, bondTip (yv, Λ.i₀), ⟨⟨z', hz', htip⟩, rfl, hopen, rep, hrep, hyvrep⟩,
      ⟨(yv, Λ.i₀), hopen, Or.inl ⟨rfl, rfl⟩⟩,
      U, W.edges.toFinset, Or.inr ⟨(walk_edge_count_le W).trans hW, rep, hrep, ?_⟩, ?_⟩
    · exact fun e he => W.edges_subset_edgeSet (List.mem_toFinset.mp he)
    · intro e he
      exact List.mem_toFinset.mpr (by simpa only [U, SimpleGraph.Walk.edges_mapLe_eq_edges] using he)
  have hstep : ∀ t, t < 2 * M - 1 → ∀ x y : Λ.X, (1 ≤ t ∧ (x.1.val.card = Λ.k ∧ x.1.val ⊆ Λ.fam (refineReveal Λ.ρ₀ Λ.S₀ z) (routeLab M γ.position (t)).site)) →
      0 < ((Λ.ruleFirstGood M p q ϱ κ hκ hs hsiteProb).toNestRule.kernel γ ((Λ.ruleFirstGood M p q ϱ κ hκ hs hsiteProb).toNestRule.ρ z)) t x y z →
      (1 ≤ t + 1 ∧ (y.1.val.card = Λ.k ∧ y.1.val ⊆ Λ.fam (refineReveal Λ.ρ₀ Λ.S₀ z) (routeLab M γ.position (t+1)).site)) ∧
      ∀ c' ∈ (y.1.val : Set (Finset (Vertex d))), ∃ c ∈ (x.1.val : Set (Finset (Vertex d))),
        ∀ pt ∈ (clusterFaceBoundary c (typicalFace Λ.t (Λ.center (routeLab M γ.position (t)).site)) : Set (Vertex d)), ∃ v ∈ (clusterFaceBoundary c' (typicalFace Λ.t (Λ.center (routeLab M γ.position (t+1)).site)) : Set (Vertex d)),
          ∃ (W : (restrictedGraph (sprinkleOrConfiguration z.1 z.2) U).Walk pt v) (C B : Finset (Sym2 (Vertex d))),
          Λ.trajectoryClusterPiece z.1 x C ∧ Λ.trajectoryBridgePiece z (routeLab M γ.position t) x B ∧
            ∀ e ∈ W.edges, e ∈ C ∨ e ∈ B := by
    intro t ht2 x y hInvT hk
    have ht1 := hInvT.1
    have hInv := hInvT.2
    obtain ⟨hsucc, hoffR⟩ := (Λ.ruleFirstGood M p q ϱ κ hκ hs hsiteProb).kernel_pos γ z t x y hk
    have hoff := Λ.offFirstGood_subset _ _ _ _ hoffR
    suffices core : (y.1.val.card = Λ.k ∧ y.1.val ⊆ Λ.fam (refineReveal Λ.ρ₀ Λ.S₀ z) (routeLab M γ.position (t+1)).site) ∧
        ∀ c' ∈ (y.1.val : Set (Finset (Vertex d))), ∃ c ∈ (x.1.val : Set (Finset (Vertex d))),
          ∀ pt ∈ (clusterFaceBoundary c (typicalFace Λ.t (Λ.center (routeLab M γ.position (t)).site)) : Set (Vertex d)), ∃ v ∈ (clusterFaceBoundary c' (typicalFace Λ.t (Λ.center (routeLab M γ.position (t+1)).site)) : Set (Vertex d)),
            ∃ (W : (restrictedGraph (sprinkleOrConfiguration z.1 z.2) U).Walk pt v) (C B : Finset (Sym2 (Vertex d))),
          Λ.trajectoryClusterPiece z.1 x C ∧ Λ.trajectoryBridgePiece z (routeLab M γ.position t) x B ∧
            ∀ e ∈ W.edges, e ∈ C ∨ e ∈ B from
      ⟨⟨by omega, core.1⟩, core.2⟩
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
      refine ⟨⟨hInv.1, ?_⟩, fun c' hc' => ⟨c', hc', fun pt hpt =>
        ⟨pt, ?_, SimpleGraph.Walk.nil, ∅, ∅, Or.inl rfl, Or.inl rfl, fun e he => by simp at he⟩⟩⟩
      · show y.1.val ⊆ Λ.fam (refineReveal Λ.ρ₀ Λ.S₀ z) (routeLab M γ.position (t+1)).site
        rw [hsite]
        exact hInv.2
      · show pt ∈ (clusterFaceBoundary c' (typicalFace Λ.t (Λ.center (routeLab M γ.position (t+1)).site)) : Set (Vertex d))
        rw [hsite]
        exact hpt
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
      obtain ⟨hLD, hRD, hLQ, hRQ⟩ :=
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
      have hrepD : (rep : Set (Vertex d)) ⊆ U :=
        fun v hv => hQD _ (hbox t htlt) (Finset.mem_coe.mpr
          (typicalCluster_subset_cube _ _ _ _ hrepfam (Finset.mem_coe.mp hv)))
      let ℓ := routeLab M γ.position t
      let G := refineReveal Λ.ρ₀ Λ.S₀ z
      refine ⟨hInv', fun c' hc' => ⟨rep, Finset.mem_coe.mpr hrep, fun pt hpt => ?_⟩⟩
      obtain ⟨x0, hx0, yv, hyv, W2, hW2, hsupport, havoid⟩ :=
        offspring_short_bridge_trace z.1 z.2 _ (Λ.L ℓ) (Λ.R ℓ) (Λ.Q ℓ.site)
          (Λ.Fat G.1 ℓ.site) (Λ.Q ℓ.target) (Λ.Fat G.1 ℓ.target)
          hLD hRD hLQ hRQ (orientedLatticePairs (Λ.Mid ℓ)) (Λ.src G ℓ x.2 rep)
          (sprinklingTargetBoundary x.1.val (Λ.src G ℓ x.2))
          (Λ.fam G ℓ.target) (Λ.tgt G ℓ) (hysub (Finset.mem_coe.mp hc')) hdiam
      have hx0bd : x0 ∈ clusterFaceBoundary rep
          (typicalFace Λ.t (Λ.center (routeLab M γ.position t).site)) :=
        typicalRegularPatch_subset_faceBoundary _ _ _ _ _ _ _ hx0
      obtain ⟨W1, hW1⟩ := (typicalCluster_boundary_connection Λ.typ Λ.t _ z.1 hrepfam
        (Finset.mem_coe.mp hpt) hx0bd).exists_walk
      let U := W1.mapLe (restrictedGraph_mono_of_le hmono hrepD)
      have hyvbd : yv ∈ clusterFaceBoundary c'
          (typicalFace Λ.t (Λ.center (routeLab M γ.position t).target)) :=
        (Finset.union_subset (typicalRegularPatch_subset_faceBoundary _ _ _ _ _ _ _)
          (typicalRegularPatch_subset_faceBoundary _ _ _ _ _ _ _)) hyv
      refine ⟨yv, ?_, U.append W2, W1.edges.toFinset, W2.edges.toFinset,
        Or.inr ⟨(walk_edge_count_le W1).trans hW1, rep, hrep, ?_⟩,
        Or.inr ⟨hstepk, hmove, (walk_edge_count_le W2).trans hW2, ?_⟩, ?_⟩
      · show yv ∈ (clusterFaceBoundary c' (typicalFace Λ.t (Λ.center (routeLab M γ.position (t+1)).site)) : Set (Vertex d))
        rw [hnext]
        exact Finset.mem_coe.mpr hyvbd
      · exact fun e he => W1.edges_subset_edgeSet (List.mem_toFinset.mp he)
      · intro e he
        have he' := List.mem_toFinset.mp he
        exact ⟨fun v hv => hsupport v (SimpleGraph.Walk.mem_support_of_mem_edges he' hv), havoid e he'⟩
      · intro e he
        rw [SimpleGraph.Walk.edges_append, List.mem_append] at he
        rcases he with he | he
        · exact Or.inl (List.mem_toFinset.mpr (by simpa only [U, SimpleGraph.Walk.edges_mapLe_eq_edges] using he))
        · exact Or.inr (List.mem_toFinset.mpr he)
  obtain ⟨c, hc, hwalk⟩ := trajectory_walk_pieces (restrictedGraph (sprinkleOrConfiguration z.1 z.2) U)
    (openGraph (sprinkleOrConfiguration z.1 z.2)) ((Λ.ruleFirstGood M p q ϱ κ hκ hs hsiteProb).toNestRule.kernel γ ((Λ.ruleFirstGood M p q ϱ κ hκ hs hsiteProb).toNestRule.ρ z)) hk0 z
    (fun x : Λ.X => (x.1.val : Set (Finset (Vertex d))))
    (fun t C => (clusterFaceBoundary C (typicalFace Λ.t (Λ.center (routeLab M γ.position (t)).site)) : Set (Vertex d)))
    (fun t x => 1 ≤ t ∧ (x.1.val.card = Λ.k ∧ x.1.val ⊆ Λ.fam (refineReveal Λ.ρ₀ Λ.S₀ z) (routeLab M γ.position (t)).site))
    (fun _ => Λ.trajectoryClusterPiece z.1) (fun t => Λ.trajectoryBridgePiece z (routeLab M γ.position t))
    (fun x v w => (∃ z' ∈ chemicalExitFace d r Λ.i₀, w = aC + z') ∧ Λ.trajectoryExit z x v w) (2 * M - 1) hexit hstep
    m 1 (f 0) (Fin.tail f) (by omega) ⟨le_refl 1, hInv1⟩ hrest
  obtain ⟨pt, hpt, xb, hxb, hptx⟩ := hbottom (f 0) c hInv1 hc
  obtain ⟨v,w,⟨hw1,he⟩,hadj,W,C,B,hC,hB,hW⟩ := hwalk pt hpt
  have hstate (j : ℕ) (hj : j ≤ m) :
      trajInput (m+1) (f 0) (Fin.tail f) j = f ⟨j, by omega⟩ := by
    cases j with
    | zero => rfl
    | succ j => exact trajInput_eq_output _ _ _ j (by omega)
  refine ⟨pt,v,w,⟨xb,hxb,hptx⟩,hw1,?_,hadj,W,C,B,?_,?_,hW⟩
  · rw [hstate m le_rfl] at he
    exact he
  · intro j hj
    simpa only [hstate j hj] using hC j hj
  · intro j hj
    simpa only [hstate j hj.le, Nat.add_comm 1 j] using hB j hj

end NearCritical.Section10.NestLayout
