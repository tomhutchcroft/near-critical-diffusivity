import NearCritical.Section10ActualTrajectoryOverlap
import NearCritical.Section10TrajectoryArrival
import NearCritical.Section10IssuedPath

noncomputable section
namespace NearCritical.Section10

open scoped Classical

/-- Every positive actual trajectory gives the issued-network path and
the footprint needed to estimate its overlap with other paths. -/
theorem actualLayout_issued_trajectory {D M : ℕ} [LinearOrder (Finset (Vertex (D+1)))]
    (hD : 0 < D) (hM : 1 ≤ M) (typ : TypicalParameters) (t : ℕ) (ht : 9 ≤ t) (k : ℕ) (hk : 0 < k)
    (MOff Mcoal Kdiam : ℕ) (p q : unitInterval) (ρ κ : ℝ) (hκ : 0 < κ) :
    let Λ := actualLayout D typ t ht k hk MOff Mcoal Kdiam M
    let aC := boxCenter (D+1) t M
    let r := boxRadius t M
    let i := Λ.i₀
    let U := translateSites aC (centeredBox (D+1) r)
    ∀ (hs : ∀ (γ : SourceRoute D M) (G : Λ.Φ) (j : ℕ) (x : Λ.X), ρ⁻¹ ≤
        localSuccessProbability p q (Λ.Bl₀ G.1 (routeLab M γ.position j))
          (bitSet G.2 (fun z => Λ.succσ G (routeLab M γ.position j) x
            (Λ.view G.1 (routeLab M γ.position j) z))))
      (hsite : ∀ s, κ⁻¹ ≤ coupledProb p q (Λ.siteEvent s))
      (z : Configuration (D+1) × Configuration (D+1)) (γ : SourceRoute D M),
    lazyRouteSurvives γ.1.1 γ.2 →
    let R := (Λ.ruleFirstGood M p q ρ κ hκ hs hsite).toNestRule
    let Ω := sprinkleOrConfiguration z.1 z.2
    0 < R.w γ (R.ρ z) →
    ∀ (m : ℕ) (hm : m+2 = 2*M) (f : Fin (m+1+1) → Λ.X),
    0 < trajWeight (R.kernel γ (R.ρ z)) (m+1+1) 0 (R.x₀ γ (R.ρ z)) f z →
    (k : ℝ) ≤ typ.countLower * (2 * (t : ℝ)) ^ ((D+1)-6) →
    ∃ (F : Λ.TrajectoryFootprint γ z (U : Set (Vertex (D+1)))
        (trajectoryState (R.x₀ γ (R.ρ z)) f))
      (x y : ↥(U : Set (Vertex (D+1))))
      (W : ((openGraph Ω).induce (U : Set (Vertex (D+1)))).Walk x y),
      internalIssuedVertex U x ∈ negativeFace U i ∧
      issuedExitVertex U y i ∈ positiveFace U i ∧ Ω (y.val,i) = true ∧
      External.bondPair (y.val,i) ∈ F.edges ∧
      ∀ e ∈ (W.map (SimpleGraph.Embedding.induce _).toHom).edges, e ∈ F.edges := by
  intro Λ aC r i U hs hsite z γ hγ R Ω hw m hm f hf hcount
  obtain ⟨pt,v,w,⟨pbot,hp,hpt⟩,⟨q',hq',hwq⟩,hExit,_,W,C,B,hC,hB,hcover⟩ :=
    actualLayout_trajectory_pieces hD hM typ t ht k hk MOff Mcoal Kdiam p q ρ κ hκ
      hs hsite z γ hγ hw m hm f hf hcount
  have hpU : pt ∈ U := by
    rw [hpt]
    exact (mem_translateSites _ _ _).mpr (Finset.mem_filter.mp hp).1
  have hWP : ∀ u ∈ W.support, u ∈ U := by
    let G := microscopicPieceGraph Ω (U : Set (Vertex (D+1))) Set.univ
    have hG : restrictedGraph Ω (U : Set (Vertex (D+1))) ≤ G :=
      fun _ _ h => ⟨h.1,h.2.1,h.2.2,Set.mem_univ _⟩
    intro u hu
    exact microscopicWalk_support (W.mapLe hG) hpU u
      (by simpa only [SimpleGraph.Walk.support_mapLe_eq_support] using hu)
  have hvU : v ∈ U := hWP v W.end_mem_support
  have hCoords : ∀ y ∈ U, aC i - (r:ℤ) ≤ y i ∧ y i ≤ aC i + (r:ℤ) := by
    intro y hy
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨hlo,hhi⟩ := (mem_centeredBox.mp hu) i
    change aC i - (r:ℤ) ≤ aC i + u i ∧ aC i + u i ≤ aC i + (r:ℤ)
    omega
  have hptCoord : pt i = aC i - (r:ℤ) := by
    rw [hpt]
    change aC i + pbot i = _
    rw [(Finset.mem_filter.mp hp).2]
    omega
  have hwCoord : w i = aC i + (r:ℤ) + 1 := by
    rw [hwq]
    change aC i + q' i = _
    rw [chemicalExitFace_coordinate i hq']
    omega
  have hexOutside : bondTip (v,i) ∉ U := by
    rw [← hExit.1]
    intro h
    have hh := (hCoords w h).2
    omega
  have hbox : ∀ j, j < 2*M → (routeLab M γ.position j).site ∈ Λ.siteBox :=
    fun _ hj => routeLab_site_mem_box γ hγ hj
  have hgood := (Λ.ruleFirstGood M p q ρ κ hκ hs hsite).weight_pos γ z hw
  have hpre : ∀ j, j < 2*M → IsPreGoodCube Λ.typ Λ.t
      (Λ.center (routeLab M γ.position j).site) z.1 := fun j hj =>
    hgood _ (routeLab_site γ.position hj).1 (hbox j hj)
  have hdata := Λ.firstGood_trajectory_state_data p q ρ κ hκ hs hsite γ z
    (R.x₀ γ (R.ρ z)) hm f hbox hpre hcount hf
  let state := trajectoryState (R.x₀ γ (R.ρ z)) f
  let F : Λ.TrajectoryFootprint γ z (U : Set (Vertex (D+1))) state := {
    inside := W.edges.toFinset
    cluster := C
    bridge := B
    exitBase := v
    interior_edges := by
      intro e he
      apply Set.mem_sym2_iff_subset.mpr
      intro u hu
      exact hWP u (SimpleGraph.Walk.mem_support_of_mem_edges (List.mem_toFinset.mp he) hu)
    exit_outside := hexOutside
    covers := by
      intro e he
      rcases hcover e (List.mem_toFinset.mp he) with ⟨j,hj,h⟩ | ⟨j,hj,h⟩
      · exact Or.inl ⟨j,by omega,h⟩
      · exact Or.inr ⟨j,by omega,h⟩
    valid := fun j hj => (hdata j (by omega)).1
    arrival := fun j hj => (hdata j (by omega)).2
    cluster_ok := by
      intro j hj
      simp only [state, trajectoryState_of_lt _ _ (by omega : j < m+1+1)]
      exact hC j (by omega)
    bridge_ok := by
      intro j hj
      simp only [state, trajectoryState_of_lt _ _ (by omega : j < m+1+1)]
      exact hB j (by omega)
    exit_ok := by
      have he : 2*M-2 = m := by omega
      simp only [he, state, trajectoryState_of_lt _ _ (by omega : m < m+1+1)]
      have heq : w = bondTip (v,Λ.i₀) := hExit.1
      rw [← heq]
      exact hExit
  }
  have hG : restrictedGraph Ω (U : Set (Vertex (D+1))) ≤ openGraph Ω :=
    fun _ _ h => h.1
  let W₀ := W.mapLe hG
  have hW₀ : ∀ u ∈ W₀.support, u ∈ U := by
    intro u hu
    exact hWP u (by simpa only [W₀, SimpleGraph.Walk.support_mapLe_eq_support] using hu)
  refine ⟨F, ⟨pt,hpU⟩, ⟨v,hvU⟩, W₀.induce _ hW₀, ?_, ?_, hExit.2.1, ?_, ?_⟩
  · have hmin : ∀ u ∈ sitesPlus U, pt i ≤ u i := by
      intro u hu
      rw [hptCoord]
      exact (sitesPlus_coordinate_bounds U i hCoords u hu).1
    exact ⟨mem_boundarySites_of_min i (base_mem_sitesPlus hpU) hmin,hmin⟩
  · have hmax : ∀ u ∈ sitesPlus U, u i ≤ bondTip (v,i) i := by
      intro u hu
      rw [← hExit.1, hwCoord]
      exact (sitesPlus_coordinate_bounds U i hCoords u hu).2
    exact ⟨mem_boundarySites_of_max i (tip_mem_sitesPlus hvU i) hmax,hmax⟩
  · exact Finset.mem_insert_self _ _
  · intro e he
    rw [SimpleGraph.Walk.map_induce] at he
    change e ∈ (W.mapLe hG).edges at he
    rw [SimpleGraph.Walk.edges_mapLe_eq_edges] at he
    exact Finset.mem_insert_of_mem (List.mem_toFinset.mpr he)

end NearCritical.Section10
