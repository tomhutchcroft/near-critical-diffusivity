module

public import NearCritical.Section10FirstGoodTrajectoryPieces
public import NearCritical.Section10ActualRoute
public import NearCritical.Section10BoxFaces

/-! The short-piece microscopic path for the actual lattice layout. -/

@[expose] public section
noncomputable section
namespace NearCritical.Section10

open scoped Classical

private theorem mem_box_of_crossing_supports {d r : ℕ} {i j : Fin d} (hij : i ≠ j)
    (a : Vertex d) {v : Vertex d}
    (hi : v ∈ translateSites a (chemicalCrossingSupport d r i))
    (hj : v ∈ translateSites a (chemicalCrossingSupport d r j)) :
    v ∈ translateSites a (centeredBox d r) := by
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hi
  have hx' := (mem_translateSites a _ x).mp hj
  rcases Finset.mem_union.mp hx with hx | hx
  · exact (mem_translateSites a _ x).mpr hx
  rcases Finset.mem_union.mp hx' with hx' | hx'
  · exact (mem_translateSites a _ x).mpr hx'
  have hi' := chemicalExitFace_coordinate i hx
  obtain ⟨y, hy, htip⟩ := Finset.mem_image.mp hx'
  have hcoord : x i = y i := by
    rw [← htip]
    simp [bondTip, Function.update_of_ne hij]
  have hbound := ((mem_centeredBox.mp (Finset.mem_filter.mp hy).1) i).2
  omega

/-- Every positive trajectory of an actual surviving route has a crossing
walk with the selected pieces and the exit bond retained. -/
theorem actualLayout_trajectory_pieces {D M : ℕ} [LinearOrder (Finset (Vertex (D+1)))]
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
    let G := restrictedGraph Ω (U : Set (Vertex (D+1)))
    0 < R.w γ (R.ρ z) →
    ∀ (m : ℕ) (hm : m+2 = 2*M) (f : Fin (m+1+1) → Λ.X),
    0 < trajWeight (R.kernel γ (R.ρ z)) (m+1+1) 0 (R.x₀ γ (R.ρ z)) f z →
    (k : ℝ) ≤ typ.countLower * (2 * (t : ℝ)) ^ ((D+1)-6) →
    ∃ pt v w, (∃ x ∈ chemicalBottomFace (D+1) r i, pt = aC + x) ∧
      (∃ x ∈ chemicalExitFace (D+1) r i, w = aC + x) ∧
      Λ.trajectoryExit z (f ⟨m, Nat.lt_succ_of_le (Nat.le_succ m)⟩) v w ∧ (openGraph Ω).Adj v w ∧
      ∃ (W : G.Walk pt v) (C B : ℕ → Finset (Sym2 (Vertex (D+1)))),
        (∀ j (hj : j ≤ m), Λ.trajectoryClusterPiece z.1 (f ⟨j, Nat.lt_succ_of_le (hj.trans (Nat.le_succ m))⟩) (C j)) ∧
        (∀ j (hj : j < m), Λ.trajectoryBridgePiece z (routeLab M γ.position (j+1))
          (f ⟨j, (hj.trans (Nat.lt_succ_self m)).trans (Nat.lt_succ_self (m+1))⟩) (B j)) ∧
        ∀ e ∈ W.edges, (∃ j ≤ m, e ∈ C j) ∨ ∃ j < m, e ∈ B j := by
  intro Λ aC r i U hs hsite z γ hroute R Ω G hw m hm f hf hcount
  have ht₀ : 0 < t := by omega
  have hbox : ∀ j, j < 2*M → (routeLab M γ.position j).site ∈ Λ.siteBox :=
    fun _ hj => routeLab_site_mem_box γ hroute hj
  let i' : Fin (D+1) := ⟨1, by omega⟩
  have hii' : (0 : Fin (D+1)) ≠ i' := by
    intro he
    have h := congrArg Fin.val he
    change 0 = 1 at h
    omega
  have hQdom : ∀ s ∈ Λ.siteBox,
      (Λ.Q s : Set (Vertex (D+1))) ⊆ (U : Set (Vertex (D+1))) := by
    intro s hst x hx
    have hc := fun j => siteCenter_bounds t hst j
    exact mem_box_of_crossing_supports hii' aC
      (cube_subset_support ht₀ 0 _ hc hx) (cube_subset_support ht₀ i' _ hc hx)
  have hStep : ∀ j, j < 2*M → ∀ ℓ : RouteLabel D, ℓ = routeLab M γ.position j →
      ℓ.isStep → ℓ.target ≠ ℓ.site →
      (Λ.L ℓ : Set (Vertex (D+1))) ⊆ (U : Set (Vertex (D+1))) ∧
      (Λ.R ℓ : Set (Vertex (D+1))) ⊆ (U : Set (Vertex (D+1))) ∧
      Disjoint (Λ.L ℓ : Set (Vertex (D+1))) (typicalCube t (siteCenter t ℓ.target) : Set (Vertex (D+1))) ∧
      Disjoint (Λ.R ℓ : Set (Vertex (D+1))) (typicalCube t (siteCenter t ℓ.site) : Set (Vertex (D+1))) := by
    intro j hj ℓ₀ rfl hstep hmove
    let ℓ := routeLab M γ.position j
    have htube : HasTube M ℓ := routeLab_hasTube γ.1.1 γ.2 hstep hmove
    have hsbox := hbox j hj
    have hL : Λ.L ℓ = stepL t (siteCenter t ℓ.site) (dirOf ℓ) := by
      show LOf t M ℓ = _
      unfold LOf
      rw [if_pos htube]
    have hR : Λ.R ℓ = stepR t (siteCenter t ℓ.site) (dirOf ℓ) := by
      show ROf t M ℓ = _
      unfold ROf
      rw [if_pos htube]
    have hfar := siteCenter_target t htube
    have htbox : ℓ.target ∈ siteBoxOf D M := by
      have hlt : j+1 < 2*M := by
        by_contra h
        have he : j = 2*M-1 := by omega
        have hs := hstep
        rw [he, routeLab_last hM] at hs
        exact hs
      rw [← routeLab_next_site γ.position hlt]
      exact hbox (j+1) hlt
    have hfarbound : siteCenter t ℓ.site (dirOf ℓ) + 2 * (t : ℤ) ≤
        2 * (t : ℤ) * ((M - 1 : ℕ) : ℤ) := by
      have h := (siteCenter_bounds t htbox (dirOf ℓ)).2
      rw [hfar, farCenter_apply_self] at h
      exact h
    have hsupp : stepL t (siteCenter t ℓ.site) (dirOf ℓ) ∪
        stepR t (siteCenter t ℓ.site) (dirOf ℓ) ⊆ U := by
      intro x hx
      have hc := fun i => siteCenter_bounds t hsbox i
      exact mem_box_of_crossing_supports hii' aC
        (stepLR_subset_support ht 0 (dirOf ℓ) _ hc hfarbound hx)
        (stepLR_subset_support ht i' (dirOf ℓ) _ hc hfarbound hx)
    change (Λ.L ℓ : Set (Vertex (D+1))) ⊆ _ ∧ (Λ.R ℓ : Set (Vertex (D+1))) ⊆ _ ∧
      Disjoint (Λ.L ℓ : Set (Vertex (D+1))) (typicalCube t (siteCenter t ℓ.target) : Set (Vertex (D+1))) ∧
      Disjoint (Λ.R ℓ : Set (Vertex (D+1))) (typicalCube t (siteCenter t ℓ.site) : Set (Vertex (D+1)))
    rw [hL,hR,hfar]
    exact ⟨Finset.coe_subset.mpr (Finset.subset_union_left.trans hsupp),
      Finset.coe_subset.mpr (Finset.subset_union_right.trans hsupp),
      Finset.disjoint_coe.mpr (stepL_disjoint_far_cube t _ _),
      Finset.disjoint_coe.mpr (stepR_disjoint_near_cube t _ _)⟩
  have hBot : ∀ s ∈ Λ.siteBox, s.1 = 0 →
      ∀ pt ∈ typicalFace t (siteCenter t s) (i,false),
        ∃ x ∈ chemicalBottomFace (D+1) r i, pt = aC + x := by
    intro s hst hlev pt hpt
    refine bottomFace_mem ht₀ 0 _ (fun j => siteCenter_bounds t hst j) ?_ hpt
    show siteCenter t s 0 = 0
    rw [siteCenter_zero, hlev]
    simp
  have hTop : ∀ s ∈ Λ.siteBox, s.1 = M-1 →
      ∀ y ∈ typicalFace t (siteCenter t s) (i,true),
        ∃ x ∈ chemicalExitFace (D+1) r i, bondTip (y,i) = aC + x := by
    intro s hst hlev y hy
    refine exitFace_mem ht₀ 0 _ (fun j => siteCenter_bounds t hst j) ?_ hy
    show siteCenter t s 0 = 2 * (t : ℤ) * ((M-1 : ℕ) : ℤ)
    rw [siteCenter_zero,hlev]

  exact Λ.firstGood_trajectory_pieces M hM p q ρ κ hκ hs hsite z γ hw m hm f hf aC r U
    rfl hbox hcount hQdom hStep hBot hTop

end NearCritical.Section10
