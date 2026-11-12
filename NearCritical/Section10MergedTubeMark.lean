module

public import NearCritical.Section10HistoryMarkSigns
public import NearCritical.Section10MergedArrivalAppend
public import NearCritical.Section10FrozenRevealHistory

/-! Locate a physical tube mark in its merged prefix, and identify the
last shared row with the incoming pair and its two used signs. -/

@[expose] public section
noncomputable section

namespace NearCritical.Section10.NestLayout

open scoped Classical

/-- The tube mark read from a merged history. The indices are the rows
immediately preceding the two local moves. -/
def mergedTubeMark {D d : ℕ} (Λ : NestLayout D d) (G : Λ.Φ) (ℓ : RouteLabel D)
    (used : Bool) (s : List PairMove) (a b : ℕ) (h : NestTrace (Λ.X × Λ.X) s.length)
    (z : Configuration d × Configuration d) : Prop :=
  Λ.historyTubeMark G ℓ used (leftCount s) (rightCount s) a b
    (mergedRouteTraces s h).1 (mergedRouteTraces s h).2 z

private theorem optionTubeMark_readsOnly {d : ℕ} {X : Type*}
    (R : Finset (LBond d))
    (M : X → X → Bool → Bool → Configuration d × Configuration d → Prop)
    (hM : ∀ u v a b, ReadsOnly R (M u v a b))
    (p q : Option X) (a b : Option Bool) :
    ReadsOnly R (optionTubeMark M p q a b) := by
  cases p <;> cases q <;> cases a <;> cases b <;> first | exact hM _ _ _ _ | exact fun _ _ _ => rfl

theorem mergedTubeMark_readsOnly {D d : ℕ} (Λ : NestLayout D d) (G : Λ.Φ) (ℓ : RouteLabel D)
    (used : Bool) (s : List PairMove) (a b : ℕ) (h : NestTrace (Λ.X × Λ.X) s.length) :
    ReadsOnly (Λ.Bl₀ G.1 ℓ) (Λ.mergedTubeMark G ℓ used s a b h) := by
  unfold mergedTubeMark historyTubeMark
  exact optionTubeMark_readsOnly (Λ.Bl₀ G.1 ℓ)
    (fun (u v : ↥Λ.P) c c' => Λ.firstGoodSharedTubeMark G ℓ u.val v.val c c')
    (fun u v c c' => Λ.firstGoodSharedTubeMark_readsOnly G ℓ u.val v.val c c')
    ((routeTraceGet? (leftCount s) (mergedRouteTraces s h).1 a).map Prod.fst)
    ((routeTraceGet? (rightCount s) (mergedRouteTraces s h).2 b).map Prod.fst)
    ((routeTraceGet? (leftCount s) (mergedRouteTraces s h).1 (if used then a+1 else a)).map Prod.snd)
    ((routeTraceGet? (rightCount s) (mergedRouteTraces s h).2 (if used then b+1 else b)).map Prod.snd)

/-- Once the two moves have occurred, a fresh suffix cannot change
the mark of their tube. -/
theorem mergedTubeMark_append {D d : ℕ} (Λ : NestLayout D d) (G : Λ.Φ) (ℓ : RouteLabel D)
    (used : Bool) (s r : List PairMove) (a b : ℕ)
    (h : NestTrace (Λ.X × Λ.X) s.length) (g : NestTrace (Λ.X × Λ.X) r.length)
    (ha : a+1 < leftCount s) (hb : b+1 < rightCount s) (z : Configuration d × Configuration d) :
    Λ.mergedTubeMark G ℓ used (s ++ r) a b (mergedTraceAppend (Λ.X × Λ.X) s r (h,g)) z =
      Λ.mergedTubeMark G ℓ used s a b h z := by
  have hsa : (if used then a+1 else a) < leftCount s := by cases used <;> simp_all <;> omega
  have hsb : (if used then b+1 else b) < rightCount s := by cases used <;> simp_all <;> omega
  unfold mergedTubeMark historyTubeMark
  rw [mergedArrivalGet_left_prefix s r h g a (by omega),
    mergedArrivalGet_right_prefix s r h g b (by omega),
    mergedArrivalGet_left_prefix s r h g _ hsa, mergedArrivalGet_right_prefix s r h g _ hsb]

/-- The tube mark on an appended shared row uses the last state of each
route and the appropriate pair of signs. -/
theorem mergedTubeMark_snoc_both_of_nonzero {D d : ℕ} (Λ : NestLayout D d)
    (G : Λ.Φ) (ℓ : RouteLabel D) (used : Bool)
    (K K' : ℕ → Λ.X → Λ.X → Configuration d × Configuration d → ℝ)
    (s : List PairMove) (t t' : ℕ) (x y : Λ.X × Λ.X) (h : NestTrace (Λ.X × Λ.X) s.length)
    (z : Configuration d × Configuration d) (ha : 0 < leftCount s) (hb : 0 < rightCount s)
    (hm : mergedTraceMass K K' z s t t' x h ≠ 0) :
    let u := mergedTraceLast s x h
    Λ.mergedTubeMark G ℓ used (s ++ [.both]) (leftCount s-1) (rightCount s-1)
      (mergedTraceAppend (Λ.X × Λ.X) s [.both] (h,(y,PUnit.unit))) z =
    Λ.firstGoodSharedTubeMark G ℓ u.1.1.val u.2.1.val
      (if used then y.1.2 else u.1.2) (if used then y.2.2 else u.2.2) z := by
  intro u
  have hu : u =
      (routeTraceLast (leftCount s) x.1 (mergedRouteTraces s h).1,
        routeTraceLast (rightCount s) x.2 (mergedRouteTraces s h).2) :=
    mergedTraceLast_eq_routeTraceLast K K' z s t t' x h hm
  let g : NestTrace (Λ.X × Λ.X) ([.both] : List PairMove).length := (y,PUnit.unit)
  have hl := mergedArrivalGet_left_prefix s [.both] h g (leftCount s-1) (by omega)
  have hr := mergedArrivalGet_right_prefix s [.both] h g (rightCount s-1) (by omega)
  have hul : u.1 = routeTraceLast (leftCount s) x.1 (mergedRouteTraces s h).1 := congrArg Prod.fst hu
  have hur : u.2 = routeTraceLast (rightCount s) x.2 (mergedRouteTraces s h).2 := congrArg Prod.snd hu
  rw [routeTraceGet?_last _ x.1 _ ha, ← hul] at hl
  rw [routeTraceGet?_last _ x.2 _ hb, ← hur] at hr
  have hyl := mergedArrivalGet_left_suffix s [.both] h g 0
  have hyr := mergedArrivalGet_right_suffix s [.both] h g 0
  simp only [Nat.zero_add] at hyl hyr
  have hleft : (leftCount s - 1) + 1 = leftCount s := by omega
  have hright : (rightCount s - 1) + 1 = rightCount s := by omega
  change Λ.mergedTubeMark G ℓ used (s ++ [.both]) (leftCount s-1) (rightCount s-1)
      (mergedTraceAppend (Λ.X × Λ.X) s [.both] (h,g)) z = _
  cases used
  · simp only [mergedTubeMark,historyTubeMark,optionTubeMark,Bool.false_eq_true,if_false,hl,hr,Option.map_some]
  · simp only [mergedTubeMark,historyTubeMark,optionTubeMark,if_true,hl,hr,hleft,hright,hyl,hyr,
      leftCount,rightCount,mergedRouteTraces,routeTraceGet?,g,Option.map_some]

/-- Used-sign histories have the same admissible final nests on the
fresh bits of a fixed reveal. A positive row is a positive pending
row with the sign supplied by its output. -/
theorem firstGood_frozen_used_prefix_valid {D d M : ℕ} (Λ : NestLayout D d)
    [LinearOrder (Finset (Vertex d))] (p q : unitInterval) (ρ κ : ℝ)
    (hκ : 0 < κ) (hρ : 0 < ρ)
    (hs : ∀ (γ : SourceRoute D M) (G : Λ.Φ) (j : ℕ) (x : Λ.X), ρ⁻¹ ≤
      localSuccessProbability p q (Λ.Bl₀ G.1 (routeLab M γ.position j))
        (bitSet G.2 (fun z => Λ.succσ G (routeLab M γ.position j) x
          (Λ.view G.1 (routeLab M γ.position j) z))))
    (hsite : ∀ s, κ⁻¹ ≤ coupledProb p q (Λ.siteEvent s))
    (γ γ' : SourceRoute D M) (active : SourceRoute D M → ℕ → Bool) (z₀ z : Configuration d × Configuration d)
    (hbox : ∀ δ ∈ ({γ,γ'} : Finset (SourceRoute D M)), ∀ j < 2*M,
      (routeLab M δ.position j).site ∈ Λ.siteBox)
    (hpre : ∀ δ ∈ ({γ,γ'} : Finset (SourceRoute D M)), ∀ j < 2*M,
      IsPreGoodCube Λ.typ Λ.t (Λ.center (routeLab M δ.position j).site) z₀.1)
    (hcount : (Λ.k : ℝ) ≤ Λ.typ.countLower * (2*(Λ.t:ℝ))^(d-6))
    (s : List PairMove) (x : Λ.X × Λ.X) (h : NestTrace (Λ.X × Λ.X) s.length) :
    let G := refineReveal Λ.ρ₀ Λ.S₀ z₀
    let B (δ : SourceRoute D M) j := Λ.Bl₀ G.1 (routeLab M δ.position j)
    let K (δ : SourceRoute D M) := usedMaskedKernel (active δ)
      (Λ.firstGoodMaskBase p q ρ κ hκ hs hsite δ G (active δ))
    let Valid (δ : SourceRoute D M) j (u : Λ.X) := 0 < j → j < 2*M →
      u.1.val.card = Λ.k ∧ u.1.val ⊆ Λ.fam G (routeLab M δ.position j).site
    Disjoint (Λ.S₀ G.1) (mergedTraceBlocks (B γ) (B γ') s 0 0) →
    0 < mergedTraceMass (K γ) (K γ') z s 0 0 x h →
    Valid γ (leftCount s) (mergedTraceLast s x h).1 ∧
      Valid γ' (rightCount s) (mergedTraceLast s x h).2 := by
  intro G B K Valid hd hw
  let T := mergedTraceBlocks (B γ) (B γ') s 0 0
  let w := gluePair G.2 (T.restrict (layerVal z))
  obtain ⟨hG,hwz⟩ := Λ.firstGood_glue_fresh_reveal z₀ z T hd
  have hLocal (δ : SourceRoute D M) (j : ℕ) (u v : Λ.X) : IsLocal (B δ j) (K δ j u v) :=
    Λ.firstGood_usedKernel_isLocal p q ρ κ hκ hs hsite δ G (active δ) j u v
  have hK₀ (δ : SourceRoute D M) (j : ℕ) (u v : Λ.X) (v₀ : Configuration d × Configuration d) :
      0 ≤ K δ j u v v₀ :=
    Λ.firstGood_usedKernel_nonneg p q ρ κ hκ hs hsite hρ δ G (active δ) j u v v₀
  obtain ⟨f,hf⟩ := mergedTraceMass_isLocal (B γ) (B γ') (K γ) (K γ')
    (hLocal γ) (hLocal γ') s 0 0 x h
  have he : T.restrict (layerVal w) = T.restrict (layerVal z) := funext fun e => hwz e.val e.property
  have hm : mergedTraceMass (K γ) (K γ') w s 0 0 x h =
      mergedTraceMass (K γ) (K γ') z s 0 0 x h :=
    (hf w).trans ((congrArg f he).trans (hf z).symm)
  have hp : 0 < mergedTraceMass (K γ) (K γ') w s 0 0 x h := by
    rw [hm]
    exact hw
  have hnext (δ : SourceRoute D M) (hδ : δ ∈ ({γ,γ'} : Finset (SourceRoute D M)))
      (j : ℕ) (u v : Λ.X) (hu : Valid δ j u) (hp₀ : 0 < K δ j u v w) :
      Valid δ (j+1) v := by
    intro _ hj
    have hprew (i : ℕ) (hi : i < 2*M) :
        IsPreGoodCube Λ.typ Λ.t (Λ.center (routeLab M δ.position i).site) w.1 := by
      apply (Λ.goodCube_iff w (hbox δ hδ i hi)).mp
      rw [hG]
      exact (Λ.goodCube_iff z₀ (hbox δ hδ i hi)).mpr (hpre δ hδ i hi)
    let P := (Λ.ruleFirstGood M p q ρ κ hκ hs hsite).toNestRule.kernel δ G
    have hrow : K δ j u v w =
        if active δ j = true then P j (u.1,v.2) (v.1,false) w
        else if v.2 = false then P j (u.1,false) (v.1,false) w else 0 :=
      Λ.firstGood_usedKernel_apply p q ρ κ hκ hs hsite δ G (active δ) j u v w
    have hsign : ∃ a : Bool, 0 < P j (u.1,a) (v.1,false) w := by
      rw [hrow] at hp₀
      by_cases ha : active δ j = true
      · exact ⟨v.2, by simpa only [if_pos ha] using hp₀⟩
      · by_cases hv : v.2 = false
        · exact ⟨false, by simpa only [if_neg ha, if_pos hv] using hp₀⟩
        · simp only [if_neg ha, if_neg hv, lt_irrefl] at hp₀
    obtain ⟨a,ha⟩ := hsign
    have h := Λ.firstGood_route_next_valid δ w p q ρ κ hκ hs hsite
      (hbox δ hδ) hprew hcount j hj (u.1,a) (v.1,false)
    have hinput (hj₀ : 1 ≤ j) : u.1.val.card = Λ.k ∧
        u.1.val ⊆ Λ.fam (refineReveal Λ.ρ₀ Λ.S₀ w) (routeLab M δ.position j).site := by
      rw [hG]
      exact hu (by omega) (by omega)
    have hpos : 0 < (Λ.ruleFirstGood M p q ρ κ hκ hs hsite).toNestRule.kernel
        δ (refineReveal Λ.ρ₀ Λ.S₀ w) j (u.1,a) (v.1,false) w := by
      rw [hG]
      exact ha
    have hv := h hinput hpos
    rw [hG] at hv
    exact hv
  simpa only [Nat.zero_add] using
    mergedTraceLast_valid_of_pos (K γ) (K γ') w (hK₀ γ) (hK₀ γ')
      (Valid γ) (Valid γ') (hnext γ (by simp)) (hnext γ' (by simp)) s 0 0 x h
      (fun h₀ _ => (Nat.lt_irrefl _ h₀).elim) (fun h₀ _ => (Nat.lt_irrefl _ h₀).elim) hp


end NearCritical.Section10.NestLayout
