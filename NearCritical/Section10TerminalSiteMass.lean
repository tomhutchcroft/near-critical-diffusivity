module

public import NearCritical.Section10SiteCollisionMass
public import NearCritical.Section10SharedArrivalRecurrence
public import NearCritical.Section10DistinctArrivalPrefixBound
public import NearCritical.Section10ArrivalTubeGeometry
public import NearCritical.Section10RootMarkMass

@[expose] public section
noncomputable section

namespace NearCritical.Section10.NestLayout

open MeasureTheory
open scoped Classical

variable {D d M : ℕ} (Λ : NestLayout D d) [LinearOrder (Finset (Vertex d))]
  (p q : unitInterval) (ρ κ : ℝ) (hκ : 0 < κ)
  (hs : ∀ (γ : SourceRoute D M) (G : Λ.Φ) (j : ℕ) (x : Λ.X), ρ⁻¹ ≤
    localSuccessProbability p q (Λ.Bl₀ G.1 (routeLab M γ.position j))
      (bitSet G.2 (fun z => Λ.succσ G (routeLab M γ.position j) x
        (Λ.view G.1 (routeLab M γ.position j) z))))
  (hsite : ∀ s, κ⁻¹ ≤ coupledProb p q (Λ.siteEvent s))

set_option maxHeartbeats 750000 in
/-- The normalized collision mass at a common site on the terminal
schedule. A common root uses the exact initial law. A non-root site is
charged to the diagonal occupations and, for a shared arrival, its
incoming shared tube mark. -/
theorem firstGood_terminal_site_mass_le
    (hρ : 1 ≤ ρ) (hM : 1 ≤ M)
    (γ γ' : SourceRoute D M) (z₀ : Configuration d × Configuration d) (x x' : Λ.X)
    (hbox : ∀ δ ∈ ({γ,γ'} : Finset (SourceRoute D M)), ∀ i < 2*M,
      (routeLab M δ.position i).site ∈ Λ.siteBox)
    (hpre : ∀ δ ∈ ({γ,γ'} : Finset (SourceRoute D M)), ∀ i < 2*M,
      IsPreGoodCube Λ.typ Λ.t (Λ.center (routeLab M δ.position i).site) z₀.1)
    (hcount : (Λ.k : ℝ) ≤ Λ.typ.countLower * (2*(Λ.t:ℝ))^(d-6))
    (z : RSite D) (hz : z ∈ routeSites M γ.position) (hz' : z ∈ routeSites M γ'.position)
    {A H E : ℝ} (hA : 0 ≤ A) (hH : 0 ≤ H) (hE : 0 ≤ E) (hHA : H*H ≤ A) :
    let G := refineReveal Λ.ρ₀ Λ.S₀ z₀
    let K (δ : SourceRoute D M) := (Λ.ruleFirstGood M p q ρ κ hκ hs hsite).toNestRule.kernel δ G
    let a := routeArrivalRank γ.position z
    let b := routeArrivalRank γ'.position z
    let ℓ := routeLab M γ.position a
    let ℓ' := routeLab M γ'.position b
    let S := Λ.fam G z
    let t := jointRoutePrefix M γ.position γ'.position (2*M)
    let μ := (percolation d p).prod (percolation d q)
    (∀ C ∈ S, ∀ u, Λ.moveCtx G ℓ u → (∫ w, ∑ y : Λ.X, if C ∈ y.1.val then K γ a u y w else 0 ∂μ) ≤ H) →
    (∀ C ∈ S, ∀ u, Λ.moveCtx G ℓ' u → (∫ w, ∑ y : Λ.X, if C ∈ y.1.val then K γ' b u y w else 0 ∂μ) ≤ H) →
    (ℓ = ℓ' → ∀ C ∈ S, ∀ u v, Λ.moveCtx G ℓ u → Λ.moveCtx G ℓ' v →
      (∫ w, (if Λ.firstGoodSharedTubeMark G ℓ u.1.val v.1.val u.2 v.2 w then 0 else 1) *
        ((∑ y : Λ.X, if C ∈ y.1.val then K γ a u y w else 0) *
         (∑ y : Λ.X, if C ∈ y.1.val then K γ' b v y w else 0)) ∂μ) ≤ ρ*A) →
    (ℓ = ℓ' → HasTube M ℓ →
      Λ.firstGood_shared_tube_mass p q ρ κ hκ hs hsite γ γ' G (x,x') a ≤ E) →
    markedPrefixMass p q (K γ) (K γ') t 0 0 (x,x')
      (fun h _ => if mergedSiteMark Λ t a b h then 1 else 0) / ρ ^ sharedCount t ≤
      max ((Λ.k:ℝ)^2 / S.card) (E + (S.card:ℝ)*A) := by
  intro G K a b ℓ ℓ' S t μ hH1 hH1' hH2 hTube
  let Rule := (Λ.ruleFirstGood M p q ρ κ hκ hs hsite).toNestRule
  let B (δ : SourceRoute D M) i := Λ.Bl₀ G.1 (routeLab M δ.position i)
  let P := jointRoutePrefix M γ.position γ'.position
  let R := Λ.S₀ G.1
  let V := NestTrace (Λ.X × Λ.X) t.length
  have hρ₀ := zero_lt_one.trans_le hρ
  have hFresh : PairFresh (B γ) (B γ') t 0 0 R := Rule.route_pair_fresh hM γ γ' G (2*M) (2*M) 0 0
  have hDisj := PairFresh.disjoint_blocks (B γ) (B γ') t 0 0 R hFresh
  have hza := routeArrivalRank_arrives γ.position hz
  have hzb := routeArrivalRank_arrives γ'.position hz'
  rcases common_site_arrivals_root_or_positive γ.position γ'.position hz hz' with
    ⟨ha₀,hb₀,hroot⟩ | ⟨ha₀,hb₀⟩
  · have hP₀ : P 0 = [] := by simp [P,jointRoutePrefix,mergeSched]
    have hP : P 1 = [.both] :=
      (jointRoutePrefix_succ hM _ _ 0).trans
        ((congrArg (P 0 ++ ·) (if_pos hroot)).trans (by rw [hP₀,List.nil_append]))
    obtain ⟨r,hr⟩ := jointRoutePrefix_extends hM γ.position γ'.position (show 1 ≤ 2*M by omega)
    change t = P 1 ++ r at hr
    rw [hP] at hr
    have hf : PairFresh (B γ) (B γ') ([.both] ++ r) 0 0 R := hr ▸ hFresh
    have hcarry := Rule.arrival_pair_mass_suffix_le hρ₀ γ γ' G (x,x') [.both] r 0 0
      (by decide) (by decide) (fun y => (y.1.1.val ∩ y.2.1.val).Nonempty) hf
    rw [← hr] at hcarry
    change a = 0 at ha₀
    change b = 0 at hb₀
    rw [ha₀,hb₀]
    refine (le_of_eq (congrArg (fun m : ℝ => m / ρ ^ sharedCount t) ?_)).trans (hcarry.trans ?_)
    · apply markedPrefixMass_congr_of_nonzero
      intro h w _
      simp only [mergedSiteMark,Finset.Nonempty,Finset.mem_inter]
    have hs₀ := Λ.firstGood_route_start_context γ z₀ (hbox γ (by simp) 0 (by omega))
      (hpre γ (by simp) 0 (by omega)) hcount
    have hbase := (Λ.firstGood_common_root_normalized_mass p q ρ κ hκ hρ hs hsite γ γ' G x x'
      hroot.symm hs₀).2
    have hsite₀ : (routeLab M γ.position 0).site = z := by
      have h := hza.2.1
      change (routeLab M γ.position a).target = z at h
      rwa [ha₀,routeLab_zero] at h
    refine le_trans ?_ (le_max_left _ _)
    have he (h : NestTrace (Λ.X × Λ.X) ([PairMove.both] : List PairMove).length) :
        mergedArrivalStates? [.both] 0 0 h = some h.1 := rfl
    simpa only [he,Option.some.injEq,exists_eq_left',hsite₀] using hbase
  · have hta := routeArrivalRank_hasTube γ hz ha₀
    have htb := routeArrivalRank_hasTube γ' hz' hb₀
    have ha : a < 2*M := hza.1
    have hb : b < 2*M := hzb.1
    have haj := (routeLab_hasTube_clock hM γ.position ha hta).2
    have hbj := (routeLab_hasTube_clock hM γ'.position hb htb).2
    have hva (h : V) (w : Configuration d × Configuration d)
        (hn : mergedTraceMass (K γ) (K γ') w t 0 0 (x,x') h ≠ 0)
        (y : Λ.X × Λ.X) (hy : mergedArrivalStates? t a b h = some y) : y.1.1.val ⊆ S := by
      have hvalid := Λ.firstGood_recorded_arrivals_valid p q ρ κ hκ hρ₀ hs hsite γ γ' z₀ w
        hbox hpre hcount t (x,x') h hDisj hn
      have hLeft : routeTraceGet? _ (mergedRouteTraces t h).1 a = some y.1 := by
        cases hl : routeTraceGet? _ (mergedRouteTraces t h).1 a <;>
          cases hr : routeTraceGet? _ (mergedRouteTraces t h).2 b <;>
          simp only [mergedArrivalStates?,hl,hr] at hy <;>
          first
          | contradiction
          | exact congrArg (fun p : Λ.X × Λ.X => some p.1) (Option.some.inj hy)
      have hh := (hvalid.1 a y.1 hLeft haj).2
      have he := (routeLab_next_site γ.position haj).trans hza.2.1
      rwa [he] at hh
    refine le_trans ?_ (le_max_right _ _)
    by_cases hlabel : ℓ = ℓ'
    · have hab : a = b := by
        have h := congrArg RouteLabel.rank hlabel
        change (routeLab M γ.position a).rank = (routeLab M γ'.position b).rank at h
        rwa [rank_routeLab hM,rank_routeLab hM] at h
      have he : routeLab M γ.position a = routeLab M γ'.position a :=
        hlabel.trans (congrArg (routeLab M γ'.position) hab.symm)
      have hP : P (a+1) = P a ++ [.both] :=
        (jointRoutePrefix_succ hM _ _ a).trans (congrArg (P a ++ ·) (if_pos he))
      obtain ⟨r,hr⟩ := jointRoutePrefix_extends hM γ.position γ'.position (show a+1 ≤ 2*M by omega)
      change t = P (a+1) ++ r at hr
      have hf : PairFresh (B γ) (B γ') (P (a+1) ++ r) 0 0 R := hr ▸ hFresh
      have hfa : PairFresh (B γ) (B γ') (P a ++ [.both]) 0 0 R :=
        hP ▸ PairFresh.prefix_of_append (B γ) (B γ') (P (a+1)) r 0 0 R hf
      obtain ⟨hLa,hRa⟩ := jointRoutePrefix_clocks M γ.position γ'.position a
      obtain ⟨hLas,hRas⟩ := jointRoutePrefix_clocks M γ.position γ'.position (a+1)
      change leftCount (P a) = a at hLa
      change rightCount (P a) = a at hRa
      change leftCount (P (a+1)) = a+1 at hLas
      change rightCount (P (a+1)) = a+1 at hRas
      have hread : Λ.Bl₀ G.1 ℓ ⊆ mergedTraceBlocks (B γ) (B γ') (P (a+1)) 0 0 := by
        simpa only [Nat.zero_add] using
          leftBlock_subset_mergedTraceBlocks (B γ) (B γ') (P (a+1)) 0 0 a (by rw [hLas]; omega)
      have hA₁ : (a-1)+1 < leftCount (P (a+1)) := by rw [hLas]; omega
      have hA₂ : (a-1)+1 < rightCount (P (a+1)) := by rw [hRas]; omega
      let Mark (h : V) w := Λ.mergedTubeMark G ℓ false t (a-1) (a-1) h w
      refine Λ.firstGood_site_collision_of_diagonal_occupations p q ρ κ hκ hρ₀ hs hsite γ γ' G (x,x')
        t a b S (Λ.Bl₀ G.1 ℓ) Mark (fun h => Λ.mergedTubeMark_readsOnly G ℓ false t (a-1) (a-1) h)
        hva ?_ ?_
      · intro C hC
        have hcarry := Λ.firstGood_disjoint_arrival_mass_suffix_le p q ρ κ hκ hs hsite hρ₀ γ γ' G
          (P (a+1)) r (x,x') ℓ (a-1) (a-1) a a hA₁ hA₂
          (by rw [hLas]; omega) (by rw [hRas]; omega) C C hf hread
        rw [← hr] at hcarry
        rw [← hab]
        refine hcarry.trans ?_
        have hbase := Λ.firstGood_shared_arrival_pair_mass_le p q ρ κ hκ hρ₀ hs hsite γ γ' z₀
          hbox hpre hcount (P a) (x,x') (by rw [hLa]; exact ha₀) (by rw [hRa]; exact ha₀)
          (by rw [hLa]; exact haj) (by rw [hRa]; exact haj) C C (mul_nonneg hρ₀.le hA) hfa
          (by rw [hLa]; exact hasTube_target_ne hta)
          (by rw [hRa,← he]; exact hasTube_target_ne hta)
          (by
            have hh := hH2 hlabel C hC
            dsimp only [ℓ,ℓ'] at hh
            rw [← hab] at hh
            simp only [hLa,hRa]
            exact hh)
        have hcancel : ρ*A/ρ = A := by field_simp
        simp only [hLa,hRa,hcancel] at hbase
        rw [hP]
        exact hbase
      · have hcarry := Λ.firstGood_tube_mark_mass_suffix_le p q ρ κ hκ hs hsite hρ₀ γ γ' G
          (P (a+1)) r (x,x') ℓ (a-1) (a-1) hA₁ hA₂ hf hread
        rw [← hr] at hcarry
        exact hcarry.trans (hTube hlabel hta)
    · have hh := Λ.firstGood_site_collision_of_diagonal_occupations p q ρ κ hκ hρ₀ hs hsite γ γ' G (x,x')
        t a b S ∅ (fun _ _ => False) (fun _ _ _ _ => rfl) (A := A) (E := E) hva
      refine hh ?_ ?_
      · intro C hC
        have hocc := Λ.firstGood_distinct_arrival_pair_mass_le p q ρ κ hκ hs hsite hρ₀ hM
          γ γ' z₀ (x,x') hbox hpre hcount z hz hz' (2*M) C C hH ha hb hlabel
          ⟨ha₀,haj,hasTube_target_ne hta⟩ ⟨hb₀,hbj,hasTube_target_ne htb⟩
          (hH1 C hC) (hH1' C hC)
        simpa only [not_false_eq_true,true_and] using hocc.trans hHA
      · simpa only [ite_false,markedPrefixMass,zero_mul,Finset.sum_const_zero,integral_zero,zero_div] using hE

/-- Sum the normalized site collision bounds over the common sites of
the two routes on the terminal schedule. -/
theorem firstGood_terminal_site_count_mass_le
    (γ γ' : SourceRoute D M) (G : Λ.Φ) (x : Λ.X × Λ.X)
    {E : ℝ} (hE : 0 ≤ E) :
    let t := jointRoutePrefix M γ.position γ'.position (2*M)
    let S := routeSites M γ.position ∩ routeSites M γ'.position
    let K (δ : SourceRoute D M) := (Λ.ruleFirstGood M p q ρ κ hκ hs hsite).toNestRule.kernel δ G
    let Mark (z : RSite D) := mergedSiteMark Λ t (routeArrivalRank γ.position z) (routeArrivalRank γ'.position z)
    (∀ z ∈ S, markedPrefixMass p q (K γ) (K γ') t 0 0 x
      (fun h _ => if Mark z h then 1 else 0) / ρ ^ sharedCount t ≤ E) →
    markedPrefixMass p q (K γ) (K γ') t 0 0 x
      (fun h _ => (((S.filter (fun z => Mark z h)).card):ℝ)) / ρ ^ sharedCount t ≤
        2 * ((commonRouteLevels M γ.position γ'.position).card:ℝ) * E := by
  intro t S K Mark hBound
  let B (δ : SourceRoute D M) j := Λ.Bl₀ G.1 (routeLab M δ.position j)
  have hk (δ : SourceRoute D M) (j : ℕ) (u v : Λ.X) : IsLocal (B δ j) (K δ j u v) :=
    stepKernel_isLocal _ _ _ _ v
  have h := markedPrefixMass_card_filter_le p q (B γ) (B γ') (K γ) (K γ')
    (hk γ) (hk γ') t 0 0 x S (fun _ => ∅) (fun z h _ => Mark z h)
    (fun _ _ _ _ _ _ => rfl) ρ E hBound
  refine h.trans (mul_le_mul_of_nonneg_right ?_ hE)
  let S₀ := @Inter.inter _ (@Finset.instInter (RSite D)
    (@instDecidableEqProd ℕ (Fin D → ℤ) instDecidableEqNat (Classical.decEq _)))
    (routeSites M γ.position) (routeSites M γ'.position)
  have he : S = S₀ := by
    ext w
    simp only [S,S₀,Finset.mem_inter]
  rw [he]
  exact_mod_cast common_route_sites_card_le_two_levels M γ.position γ'.position

end NearCritical.Section10.NestLayout
