module

public import NearCritical.Section10SharedArrivalRecurrence
public import NearCritical.Section10DistinctArrivalPrefixBound
public import NearCritical.Section10ArrivalTubeGeometry
public import NearCritical.Section10RootTubeEntry

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

set_option maxHeartbeats 500000 in
/-- Uniform normalized mark bound on every shared physical tube.
The inputs are the one-row H1, H2 and H3 bounds at the frozen reveal,
a root occupancy bound, and a uniform bound on the cluster count. -/
theorem firstGood_shared_tube_mass_le
    (hρ : 1 ≤ ρ) (hρ' : ρ ≤ 9/8) (hM : 1 ≤ M)
    (γ γ' : SourceRoute D M) (z₀ : Configuration d × Configuration d) (x x' : Λ.X)
    (hbox : ∀ δ ∈ ({γ,γ'} : Finset (SourceRoute D M)), ∀ i < 2*M,
      (routeLab M δ.position i).site ∈ Λ.siteBox)
    (hpre : ∀ δ ∈ ({γ,γ'} : Finset (SourceRoute D M)), ∀ i < 2*M,
      IsPreGoodCube Λ.typ Λ.t (Λ.center (routeLab M δ.position i).site) z₀.1)
    (hcount : (Λ.k : ℝ) ≤ Λ.typ.countLower * (2*(Λ.t:ℝ))^(d-6))
    {A H K₀ N : ℝ} (hA : 0 ≤ A) (hH : 0 ≤ H) (hK : 0 ≤ K₀) (hN : 0 ≤ N)
    (hHA : H * H ≤ A) :
    let G := refineReveal Λ.ρ₀ Λ.S₀ z₀
    let L (δ : SourceRoute D M) i := routeLab M δ.position i
    let K (δ : SourceRoute D M) := (Λ.ruleFirstGood M p q ρ κ hκ hs hsite).toNestRule.kernel δ G
    let μ := (percolation d p).prod (percolation d q)
    let Shared i := i < 2*M ∧ L γ i = L γ' i ∧ HasTube M (L γ i)
    let E := ρ * (N * (A * (1+4*K₀)))
    (∀ i, Shared i → ((Λ.fam G (L γ i).site).card:ℝ) ≤ N) →
    (Shared 1 → ((Λ.k:ℝ)/(Λ.fam G (L γ 1).site).card)^2 ≤ A) →
    (∀ δ ∈ ({γ,γ'} : Finset (SourceRoute D M)), ∀ i < 2*M,
      ∀ C ∈ Λ.fam G (L δ i).target, ∀ u, Λ.moveCtx G (L δ i) u →
      (∫ z, ∑ y : Λ.X, if C ∈ y.1.val then K δ i u y z else 0 ∂μ) ≤ H) →
    (∀ i, Shared i → ∀ C ∈ Λ.fam G (L γ i).target, ∀ C' ∈ Λ.fam G (L γ i).target,
      ∀ u v, Λ.moveCtx G (L γ i) u → Λ.moveCtx G (L γ i) v →
      (∫ z, (if Λ.firstGoodSharedTubeMark G (L γ i) u.1.val v.1.val u.2 v.2 z then 0 else 1) *
        ((∑ y : Λ.X, if C ∈ y.1.val then K γ i u y z else 0) *
         (∑ y : Λ.X, if C' ∈ y.1.val then K γ' i v y z else 0)) ∂μ) ≤ ρ*A) →
    (∀ i, Shared i → ∀ u v, Λ.moveCtx G (L γ i) u → Λ.moveCtx G (L γ i) v →
      ∀ e e', e ≠ e' →
      μ.real {z | Λ.firstGoodSharedTubeMark G (L γ i) u.1.val v.1.val e e' z} ≤ 1/40) →
    (∀ i, Shared i → ∀ C ∈ Λ.fam G (L γ i).site, ∀ e e' : Bool,
      (∑ C' ∈ (Λ.fam G (L γ i).site).erase C,
        μ.real {z | Λ.firstGoodSharedTubeMark G (L γ i) {C} {C'} e e' z}) ≤ K₀) →
    ∀ i, Shared i → Λ.firstGood_shared_tube_mass p q ρ κ hκ hs hsite γ γ' G (x,x') i ≤ 3*E := by
  intro G L K μ Shared E hcard hroot hH1 hH2 hrare hrow
  let P := jointRoutePrefix M γ.position γ'.position
  let B (δ : SourceRoute D M) i := Λ.Bl₀ G.1 (L δ i)
  let Rule := (Λ.ruleFirstGood M p q ρ κ hκ hs hsite).toNestRule
  let mass := Λ.firstGood_shared_tube_mass p q ρ κ hκ hs hsite γ γ' G (x,x')
  have hρ₀ := zero_lt_one.trans_le hρ
  have hK₁ : 0 ≤ 1+4*K₀ := by linarith
  have hE : 0 ≤ E := mul_nonneg hρ₀.le (mul_nonneg hN (mul_nonneg hA hK₁))
  have hentry (i : ℕ) (hi : Shared i) (a : ℝ) (ha : 0 ≤ a) (ha' : a ≤ A) :
      ρ * (((Λ.fam G (L γ i).site).card:ℝ) * (a * (1+4*K₀))) ≤ E :=
    mul_le_mul_of_nonneg_left
      (mul_le_mul (hcard i hi) (mul_le_mul_of_nonneg_right ha' hK₁)
        (mul_nonneg ha hK₁) hN) hρ₀.le
  intro j
  change Shared j → mass j ≤ 3*E
  induction j using Nat.strong_induction_on with
  | h j ih =>
    intro hj
    obtain ⟨hjM,hcur,hTube⟩ := show Shared j from hj
    obtain ⟨hj₀,hj₁⟩ := routeLab_hasTube_clock hM γ.position hjM hTube
    let z := (L γ j).site
    let S := Λ.fam G z
    let a := routeArrivalRank γ.position z
    let b := routeArrivalRank γ'.position z
    have hz : z ∈ routeSites M γ.position := (routeLab_site γ.position hjM).1
    have hsiteEq : (routeLab M γ'.position j).site = z := congrArg RouteLabel.site hcur.symm
    have hz' : z ∈ routeSites M γ'.position := by rw [← hsiteEq]; exact (routeLab_site γ'.position hjM).1
    obtain ⟨ha,hb,_⟩ := sharedTube_predecessor hM γ.position γ'.position hj₀ hjM hcur
    have hsj : P (j+1) = P j ++ [.both] := by
      exact (jointRoutePrefix_succ hM _ _ j).trans (congrArg (P j ++ ·) (if_pos hcur))
    obtain ⟨hL,hR⟩ := jointRoutePrefix_clocks M γ.position γ'.position j
    change leftCount (P j) = j at hL
    change rightCount (P j) = j at hR
    have hFresh : PairFresh (B γ) (B γ') (P j ++ [.both]) 0 0 (Λ.S₀ G.1) :=
      hsj ▸ Rule.route_pair_fresh hM γ γ' G (j+1) (j+1) 0 0
    rcases common_site_arrivals_root_or_positive γ.position γ'.position hz hz' with
      ⟨ha₀,hb₀,hrootLabel⟩ | ⟨ha₀,hb₀⟩
    · change a = 0 at ha₀
      change b = 0 at hb₀
      have hprev : L γ a = L γ' b := by rw [ha₀,hb₀]; exact hrootLabel
      have hlag := shared_move_shared_arrival_lag hM γ.position γ'.position hj₀ hjM hcur hprev
      have hjEq : j = 1 := by
        rcases hlag with ⟨h,_⟩ | ⟨h,_,hj',_⟩
        · change a = j-1 at h
          omega
        · change a = j-2 at h
          omega
      subst j
      have hP₀ : P 0 = [] := by simp [P,jointRoutePrefix,mergeSched]
      have hP₁ : P 1 = [.both] := by
        exact (jointRoutePrefix_succ hM _ _ 0).trans
          ((congrArg (P 0 ++ ·) (if_pos hrootLabel)).trans (by rw [hP₀,List.nil_append]))
      have hP₂ : P (1+1) = [.both,.both] := hsj.trans (congrArg (· ++ [PairMove.both]) hP₁)
      have hbound := Λ.firstGood_root_tube_mass_le p q ρ κ hκ hρ hM hs hsite γ γ' z₀ x x'
        hbox hpre hcount hrootLabel.symm hcur.symm (hrow 1 hj)
      have hle : mass 1 ≤ E := by
        refine le_trans ?_ (hentry 1 hj _ (sq_nonneg _) (hroot hj))
        change markedPrefixMass p q (K γ) (K γ') (P (1+1)) 0 0 (x,x')
          (fun h z => if Λ.mergedTubeMark G (L γ 1) false (P (1+1)) 0 0 h z then 1 else 0) /
            ρ ^ sharedCount (P (1+1)) ≤ _
        rw [hP₂]
        exact hbound
      linarith
    · have hta := routeArrivalRank_hasTube γ hz ha₀
      have htb := routeArrivalRank_hasTube γ' hz' hb₀
      have haM : a < 2*M := (routeArrivalRank_arrives γ.position hz).1
      have hbM : b < 2*M := (routeArrivalRank_arrives γ'.position hz').1
      have hta' : (L γ a).target = z := (routeArrivalRank_arrives γ.position hz).2.1
      have htb' : (L γ' b).target = z := (routeArrivalRank_arrives γ'.position hz').2.1
      by_cases hprev : L γ a = L γ' b
      · have hab : a = b := by
          have hh := congrArg RouteLabel.rank hprev
          change (routeLab M γ.position a).rank = (routeLab M γ'.position b).rank at hh
          rwa [rank_routeLab hM,rank_routeLab hM] at hh
        have he : L γ a = L γ' a := hprev.trans (congrArg (L γ') hab.symm)
        have hpa : Shared a := ⟨haM,he,hta⟩
        have hArrival' : routeArrivalRank γ'.position (L γ' j).site = a := by
          rw [hsiteEq]
          exact hab.symm
        have hstep := Λ.firstGood_shared_arrival_recurrence_le p q ρ κ hκ hs hsite hρ hρ' hM
          γ γ' z₀ x x' hbox hpre hcount a j ha₀ ha hj₁ he hcur hta hTube rfl hArrival' hA
          (by simpa only [hta'] using hH2 a hpa) (hrare j hj) (hrow j hj)
        have hprevBound := ih a ha hpa
        have hfirst := hentry j hj A hA le_rfl
        change mass j ≤ _ + (2/3:ℝ) * mass a at hstep
        linarith
      · have hAo (C : Finset (Vertex d)) (hC : C ∈ S) (C' : Finset (Vertex d)) (hC' : C' ∈ S) :
          markedPrefixMass p q (K γ) (K γ') (P j) 0 0 (x,x')
            (fun h _ => if ∃ y, mergedArrivalStates? (P j) a b h = some y ∧ C ∈ y.1.1.val ∧ C' ∈ y.2.1.val
              then 1 else 0) / ρ ^ sharedCount (P j) ≤ A := by
          have hm := Λ.firstGood_distinct_arrival_pair_mass_le p q ρ κ hκ hs hsite hρ₀ hM
            γ γ' z₀ (x,x') hbox hpre hcount z hz hz' j C C' hH ha hb hprev
            ⟨ha₀,(routeLab_hasTube_clock hM _ haM hta).2,hasTube_target_ne hta⟩
            ⟨hb₀,(routeLab_hasTube_clock hM _ hbM htb).2,hasTube_target_ne htb⟩
            (hH1 γ (by simp) a haM C (by rwa [hta']))
            (hH1 γ' (by simp) b hbM C' (by rwa [htb']))
          exact hm.trans hHA
        have hbound := Λ.firstGood_tube_entry_of_arrival_occupation p q ρ κ hκ hρ₀ hs hsite
          γ γ' z₀ hbox hpre hcount (P j) (x,x')
          (by rw [hL]; exact hj₀) (by rw [hR]; exact hj₀)
          (by rw [hL]; exact hjM) (by rw [hR]; exact hjM) (fun _ _ => 1) hA
          (by rw [hL,hR]; exact hsiteEq) hFresh
          (fun _ => isLocal_const _ 1) (fun _ _ => zero_le_one)
          (by simp only [hL,hR,hsiteEq]; exact hAo)
          (by simp only [hL]; exact hrow j hj)
        have hle : mass j ≤ E := by
          refine le_trans ?_ (hentry j hj A hA le_rfl)
          simp only [hL,hR] at hbound
          change markedPrefixMass p q (K γ) (K γ') (P (j+1)) 0 0 (x,x')
            (fun h z => if Λ.mergedTubeMark G (L γ j) false (P (j+1)) (j-1) (j-1) h z then 1 else 0) /
              ρ ^ sharedCount (P (j+1)) ≤ _
          rw [hsj]
          exact hbound
        linarith

end NearCritical.Section10.NestLayout
