module

public import NearCritical.Section10RootMarkMass
public import NearCritical.Section10NormalizedSpread
public import NearCritical.Section10MergedTubeMark
public import NearCritical.Section10NormalizedOccupation

/-! The first shared physical tube entered from the common root. -/

@[expose] public section
noncomputable section

namespace NearCritical.Section10.NestLayout

open MeasureTheory
open scoped Classical

/-- The common-root pair occupation gives the entry estimate for the
first shared tube. -/
theorem firstGood_root_tube_mass_le
    {D d M : ℕ} (Λ : NestLayout D d) [LinearOrder (Finset (Vertex d))]
    (p q : unitInterval) (ρ κ : ℝ) (hκ : 0 < κ) (hρ : 1 ≤ ρ) (hM : 1 ≤ M)
    (hs : ∀ (γ : SourceRoute D M) (G : Λ.Φ) (j : ℕ) (x : Λ.X), ρ⁻¹ ≤
      localSuccessProbability p q (Λ.Bl₀ G.1 (routeLab M γ.position j))
        (bitSet G.2 (fun z => Λ.succσ G (routeLab M γ.position j) x
          (Λ.view G.1 (routeLab M γ.position j) z))))
    (hsite : ∀ s, κ⁻¹ ≤ coupledProb p q (Λ.siteEvent s))
    (γ γ' : SourceRoute D M) (z₀ : Configuration d × Configuration d) (x x' : Λ.X)
    (hbox : ∀ δ ∈ ({γ,γ'} : Finset (SourceRoute D M)), ∀ j < 2*M,
      (routeLab M δ.position j).site ∈ Λ.siteBox)
    (hpre : ∀ δ ∈ ({γ,γ'} : Finset (SourceRoute D M)), ∀ j < 2*M,
      IsPreGoodCube Λ.typ Λ.t (Λ.center (routeLab M δ.position j).site) z₀.1)
    (hcount : (Λ.k : ℝ) ≤ Λ.typ.countLower * (2*(Λ.t:ℝ))^(d-6))
    (hroot : routeLab M γ'.position 0 = routeLab M γ.position 0)
    (hnext : routeLab M γ'.position 1 = routeLab M γ.position 1) {K : ℝ} :
    let G := refineReveal Λ.ρ₀ Λ.S₀ z₀
    let ℓ := routeLab M γ.position 1
    let S := Λ.fam G ℓ.site
    let μ := (percolation d p).prod (percolation d q)
    let L := (Λ.ruleFirstGood M p q ρ κ hκ hs hsite).toNestRule.kernel
    (∀ C ∈ S, ∀ a b : Bool,
      (∑ C' ∈ S.erase C, μ.real {z | Λ.firstGoodSharedTubeMark G ℓ {C} {C'} a b z}) ≤ K) →
    markedPrefixMass p q (L γ G) (L γ' G) [.both,.both] 0 0 (x,x')
      (fun h z => if Λ.mergedTubeMark G ℓ false [.both,.both] 0 0 h z then 1 else 0) /
        ρ ^ sharedCount [.both,.both] ≤
      ρ * ((S.card:ℝ) * (((Λ.k:ℝ)/S.card)^2 * (1 + 4*K))) := by
  intro G ℓ S μ L hrow
  let ℓ₀ := routeLab M γ.position 0
  let R := Λ.S₀ G.1
  let B (δ : SourceRoute D M) (j : ℕ) := Λ.Bl₀ G.1 (routeLab M δ.position j)
  let s : List PairMove := [.both]
  have hρ₀ : 0 < ρ := zero_lt_one.trans_le hρ
  have hj : 1 < 2*M := by omega
  have hsite₀ : ℓ.site = ℓ₀.site := by
    have h := routeLab_next_site γ.position (t := 0) hj
    change ℓ.site = ℓ₀.target at h
    have he : ℓ₀.target = ℓ₀.site := by simp [ℓ₀,routeLab_zero,RouteLabel.target,RouteLabel.site]
    exact h.trans he
  have hS : S = Λ.fam G ℓ₀.site := congrArg (Λ.fam G) hsite₀
  have hctx : Λ.startCtx G ℓ₀ :=
    Λ.firstGood_route_start_context γ z₀ (hbox γ (by simp) 0 (by omega))
      (hpre γ (by simp) 0 (by omega)) hcount
  have hFresh : PairFresh (B γ) (B γ') (s ++ [.both]) 0 0 R := by
    have hne : ℓ₀ ≠ ℓ := by
      intro he
      have hh := congrArg RouteLabel.rank he
      change (routeLab M γ.position 0).rank = (routeLab M γ.position 1).rank at hh
      rw [rank_routeLab hM, rank_routeLab hM] at hh
      omega
    change Disjoint R (B γ 0 ∪ B γ' 0) ∧
      Disjoint (R ∪ (B γ 0 ∪ B γ' 0)) (B γ 1 ∪ B γ' 1) ∧ True
    have hB₀ : B γ' 0 = B γ 0 := congrArg (Λ.Bl₀ G.1) hroot
    have hB₁ : B γ' 1 = B γ 1 := congrArg (Λ.Bl₀ G.1) hnext
    rw [hB₀,hB₁,Finset.union_self,Finset.union_self]
    exact ⟨Λ.hS₀ G.1 ℓ₀,Finset.disjoint_union_left.mpr
      ⟨Λ.hS₀ G.1 ℓ,Λ.hBl₀ G.1 _ _ hne⟩,trivial⟩
  have hdR := PairFresh.disjoint_blocks (B γ) (B γ') s 0 0 R
    (PairFresh.prefix_of_append (B γ) (B γ') s [.both] 0 0 R hFresh)
  have hd : Disjoint (R ∪ mergedTraceBlocks (B γ) (B γ') s 0 0) (B γ 1) :=
    Finset.disjoint_of_subset_right Finset.subset_union_left
      (PairFresh.suffix_of_append (B γ) (B γ') s [.both] 0 0 R hFresh).1
  have hK₀ (δ : SourceRoute D M) (j : ℕ) (u v : Λ.X) (z : Configuration d × Configuration d) :
      0 ≤ L δ G j u v z :=
    stepKernel_nonneg _ _ _ ((inv_nonneg.mpr hρ₀.le).trans (hs δ G j u)) v z
  have hvalid (h : NestTrace (Λ.X × Λ.X) s.length) (z : Configuration d × Configuration d)
      (hn : mergedTraceMass (L γ G) (L γ' G) z s 0 0 (x,x') h ≠ 0) :
      h.1.1.1.val ⊆ S ∧ h.1.2.1.val ⊆ S := by
    have hp := lt_of_le_of_ne (mergedTraceMass_nonneg _ _ (hK₀ γ) (hK₀ γ') z s 0 0 (x,x') h) hn.symm
    obtain ⟨hl,hr⟩ := Λ.firstGood_frozen_prefix_valid p q ρ κ hκ hρ₀ hs hsite γ γ' z₀ z
      hbox hpre hcount s (x,x') h hdR hp
    refine ⟨(hl (by decide) hj).2,?_⟩
    have he : (routeLab M γ'.position 1).site = ℓ.site := congrArg RouteLabel.site hnext
    have hh := (hr (by decide) hj).2
    change h.1.2.1.val ⊆ Λ.fam G (routeLab M γ'.position 1).site at hh
    rwa [he] at hh
  have hrootLaw := (Λ.firstGood_common_root_normalized_mass p q ρ κ hκ hρ hs hsite γ γ' G x x'
    hroot hctx).1
  have hbound := Λ.firstGood_spread_pending_prefix_le p q ρ κ hκ hs hsite hρ₀ G γ γ' s 0 0 (x,x') R
    (fun _ _ => 1) (A := ((Λ.k:ℝ)/S.card)^2) (sq_nonneg _)
    (fun _ => isLocal_const _ 1) (fun _ _ => zero_le_one) hd
    (fun h z hn => hvalid h z (right_ne_zero_of_mul hn))
    (fun C hC C' hC' => by
      have h := hrootLaw C (hS ▸ hC) C' (hS ▸ hC')
      rw [hS] 
      exact h)
    hrow
  refine le_trans ?_ hbound
  apply div_le_div_of_nonneg_right _ (pow_nonneg hρ₀.le _)
  apply le_of_eq
  apply integral_congr_ae
  refine Filter.Eventually.of_forall fun z => ?_
  change (∑ h : (Λ.X × Λ.X) × ((Λ.X × Λ.X) × PUnit),
    (if Λ.mergedTubeMark G ℓ false [.both,.both] 0 0 h z then (1:ℝ) else 0) *
      mergedTraceMass (L γ G) (L γ' G) z [.both,.both] 0 0 (x,x') h) = _
  refine Finset.sum_congr rfl fun h _ => ?_
  let h₀ : NestTrace (Λ.X × Λ.X) s.length := (h.1,PUnit.unit)
  let e := mergedTraceAppend (Λ.X × Λ.X) s [.both]
  let y := h.2.1
  have he : e (h₀,(y,PUnit.unit)) = h := by
    dsimp only [e,h₀,y]
    cases h.2.2
    rfl
  have he' : e.symm h = (h₀,(y,PUnit.unit)) := by
    exact (congrArg e.symm he.symm).trans (e.symm_apply_apply _)
  let Q (v : NestTrace (Λ.X × Λ.X) (s ++ [PairMove.both]).length) :=
    Λ.mergedTubeMark G ℓ false (s ++ [.both]) 0 0 v z
  let W (v : NestTrace (Λ.X × Λ.X) (s ++ [PairMove.both]).length) :=
    mergedTraceMass (L γ G) (L γ' G) z (s ++ [.both]) 0 0 (x,x') v
  let P (k : NestTrace (Λ.X × Λ.X) s.length) :=
    let u := mergedTraceLast s (x,x') k
    Λ.firstGoodSharedTubeMark G ℓ u.1.1.val u.2.1.val u.1.2 u.2.2 z
  change (if Q h then (1:ℝ) else 0) * W h =
    (if P (e.symm h).1 then (1:ℝ) else 0) * W h
  rw [he']
  by_cases hh : mergedTraceMass (L γ G) (L γ' G) z s 0 0 (x,x') h₀ = 0
  · have hzero : W h = 0 :=
      (congrArg W he.symm).trans ((mergedTraceMass_snoc (L γ G) (L γ' G) z s .both
        0 0 (x,x') y h₀).trans (by rw [hh,zero_mul]))
    simp only [hzero,mul_zero]
  · have hmark := Λ.mergedTubeMark_snoc_both_of_nonzero G ℓ false (L γ G) (L γ' G)
      s 0 0 (x,x') y h₀ z (by decide) (by decide) hh
    have heq : Q (e (h₀,(y,PUnit.unit))) = P h₀ := by
      simpa only [Q,P,e,s,leftCount,rightCount,Nat.reduceAdd,Nat.reduceSub,Bool.false_eq_true,if_false] using hmark
    rw [(congrArg Q he.symm).trans heq]

end NearCritical.Section10.NestLayout
