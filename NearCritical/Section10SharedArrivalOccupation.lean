module

public import NearCritical.Section10MergedTubeMark
public import NearCritical.Section10ActualPrefixMass

/-! The normalized H2 pair occupation on the actual shared arrival,
with the bridge mark read from the merged history. -/

@[expose] public section
noncomputable section

namespace NearCritical.Section10

open MeasureTheory
open scoped Classical

theorem mergedArrivalStates?_snoc_both {X Y : Type*} (s : List PairMove)
    (h : NestTrace (X × Y) s.length) (y : X × Y) :
    mergedArrivalStates? (s ++ [.both]) (leftCount s) (rightCount s)
      (mergedTraceAppend (X × Y) s [.both] (h,(y,PUnit.unit))) = some y := by
  have hl := mergedArrivalGet_left_suffix s [.both] h (y,PUnit.unit) 0
  have hr := mergedArrivalGet_right_suffix s [.both] h (y,PUnit.unit) 0
  simp only [Nat.zero_add] at hl hr
  dsimp only [mergedArrivalStates?]
  rw [hl,hr]
  rfl

namespace NestLayout

set_option maxHeartbeats 500000 in
/-- A prescribed pair of clusters reached by a shared row with disjoint
bridges costs the normalized H2 row bound. Both arrivals and the bridge
mark are read chronologically from the actual history. -/
theorem firstGood_shared_arrival_pair_mass_le
    {D d M : ℕ} (Λ : NestLayout D d) [LinearOrder (Finset (Vertex d))]
    (p q : unitInterval) (ρ κ : ℝ) (hκ : 0 < κ) (hρ : 0 < ρ)
    (hs : ∀ (γ : SourceRoute D M) (G : Λ.Φ) (j : ℕ) (x : Λ.X), ρ⁻¹ ≤
      localSuccessProbability p q (Λ.Bl₀ G.1 (routeLab M γ.position j))
        (bitSet G.2 (fun z => Λ.succσ G (routeLab M γ.position j) x
          (Λ.view G.1 (routeLab M γ.position j) z))))
    (hsite : ∀ s, κ⁻¹ ≤ coupledProb p q (Λ.siteEvent s))
    (γ γ' : SourceRoute D M) (z₀ : Configuration d × Configuration d)
    (hbox : ∀ δ ∈ ({γ,γ'} : Finset (SourceRoute D M)), ∀ i < 2*M,
      (routeLab M δ.position i).site ∈ Λ.siteBox)
    (hpre : ∀ δ ∈ ({γ,γ'} : Finset (SourceRoute D M)), ∀ i < 2*M,
      IsPreGoodCube Λ.typ Λ.t (Λ.center (routeLab M δ.position i).site) z₀.1)
    (hcount : (Λ.k : ℝ) ≤ Λ.typ.countLower * (2*(Λ.t:ℝ))^(d-6))
    (s : List PairMove) (x : Λ.X × Λ.X)
    (hj₀ : 0 < leftCount s) (hj'₀ : 0 < rightCount s)
    (hj : leftCount s + 1 < 2*M) (hj' : rightCount s + 1 < 2*M)
    (c c' : Finset (Vertex d)) {a : ℝ} (ha : 0 ≤ a) :
    let G := refineReveal Λ.ρ₀ Λ.S₀ z₀
    let B (δ : SourceRoute D M) i := Λ.Bl₀ G.1 (routeLab M δ.position i)
    let K (δ : SourceRoute D M) := (Λ.ruleFirstGood M p q ρ κ hκ hs hsite).toNestRule.kernel δ G
    let j := leftCount s
    let j' := rightCount s
    let ℓ := routeLab M γ.position j
    let ℓ' := routeLab M γ'.position j'
    let r := s ++ [PairMove.both]
    let μ := (percolation d p).prod (percolation d q)
    PairFresh (B γ) (B γ') r 0 0 (Λ.S₀ G.1) →
    ℓ.target ≠ ℓ.site → ℓ'.target ≠ ℓ'.site →
    (∀ u v : Λ.X, Λ.moveCtx G ℓ u → Λ.moveCtx G ℓ' v →
      (∫ z, (if Λ.firstGoodSharedTubeMark G ℓ u.1.val v.1.val u.2 v.2 z then 0 else 1) *
        ((∑ y : Λ.X, if c ∈ y.1.val then K γ j u y z else 0) *
         (∑ y : Λ.X, if c' ∈ y.1.val then K γ' j' v y z else 0)) ∂μ) ≤ a) →
    markedPrefixMass p q (K γ) (K γ') r 0 0 x (fun h z =>
      if ¬ Λ.mergedTubeMark G ℓ false r (j-1) (j'-1) h z ∧
        (∃ y, mergedArrivalStates? r j j' h = some y ∧ c ∈ y.1.1.val ∧ c' ∈ y.2.1.val)
      then 1 else 0) / ρ ^ sharedCount r ≤ a/ρ := by
  intro G B K j j' ℓ ℓ' r μ hFresh hm hm' hH2
  let R := Λ.S₀ G.1
  let Rule := (Λ.ruleFirstGood M p q ρ κ hκ hs hsite).toNestRule
  let H := NestTrace (Λ.X × Λ.X) s.length
  let u := mergedTraceLast s x
  let V (h : H) := Λ.moveCtx G ℓ (u h).1 ∧ Λ.moveCtx G ℓ' (u h).2
  let g (h : H) z := if Λ.firstGoodSharedTubeMark G ℓ (u h).1.1.val (u h).2.1.val
    (u h).1.2 (u h).2.2 z then (0:ℝ) else 1
  have hF₀ := PairFresh.prefix_of_append (B γ) (B γ') s [PairMove.both] 0 0 R hFresh
  have hd₀ := PairFresh.disjoint_blocks (B γ) (B γ') s 0 0 R hF₀
  have hd := (PairFresh.suffix_of_append (B γ) (B γ') s [PairMove.both] 0 0 R hFresh).1
  have hk (δ : SourceRoute D M) (i : ℕ) (x y : Λ.X) : IsLocal (B δ i) (K δ i x y) :=
    stepKernel_isLocal _ _ _ _ y
  have hk₀ (δ : SourceRoute D M) (i : ℕ) (x y : Λ.X) (z : Configuration d × Configuration d) :
      0 ≤ K δ i x y z :=
    stepKernel_nonneg _ _ _ ((inv_nonneg.mpr hρ.le).trans (hs δ G i x)) y z
  have hg (h : H) : IsLocal (pairMoveBlock (B γ) (B γ') .both (0+j) (0+j')) (g h) := by
    have ht := isLocal_of_readsOnly
      (Λ.firstGoodSharedTubeMark_readsOnly G ℓ (u h).1.1.val (u h).2.1.val (u h).1.2 (u h).2.2)
      (fun v : Prop => if v then (0:ℝ) else 1)
    simpa only [pairMoveBlock,Nat.zero_add] using ht.mono
      (Finset.subset_union_left : B γ j ⊆ B γ j ∪ B γ' j')
  have hocc := markedPrefixMass_shared_pair_occupation_le (fun y : Λ.X => y.1.val) p q
    (B γ) (B γ') (K γ) (K γ') (hk γ) (hk γ') (hk₀ γ) (hk₀ γ') hρ ha s 0 0 x R
    (fun _ _ => 1) V c c' g (fun _ => isLocal_const _ 1) (fun _ _ => zero_le_one) hd hg
    (fun h hV => by simpa only [Nat.zero_add] using hH2 (u h).1 (u h).2 hV.1 hV.2)
  have hcap := Rule.unmarked_prefix_mass_le_one hρ γ γ' G s x hF₀
  refine le_trans ?_ (hocc.trans ((mul_le_mul_of_nonneg_left hcap (div_nonneg ha hρ.le)).trans_eq (mul_one _)))
  apply div_le_div_of_nonneg_right _ (pow_nonneg hρ.le _)
  apply le_of_eq
  apply integral_congr_ae
  refine Filter.Eventually.of_forall fun z => Finset.sum_congr rfl fun f _ => ?_
  let e := mergedTraceAppend (Λ.X × Λ.X) s [PairMove.both]
  let h := (e.symm f).1
  let y := (e.symm f).2.1
  have he : e (h,(y,PUnit.unit)) = f := by
    have hh : (h,(y,PUnit.unit)) = e.symm f := by
      dsimp [h,y]
      rcases e.symm f with ⟨u,v,t⟩
      cases t
      rfl
    exact (congrArg e hh).trans (e.apply_symm_apply f)
  by_cases hz : mergedTraceMass (K γ) (K γ') z s 0 0 x h = 0
  · have hz' : mergedTraceMass (K γ) (K γ') z r 0 0 x f = 0 := by
      rw [← he]
      exact (mergedTraceMass_snoc _ _ _ _ _ _ _ _ _ _).trans (by rw [hz,zero_mul])
    rw [hz',mul_zero,mul_zero]
  · have hp := lt_of_le_of_ne (mergedTraceMass_nonneg _ _ (hk₀ γ) (hk₀ γ') z s 0 0 x h) (Ne.symm hz)
    obtain ⟨hl,hr⟩ := Λ.firstGood_frozen_prefix_valid p q ρ κ hκ hρ hs hsite γ γ' z₀ z
      hbox hpre hcount s x h hd₀ hp
    have hleft := hl hj₀ (by omega)
    have hright := hr hj'₀ (by omega)
    have hv : V h :=
      ⟨Λ.firstGood_route_move_context γ z₀ hj₀ hj (hbox γ (by simp)) (hpre γ (by simp))
          (u h).1 hleft.1 hleft.2 hm,
       Λ.firstGood_route_move_context γ' z₀ hj'₀ hj' (hbox γ' (by simp)) (hpre γ' (by simp))
          (u h).2 hright.1 hright.2 hm'⟩
    have hTube := Λ.mergedTubeMark_snoc_both_of_nonzero G ℓ false (K γ) (K γ') s 0 0 x y h z hj₀ hj'₀ hz
    have hArrival := mergedArrivalStates?_snoc_both s h y
    change Λ.mergedTubeMark G ℓ false r (j-1) (j'-1) (e (h,(y,PUnit.unit))) z = _ at hTube
    change mergedArrivalStates? r j j' (e (h,(y,PUnit.unit))) = some y at hArrival
    rw [he] at hTube hArrival
    simp only [Bool.false_eq_true,if_false] at hTube
    dsimp only
    simp only [hTube,hArrival,Option.some.injEq,exists_eq_left',one_mul]
    by_cases hb : Λ.firstGoodSharedTubeMark G ℓ (u h).1.1.val (u h).2.1.val
        (u h).1.2 (u h).2.2 z <;>
      by_cases hc : c ∈ y.1.1.val ∧ c' ∈ y.2.1.val <;>
      simp [g,hb,hc,hv,h,y,e,u] <;> rfl

end NestLayout
end NearCritical.Section10
