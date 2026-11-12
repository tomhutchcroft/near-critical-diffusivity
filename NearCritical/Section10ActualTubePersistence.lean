module

public import NearCritical.Section10MergedTubeMark
public import NearCritical.Section10HistoryTubeMass
public import NearCritical.Section10NormalizedPersistence
public import NearCritical.Section10NormalizedOccupation

/-! Persistence of the two actual chronological tube marks at a fixed
reveal. The later tube contracts the normalized mass of the earlier one. -/

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

/-- On a shared physical move, the histories marked both on an earlier
tube and on the current tube have at most two thirds of the normalized
mass of the earlier mark. This statement uses the original pending-sign
histories in both terms. -/
theorem firstGood_frozen_two_tube_mass_le
    (hρ : 1 ≤ ρ) (hρ' : ρ ≤ 9/8) (hM : 1 ≤ M)
    (γ γ' : SourceRoute D M) (z₀ : Configuration d × Configuration d)
    (hbox : ∀ δ ∈ ({γ,γ'} : Finset (SourceRoute D M)), ∀ i < 2*M,
      (routeLab M δ.position i).site ∈ Λ.siteBox)
    (hpre : ∀ δ ∈ ({γ,γ'} : Finset (SourceRoute D M)), ∀ i < 2*M,
      IsPreGoodCube Λ.typ Λ.t (Λ.center (routeLab M δ.position i).site) z₀.1)
    (hcount : (Λ.k : ℝ) ≤ Λ.typ.countLower * (2*(Λ.t:ℝ))^(d-6))
    (s : List PairMove) (x x' : Λ.X) (ℓ₀ : RouteLabel D) (a b : ℕ)
    (ha : a+1 < leftCount s) (hb : b+1 < rightCount s)
    (ha₀ : routeSignDraw γ (a+1) = true) (hb₀ : routeSignDraw γ' (b+1) = true) :
    let G := refineReveal Λ.ρ₀ Λ.S₀ z₀
    let B (δ : SourceRoute D M) i := Λ.Bl₀ G.1 (routeLab M δ.position i)
    let K (δ : SourceRoute D M) := (Λ.ruleFirstGood M p q ρ κ hκ hs hsite).toNestRule.kernel δ G
    let j := leftCount s
    let j' := rightCount s
    let ℓ := routeLab M γ.position j
    let ℓ' := routeLab M γ'.position j'
    let P used r (h : NestTrace (Λ.X × Λ.X) r.length) z :=
      Λ.mergedTubeMark G ℓ₀ used r a b h z
    let Q used (h : NestTrace (Λ.X × Λ.X) (s ++ [PairMove.both]).length) z :=
      Λ.mergedTubeMark G ℓ used (s ++ [PairMove.both]) (j-1) (j'-1) h z
    PairFresh (B γ) (B γ') (s ++ [PairMove.both]) 0 0 (Λ.S₀ G.1) →
    Λ.Bl₀ G.1 ℓ₀ ⊆ mergedTraceBlocks (B γ) (B γ') s 0 0 →
    j+1 < 2*M → j'+1 < 2*M →
    ℓ.target ≠ ℓ.site → ℓ'.target ≠ ℓ'.site →
    routeSignDraw γ j = true → routeSignDraw γ' j' = true →
    (∀ u v : Λ.X, Λ.moveCtx G ℓ u → Λ.moveCtx G ℓ' v → ∀ c c', c ≠ c' →
      ((percolation d p).prod (percolation d q)).real
        {z | Λ.firstGoodSharedTubeMark G ℓ u.1.val v.1.val c c' z} ≤ 1/40) →
    markedPrefixMass p q (K γ) (K γ') (s ++ [PairMove.both]) 0 0 (x,x')
      (fun h z => if P false (s ++ [PairMove.both]) h z ∧ Q false h z then 1 else 0) /
        ρ ^ sharedCount (s ++ [PairMove.both]) ≤
      (2/3:ℝ) * (markedPrefixMass p q (K γ) (K γ') s 0 0 (x,x')
        (fun h z => if P false s h z then 1 else 0) / ρ ^ sharedCount s) := by
  intro G B K j j' ℓ ℓ' P Q hFresh hRead hj hj' hm hm' hactive hactive' hrare
  let R := Λ.S₀ G.1
  let L (δ : SourceRoute D M) := usedMaskedKernel (routeSignDraw δ)
    (Λ.firstGoodMaskBase p q ρ κ hκ hs hsite δ G (routeSignDraw δ))
  let u₀ : Λ.X × Λ.X := ((x.1,false),(x'.1,false))
  let r := s ++ [PairMove.both]
  have hdR := PairFresh.disjoint_blocks (B γ) (B γ') r 0 0 R hFresh
  have hFresh₀ := PairFresh.prefix_of_append (B γ) (B γ') s [PairMove.both] 0 0 R hFresh
  have hdR₀ := PairFresh.disjoint_blocks (B γ) (B γ') s 0 0 R hFresh₀
  have hd := (PairFresh.suffix_of_append (B γ) (B γ') s [PairMove.both] 0 0 R hFresh).1
  have hja : (j-1)+1 = j := by dsimp [j]; omega
  have hjb : (j'-1)+1 = j' := by dsimp [j']; omega
  have hcountL : leftCount r = j+1 := by
    have h (m : List PairMove) : leftCount (m ++ [PairMove.both]) = leftCount m + 1 := by
      induction m with
      | nil => rfl
      | cons k m ih => cases k <;> simp only [List.cons_append,leftCount,ih]
    exact h s
  have hcountR : rightCount r = j'+1 := by
    have h (m : List PairMove) : rightCount (m ++ [PairMove.both]) = rightCount m + 1 := by
      induction m with
      | nil => rfl
      | cons k m ih => cases k <;> simp only [List.cons_append,rightCount,ih]
    exact h s
  have hprev :
      markedPrefixMass p q (K γ) (K γ') s 0 0 (x,x') (fun h z => if P false s h z then 1 else 0) =
      markedPrefixMass p q (L γ) (L γ') s 0 0 u₀ (fun h z => if P true s h z then 1 else 0) := by
    apply integral_congr_ae
    refine Filter.Eventually.of_forall fun z => ?_
    exact Λ.firstGood_frozen_tube_marks_eq_used p q ρ κ hκ hs hsite γ γ' z₀ z hM
      hbox hpre hcount s x x' false false (fun _ : Unit => ℓ₀) (fun _ => a) (fun _ => b)
      (fun F => if F () then 1 else 0) (fun _ => ha) (fun _ => hb)
      (fun _ => ha₀) (fun _ => hb₀) hdR₀
  have hpair :
      markedPrefixMass p q (K γ) (K γ') r 0 0 (x,x')
        (fun h z => if P false r h z ∧ Q false h z then 1 else 0) =
      markedPrefixMass p q (L γ) (L γ') r 0 0 u₀
        (fun h z => if P true r h z ∧ Q true h z then 1 else 0) := by
    apply integral_congr_ae
    refine Filter.Eventually.of_forall fun z => ?_
    exact Λ.firstGood_frozen_tube_marks_eq_used p q ρ κ hκ hs hsite γ γ' z₀ z hM
      hbox hpre hcount r x x' false false (fun c : Bool => if c then ℓ else ℓ₀)
      (fun c => if c then j-1 else a) (fun c => if c then j'-1 else b)
      (fun F => if F false ∧ F true then 1 else 0)
      (fun c => by cases c <;> simp [hcountL,hja] <;> dsimp [j] <;> omega)
      (fun c => by cases c <;> simp [hcountR,hjb] <;> dsimp [j'] <;> omega)
      (fun c => by cases c <;> simp [ha₀,hja,hactive])
      (fun c => by cases c <;> simp [hb₀,hjb,hactive']) hdR
  let F (h : NestTrace (Λ.X × Λ.X) s.length) z := if P true s h z then (1:ℝ) else 0
  let E (h : NestTrace (Λ.X × Λ.X) s.length) (y : Λ.X × Λ.X) z :=
    let u := mergedTraceLast s u₀ h
    if Λ.moveCtx G ℓ u.1 ∧ Λ.moveCtx G ℓ' u.2 ∧
        Λ.firstGoodSharedTubeMark G ℓ u.1.1.val u.2.1.val y.1.2 y.2.2 z then (1:ℝ) else 0
  have hF (h : NestTrace (Λ.X × Λ.X) s.length) :
      IsLocal (R ∪ mergedTraceBlocks (B γ) (B γ') s 0 0) (F h) :=
    (isLocal_of_readsOnly (Λ.mergedTubeMark_readsOnly G ℓ₀ true s a b h)
      (fun v : Prop => if v then (1:ℝ) else 0)).mono (hRead.trans Finset.subset_union_right)
  have hF₀ (h : NestTrace (Λ.X × Λ.X) s.length) (z : Configuration d × Configuration d) :
      0 ≤ F h z := by unfold F; split_ifs <;> norm_num
  have hcontract := Λ.firstGood_shared_persistence_normalized_le p q ρ κ hκ hs hsite hρ hρ'
    G γ γ' (routeSignDraw γ) (routeSignDraw γ') s 0 0 u₀ R F hF hF₀
      (by simpa only [Nat.zero_add] using hactive)
      (by simpa only [Nat.zero_add] using hactive') hd
      (by simpa only [Nat.zero_add] using hrare)
  have heq :
      markedPrefixMass p q (L γ) (L γ') r 0 0 u₀
        (fun h z => if P true r h z ∧ Q true h z then 1 else 0) =
      markedPrefixMass p q (L γ) (L γ') r 0 0 u₀ (fun h z =>
        let v := (mergedTraceAppend (Λ.X × Λ.X) s [PairMove.both]).symm h
        F v.1 z * E v.1 v.2.1 z) := by
    change markedPrefixMass p q (L γ) (L γ') (s ++ [PairMove.both]) 0 0 u₀
        (fun h z => if P true (s ++ [PairMove.both]) h z ∧ Q true h z then 1 else 0) =
      markedPrefixMass p q (L γ) (L γ') (s ++ [PairMove.both]) 0 0 u₀ (fun h z =>
        let v := (mergedTraceAppend (Λ.X × Λ.X) s [PairMove.both]).symm h
        F v.1 z * E v.1 v.2.1 z)
    rw [markedPrefixMass_snoc p q (L γ) (L γ') s .both 0 0 u₀
      (fun h y z => F h z * E h y z)]
    have hform : (fun h : NestTrace (Λ.X × Λ.X) (s ++ [PairMove.both]).length => fun z =>
        if P true (s ++ [PairMove.both]) h z ∧ Q true h z then (1:ℝ) else 0) =
        (fun h z => let g := (mergedTraceAppend (Λ.X × Λ.X) s [PairMove.both]).symm h
          if P true (s ++ [PairMove.both]) (mergedTraceAppend (Λ.X × Λ.X) s [PairMove.both] (g.1,(g.2.1,PUnit.unit))) z ∧
              Q true (mergedTraceAppend (Λ.X × Λ.X) s [PairMove.both] (g.1,(g.2.1,PUnit.unit))) z then 1 else 0) := by
      funext h z
      let e := mergedTraceAppend (Λ.X × Λ.X) s [PairMove.both]
      have he : ((e.symm h).1,((e.symm h).2.1,PUnit.unit)) = e.symm h := by
        rcases e.symm h with ⟨g,y,v⟩
        cases v
        rfl
      change (if P true r h z ∧ Q true h z then (1:ℝ) else 0) =
        (if P true r (e ((e.symm h).1,((e.symm h).2.1,PUnit.unit))) z ∧
          Q true (e ((e.symm h).1,((e.symm h).2.1,PUnit.unit))) z then 1 else 0)
      have hf : e ((e.symm h).1,((e.symm h).2.1,PUnit.unit)) = h :=
        (congrArg e he).trans (e.apply_symm_apply h)
      exact congrArg (fun f => if P true r f z ∧ Q true f z then (1:ℝ) else 0) hf.symm
    rw [hform, markedPrefixMass_snoc p q (L γ) (L γ') s .both 0 0 u₀
      (fun h y z => if P true r (mergedTraceAppend (Λ.X × Λ.X) s [PairMove.both] (h,(y,PUnit.unit))) z ∧
          Q true (mergedTraceAppend (Λ.X × Λ.X) s [PairMove.both] (h,(y,PUnit.unit))) z then 1 else 0)]
    apply integral_congr_ae
    refine Filter.Eventually.of_forall fun z => Finset.sum_congr rfl fun h _ =>
      Finset.sum_congr rfl fun y _ => ?_
    by_cases hz : mergedTraceMass (L γ) (L γ') z s 0 0 u₀ h = 0
    · simp only [mergedTraceMass_snoc,hz,zero_mul,mul_zero]
    · have hz₀ : 0 < mergedTraceMass (L γ) (L γ') z s 0 0 u₀ h :=
        lt_of_le_of_ne (mergedTraceMass_nonneg _ _
          (Λ.firstGood_usedKernel_nonneg p q ρ κ hκ hs hsite (zero_lt_one.trans_le hρ) γ G (routeSignDraw γ))
          (Λ.firstGood_usedKernel_nonneg p q ρ κ hκ hs hsite (zero_lt_one.trans_le hρ) γ' G (routeSignDraw γ'))
          z s 0 0 u₀ h) (Ne.symm hz)
      have hvalid := Λ.firstGood_frozen_used_prefix_valid p q ρ κ hκ (zero_lt_one.trans_le hρ)
        hs hsite γ γ' routeSignDraw z₀ z hbox hpre hcount s u₀ h hdR₀ hz₀
      have hvl := hvalid.1 (by dsimp [j] at *; omega) (by dsimp [j] at *; omega)
      have hvr := hvalid.2 (by dsimp [j'] at *; omega) (by dsimp [j'] at *; omega)
      let u := mergedTraceLast s u₀ h
      have hctx : Λ.moveCtx G ℓ u.1 :=
        Λ.firstGood_route_move_context γ z₀ (by dsimp [j]; omega) hj
          (hbox γ (by simp)) (hpre γ (by simp)) u.1 hvl.1 hvl.2 hm
      have hctx' : Λ.moveCtx G ℓ' u.2 :=
        Λ.firstGood_route_move_context γ' z₀ (by dsimp [j']; omega) hj'
          (hbox γ' (by simp)) (hpre γ' (by simp)) u.2 hvr.1 hvr.2 hm'
      let g : NestTrace (Λ.X × Λ.X) ([PairMove.both] : List PairMove).length := (y,PUnit.unit)
      have hp := Λ.mergedTubeMark_append G ℓ₀ true s [PairMove.both] a b h g ha hb z
      have hq := Λ.mergedTubeMark_snoc_both_of_nonzero G ℓ true (L γ) (L γ') s 0 0 u₀ y h z
        (by omega) (by omega) hz
      change P true r (mergedTraceAppend (Λ.X × Λ.X) s [PairMove.both] (h,g)) z = P true s h z at hp
      change Q true (mergedTraceAppend (Λ.X × Λ.X) s [PairMove.both] (h,g)) z =
        Λ.firstGoodSharedTubeMark G ℓ u.1.1.val u.2.1.val y.1.2 y.2.2 z at hq
      by_cases hp₀ : P true s h z <;>
        by_cases hq₀ : Λ.firstGoodSharedTubeMark G ℓ u.1.1.val u.2.1.val y.1.2 y.2.2 z <;>
        simp [hp,hq,F,E,hp₀,hq₀,hctx,hctx',u,g]
  change markedPrefixMass p q (K γ) (K γ') r 0 0 (x,x')
    (fun h z => if P false r h z ∧ Q false h z then 1 else 0) / ρ ^ sharedCount r ≤ _
  rw [hpair, heq, hprev]
  simpa only [Nat.zero_add] using hcontract

end NearCritical.Section10.NestLayout
