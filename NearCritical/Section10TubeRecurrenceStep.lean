module

public import NearCritical.Section10ActualTubePersistence
public import NearCritical.Section10ArrivalTubeEntry

/-! Split a current shared-tube mark into spread entry and persistence
of the previous shared incoming bridge. -/

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

/-- If both arrivals used the preceding shared tube, split according
to that tube's mark. Its complement is charged to spread occupation;
its presence is charged to the normalized two-thirds persistence. -/
theorem firstGood_shared_predecessor_recurrence_le
    (hρ : 1 ≤ ρ) (hρ' : ρ ≤ 9/8) (hM : 1 ≤ M)
    (γ γ' : SourceRoute D M) (z₀ : Configuration d × Configuration d)
    (hbox : ∀ δ ∈ ({γ,γ'} : Finset (SourceRoute D M)), ∀ i < 2*M,
      (routeLab M δ.position i).site ∈ Λ.siteBox)
    (hpre : ∀ δ ∈ ({γ,γ'} : Finset (SourceRoute D M)), ∀ i < 2*M,
      IsPreGoodCube Λ.typ Λ.t (Λ.center (routeLab M δ.position i).site) z₀.1)
    (hcount : (Λ.k : ℝ) ≤ Λ.typ.countLower * (2*(Λ.t:ℝ))^(d-6))
    (s : List PairMove) (x x' : Λ.X) (ℓ₀ : RouteLabel D) (a b : ℕ)
    (ha : a+1 < leftCount s) (hb : b+1 < rightCount s)
    (ha₀ : routeSignDraw γ (a+1) = true) (hb₀ : routeSignDraw γ' (b+1) = true)
    {A K₀ : ℝ} (hA : 0 ≤ A) :
    let G := refineReveal Λ.ρ₀ Λ.S₀ z₀
    let B (δ : SourceRoute D M) i := Λ.Bl₀ G.1 (routeLab M δ.position i)
    let K (δ : SourceRoute D M) := (Λ.ruleFirstGood M p q ρ κ hκ hs hsite).toNestRule.kernel δ G
    let j := leftCount s
    let j' := rightCount s
    let ℓ := routeLab M γ.position j
    let ℓ' := routeLab M γ'.position j'
    let c := routeArrivalRank γ.position ℓ.site
    let c' := routeArrivalRank γ'.position ℓ'.site
    let S := Λ.fam G ℓ.site
    let μ := (percolation d p).prod (percolation d q)
    let r := s ++ [PairMove.both]
    let P t (h : NestTrace (Λ.X × Λ.X) t.length) z :=
      Λ.mergedTubeMark G ℓ₀ false t a b h z
    let Q (h : NestTrace (Λ.X × Λ.X) r.length) z :=
      Λ.mergedTubeMark G ℓ false r (j-1) (j'-1) h z
    ℓ'.site = ℓ.site →
    PairFresh (B γ) (B γ') r 0 0 (Λ.S₀ G.1) →
    Λ.Bl₀ G.1 ℓ₀ ⊆ mergedTraceBlocks (B γ) (B γ') s 0 0 →
    j+1 < 2*M → j'+1 < 2*M →
    ℓ.target ≠ ℓ.site → ℓ'.target ≠ ℓ'.site →
    routeSignDraw γ j = true → routeSignDraw γ' j' = true →
    (∀ u v : Λ.X, Λ.moveCtx G ℓ u → Λ.moveCtx G ℓ' v → ∀ e e', e ≠ e' →
      μ.real {z | Λ.firstGoodSharedTubeMark G ℓ u.1.val v.1.val e e' z} ≤ 1/40) →
    (∀ C ∈ S, ∀ C' ∈ S, markedPrefixMass p q (K γ) (K γ') s 0 0 (x,x')
      (fun h z => if ¬ P s h z ∧
        (∃ y, mergedArrivalStates? s c c' h = some y ∧ C ∈ y.1.1.val ∧ C' ∈ y.2.1.val)
        then 1 else 0) / ρ ^ sharedCount s ≤ A) →
    (∀ C ∈ S, ∀ e e' : Bool,
      (∑ C' ∈ S.erase C, μ.real {z | Λ.firstGoodSharedTubeMark G ℓ {C} {C'} e e' z}) ≤ K₀) →
    markedPrefixMass p q (K γ) (K γ') r 0 0 (x,x') (fun h z => if Q h z then 1 else 0) /
      ρ ^ sharedCount r ≤
      ρ * ((S.card:ℝ) * (A * (1+4*K₀))) +
        (2/3:ℝ) * (markedPrefixMass p q (K γ) (K γ') s 0 0 (x,x')
          (fun h z => if P s h z then 1 else 0) / ρ ^ sharedCount s) := by
  intro G B K j j' ℓ ℓ' c c' S μ r P Q hSite hFresh hRead hj hj' hm hm' hact hact' hrare hocc hrow
  let F (h : NestTrace (Λ.X × Λ.X) s.length) z := if P s h z then (0:ℝ) else 1
  let e := mergedTraceAppend (Λ.X × Λ.X) s [PairMove.both]
  have hF (h : NestTrace (Λ.X × Λ.X) s.length) :
      IsLocal (Λ.S₀ G.1 ∪ mergedTraceBlocks (B γ) (B γ') s 0 0) (F h) :=
    (isLocal_of_readsOnly (Λ.mergedTubeMark_readsOnly G ℓ₀ false s a b h)
      (fun v : Prop => if v then (0:ℝ) else 1)).mono (hRead.trans Finset.subset_union_right)
  have hF₀ (h : NestTrace (Λ.X × Λ.X) s.length) (z : Configuration d × Configuration d) :
      0 ≤ F h z := by unfold F; split_ifs <;> norm_num
  have hOcc (C : Finset (Vertex d)) (hC : C ∈ S) (C' : Finset (Vertex d)) (hC' : C' ∈ S) :
      markedPrefixMass p q (K γ) (K γ') s 0 0 (x,x')
        (fun h z => if ∃ y, mergedArrivalStates? s c c' h = some y ∧ C ∈ y.1.1.val ∧ C' ∈ y.2.1.val
          then F h z else 0) / ρ ^ sharedCount s ≤ A := by
    refine le_trans (le_of_eq (congrArg (fun z : ℝ => z / ρ ^ sharedCount s) ?_)) (hocc C hC C' hC')
    apply markedPrefixMass_congr_of_nonzero
    intro f z _
    by_cases hp : P s f z <;>
      by_cases ho : ∃ y, mergedArrivalStates? s c c' f = some y ∧ C ∈ y.1.1.val ∧ C' ∈ y.2.1.val <;>
      simp [F,hp,ho]
  have hEntry := Λ.firstGood_tube_entry_of_arrival_occupation p q ρ κ hκ (zero_lt_one.trans_le hρ)
    hs hsite γ γ' z₀ hbox hpre hcount s (x,x') (by dsimp [j] at hj ⊢; omega)
    (by dsimp [j'] at hj' ⊢; omega) (by dsimp [j] at hj ⊢; omega) (by dsimp [j'] at hj' ⊢; omega)
    F hA hSite hFresh hF hF₀ hOcc hrow
  have hPersist := Λ.firstGood_frozen_two_tube_mass_le p q ρ κ hκ hs hsite hρ hρ' hM γ γ' z₀
    hbox hpre hcount s x x' ℓ₀ a b ha hb ha₀ hb₀ hFresh hRead hj hj' hm hm' hact hact' hrare
  let H := NestTrace (Λ.X × Λ.X) r.length
  let W (h : H) z := mergedTraceMass (K γ) (K γ') z r 0 0 (x,x') h
  let J (h : H) z := if Q h z then F (e.symm h).1 z else 0
  let J' (h : H) z := if P r h z ∧ Q h z then (1:ℝ) else 0
  have he (h : H) (z : Configuration d × Configuration d) : P r h z = P s (e.symm h).1 z := by
    have hp := Λ.mergedTubeMark_append G ℓ₀ false s [PairMove.both] a b
      (e.symm h).1 (e.symm h).2 ha hb z
    have heq : e ((e.symm h).1,(e.symm h).2) = h := e.apply_symm_apply h
    exact (congrArg (fun f => P r f z) heq.symm).trans hp
  have hpt (z : Configuration d × Configuration d) :
      (∑ h : H, (if Q h z then (1:ℝ) else 0) * W h z) =
        (∑ h : H, J h z * W h z) + ∑ h : H, J' h z * W h z := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun h _ => ?_
    by_cases hp : P r h z <;> by_cases hq : Q h z <;>
      simp only [J,J',F,← he h z,hp,hq,true_and,false_and,if_true,if_false,
        mul_zero,zero_mul,zero_add,add_zero]
  have hW (h : H) : IsLocal (mergedTraceBlocks (B γ) (B γ') r 0 0) (W h) :=
    mergedTraceMass_isLocal (B γ) (B γ') (K γ) (K γ')
      (fun _ _ y => stepKernel_isLocal _ _ _ _ y) (fun _ _ y => stepKernel_isLocal _ _ _ _ y)
      r 0 0 (x,x') h
  let T := Λ.Bl₀ G.1 ℓ₀ ∪ Λ.Bl₀ G.1 ℓ
  have hP (h : H) : ReadsOnly T (P r h) :=
    (Λ.mergedTubeMark_readsOnly G ℓ₀ false r a b h).mono Finset.subset_union_left
  have hQ (h : H) : ReadsOnly T (Q h) :=
    (Λ.mergedTubeMark_readsOnly G ℓ false r (j-1) (j'-1) h).mono Finset.subset_union_right
  have hJ (h : H) : IsLocal T (J h) := by
    have hR : ReadsOnly T (fun z => Q h z ∧ ¬ P r h z) := by
      intro z z' hz
      change (Q h z ∧ ¬ P r h z) = (Q h z' ∧ ¬ P r h z')
      rw [hQ h z z' hz,hP h z z' hz]
    have hloc := isLocal_of_readsOnly hR (fun b : Prop => if b then (1:ℝ) else 0)
    have heq : J h = fun z => if Q h z ∧ ¬ P r h z then (1:ℝ) else 0 := by
      funext z
      by_cases hp : P r h z <;> by_cases hq : Q h z <;> simp [J,F,← he h z,hp,hq]
    rw [heq]
    convert hloc using 1 <;>
      (funext z; by_cases hz : Q h z ∧ ¬ P r h z <;> simp only [hz, ite_true, ite_false])
  have hJ' (h : H) : IsLocal T (J' h) := by
    have hR : ReadsOnly T (fun z => P r h z ∧ Q h z) := by
      intro z z' hz
      change (P r h z ∧ Q h z) = (P r h z' ∧ Q h z')
      rw [hP h z z' hz,hQ h z z' hz]
    convert isLocal_of_readsOnly hR (fun b : Prop => if b then (1:ℝ) else 0) using 1 <;>
      (funext z; by_cases hz : P r h z ∧ Q h z <;> simp only [J', hz, ite_true, ite_false])
  have hsplit :
      markedPrefixMass p q (K γ) (K γ') r 0 0 (x,x') (fun h z => if Q h z then 1 else 0) =
      markedPrefixMass p q (K γ) (K γ') r 0 0 (x,x') J +
        markedPrefixMass p q (K γ) (K γ') r 0 0 (x,x') J' := by
    unfold markedPrefixMass
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
    exact integral_add
      (integrable_finsetSum _ (fun h _ => ((hJ h).mul_union (hW h)).integrable p q))
      (integrable_finsetSum _ (fun h _ => ((hJ' h).mul_union (hW h)).integrable p q))
  rw [hsplit,add_div]
  exact add_le_add hEntry hPersist

end NearCritical.Section10.NestLayout
