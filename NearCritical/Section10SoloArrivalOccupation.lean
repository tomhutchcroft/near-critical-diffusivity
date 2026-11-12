module

public import NearCritical.Section10ActualPrefixMass
public import NearCritical.Section10FrozenRevealHistory
public import NearCritical.Section10MergedArrivalAppend

/-! H1 on an actual solo arrival, with the earlier nest and any other
mark read from the already revealed history. -/

@[expose] public section
noncomputable section

namespace NearCritical.Section10

open MeasureTheory
open scoped Classical

/-- Read the state created on the appended solo arrival. -/
def soloArrivalState? {X : Type*} (s : List PairMove) (m : PairMove)
    (h : NestTrace (X × X) (s ++ [m]).length) : Option X :=
  match m with
  | .left => routeTraceGet? _ (mergedRouteTraces (s ++ [PairMove.left]) h).1 (leftCount s)
  | .right => routeTraceGet? _ (mergedRouteTraces (s ++ [PairMove.right]) h).2 (rightCount s)
  | .both => none

theorem soloArrivalState?_append {X : Type*} (s : List PairMove) (m : PairMove)
    (hm : m ≠ .both) (h : NestTrace (X × X) s.length) (y : X × X) :
    soloArrivalState? s m (mergedTraceAppend (X × X) s [m] (h,(y,PUnit.unit))) =
      some (soloDestination m y) := by
  cases m
  · have he := mergedArrivalGet_left_suffix s [PairMove.left] h (y,PUnit.unit) 0
    simpa only [soloArrivalState?,soloDestination,Nat.zero_add, leftCount, mergedRouteTraces, routeTraceGet?] using he
  · have he := mergedArrivalGet_right_suffix s [PairMove.right] h (y,PUnit.unit) 0
    simpa only [soloArrivalState?,soloDestination,Nat.zero_add, rightCount, mergedRouteTraces, routeTraceGet?] using he
  · exact (hm rfl).elim

namespace NestLayout

set_option maxHeartbeats 500000 in
/-- The normalized H1 cost at an actual solo arrival is at most the
one-child bound times the size of the recorded earlier nest. A singleton
earlier nest gives the prescribed-cluster occupation estimate. -/
theorem firstGood_solo_arrival_mass_le
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
    (s : List PairMove) (m : PairMove) (hm : m ≠ .both) (x : Λ.X × Λ.X)
    (F : NestTrace (Λ.X × Λ.X) s.length → Configuration d × Configuration d → ℝ)
    (N : NestTrace (Λ.X × Λ.X) s.length → Finset (Finset (Vertex d)))
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    let G := refineReveal Λ.ρ₀ Λ.S₀ z₀
    let B (δ : SourceRoute D M) i := Λ.Bl₀ G.1 (routeLab M δ.position i)
    let K (δ : SourceRoute D M) := (Λ.ruleFirstGood M p q ρ κ hκ hs hsite).toNestRule.kernel δ G
    let R := Λ.S₀ G.1
    let j := leftCount s
    let j' := rightCount s
    let ℓ := routeLab M γ.position j
    let ℓ' := routeLab M γ'.position j'
    let μ := (percolation d p).prod (percolation d q)
    PairFresh (B γ) (B γ') (s ++ [m]) 0 0 R →
    (m = .left → 0 < j ∧ j+1 < 2*M ∧ ℓ.target ≠ ℓ.site) →
    (m = .right → 0 < j' ∧ j'+1 < 2*M ∧ ℓ'.target ≠ ℓ'.site) →
    (∀ h, IsLocal (R ∪ mergedTraceBlocks (B γ) (B γ') s 0 0) (F h)) →
    (∀ h z, 0 ≤ F h z) →
    (∀ h z, mergedTraceMass (K γ) (K γ') z s 0 0 x h ≠ 0 → (N h).card ≤ b) →
    (∀ h, m = .left → Λ.moveCtx G ℓ (mergedTraceLast s x h).1 → ∀ c ∈ N h,
      (∫ z, ∑ y : Λ.X, if c ∈ y.1.val then K γ j (mergedTraceLast s x h).1 y z else 0 ∂μ) ≤ a) →
    (∀ h, m = .right → Λ.moveCtx G ℓ' (mergedTraceLast s x h).2 → ∀ c ∈ N h,
      (∫ z, ∑ y : Λ.X, if c ∈ y.1.val then K γ' j' (mergedTraceLast s x h).2 y z else 0 ∂μ) ≤ a) →
    markedPrefixMass p q (K γ) (K γ') (s ++ [m]) 0 0 x (fun h z =>
      let past := ((mergedTraceAppend (Λ.X × Λ.X) s [m]).symm h).1
      if ∃ y, soloArrivalState? s m h = some y ∧ (N past ∩ y.1.val).Nonempty then F past z else 0) /
        ρ ^ sharedCount (s ++ [m]) ≤
      (b*a) * (markedPrefixMass p q (K γ) (K γ') s 0 0 x F / ρ ^ sharedCount s) := by
  intro G B K R j j' ℓ ℓ' μ hFresh hleft hright hF hF₀ hN hH1 hH1'
  let H := NestTrace (Λ.X × Λ.X) s.length
  let u := mergedTraceLast s x
  let V (h : H) := (m = .left → Λ.moveCtx G ℓ (u h).1) ∧
    (m = .right → Λ.moveCtx G ℓ' (u h).2) ∧ (N h).card ≤ b
  let e := mergedTraceAppend (Λ.X × Λ.X) s [m]
  let E (h : H) (y : Λ.X × Λ.X) := if
    V h ∧ (N h ∩ (soloDestination m y).1.val).Nonempty then (1:ℝ) else 0
  have hFresh₀ := PairFresh.prefix_of_append (B γ) (B γ') s [m] 0 0 R hFresh
  have hd₀ := PairFresh.disjoint_blocks (B γ) (B γ') s 0 0 R hFresh₀
  have hf := PairFresh.suffix_of_append (B γ) (B γ') s [m] 0 0 R hFresh
  have hd : Disjoint (R ∪ mergedTraceBlocks (B γ) (B γ') s 0 0)
      (pairMoveBlock (B γ) (B γ') m (0+j) (0+j')) := by
    cases m <;> exact hf.1
  have hk (δ : SourceRoute D M) (i : ℕ) (x y : Λ.X) : IsLocal (B δ i) (K δ i x y) :=
    stepKernel_isLocal _ _ _ _ y
  have hk₀ (δ : SourceRoute D M) (i : ℕ) (x y : Λ.X) (z : Configuration d × Configuration d) :
      0 ≤ K δ i x y z :=
    stepKernel_nonneg _ _ _ ((inv_nonneg.mpr hρ.le).trans (hs δ G i x)) y z
  have hraw : markedPrefixMass p q (K γ) (K γ') (s ++ [m]) 0 0 x
      (fun f z => F (e.symm f).1 z * E (e.symm f).1 (e.symm f).2.1) ≤
      (b*a) * markedPrefixMass p q (K γ) (K γ') s 0 0 x F := by
    rw [markedPrefixMass_snoc p q (K γ) (K γ') s m 0 0 x (fun h y z => F h z * E h y)]
    have hrow := firstGood_solo_site_collision_prefix (fun y : Λ.X => y.1.val) p q (B γ) (B γ')
      (K γ) (K γ') (hk γ) (hk γ') (hk₀ γ) (hk₀ γ') s m hm 0 0 x R F N V ha hb
      (fun h hv => hv.2.2) hF hF₀ hd
      (fun h hv c hc he => by simpa only [Nat.zero_add] using hH1 h he (hv.1 he) c hc)
      (fun h hv c hc he => by simpa only [Nat.zero_add] using hH1' h he (hv.2.1 he) c hc)
    refine le_trans (le_of_eq ?_) hrow
    apply integral_congr_ae
    refine Filter.Eventually.of_forall fun z => Finset.sum_congr rfl fun h _ =>
      Finset.sum_congr rfl fun y _ => ?_
    dsimp only [E]
    let S := (soloDestination m y).1.val
    let I := letI : DecidableEq (Finset (Vertex d)) := Classical.decEq _
             N h ∩ S
    have hI : I = N h ∩ S := by
      ext c
      simp only [I, Finset.mem_inter]
    by_cases he : V h ∧ (N h ∩ S).Nonempty
    · have he' : V h ∧ I.Nonempty := by rwa [hI]
      rw [if_pos he, if_pos he']
    · have he' : ¬ (V h ∧ I.Nonempty) := by rwa [hI]
      rw [if_neg he, if_neg he']
  have hnorm : sharedCount (s ++ [m]) = sharedCount s := by
    rw [sharedCount_append]
    cases m
    · simp [sharedCount]
    · simp [sharedCount]
    · exact (hm rfl).elim
  rw [hnorm, ← mul_div_assoc]
  apply div_le_div_of_nonneg_right _ (pow_nonneg hρ.le _)
  refine le_trans (le_of_eq ?_) hraw
  apply integral_congr_ae
  refine Filter.Eventually.of_forall fun z => Finset.sum_congr rfl fun f _ => ?_
  let h := (e.symm f).1
  let y := (e.symm f).2.1
  have he : e (h,(y,PUnit.unit)) = f := by
    have ht : (h,(y,PUnit.unit)) = e.symm f := by
      dsimp [h,y]
      rcases e.symm f with ⟨k,v,w⟩
      cases w
      rfl
    exact (congrArg e ht).trans (e.apply_symm_apply f)
  by_cases hz : mergedTraceMass (K γ) (K γ') z s 0 0 x h = 0
  · have hz' : mergedTraceMass (K γ) (K γ') z (s ++ [m]) 0 0 x f = 0 := by
      rw [← he]
      exact (mergedTraceMass_snoc _ _ _ _ _ _ _ _ _ _).trans (by rw [hz,zero_mul])
    rw [hz',mul_zero,mul_zero]
  · have hp := lt_of_le_of_ne (mergedTraceMass_nonneg _ _ (hk₀ γ) (hk₀ γ') z s 0 0 x h) (Ne.symm hz)
    obtain ⟨hl,hr⟩ := Λ.firstGood_frozen_prefix_valid p q ρ κ hκ hρ hs hsite γ γ' z₀ z
      hbox hpre hcount s x h hd₀ hp
    have hv : V h := by
      refine ⟨?_,?_,hN h z hz⟩
      · intro hm₀
        obtain ⟨hj₀,hj,hmv⟩ := hleft hm₀
        have hi := hl hj₀ (by dsimp [j] at hj ⊢; omega)
        exact Λ.firstGood_route_move_context γ z₀ hj₀ hj (hbox γ (by simp))
          (hpre γ (by simp)) (u h).1 hi.1 hi.2 hmv
      · intro hm₀
        obtain ⟨hj₀,hj,hmv⟩ := hright hm₀
        have hi := hr hj₀ (by dsimp [j'] at hj ⊢; omega)
        exact Λ.firstGood_route_move_context γ' z₀ hj₀ hj (hbox γ' (by simp))
          (hpre γ' (by simp)) (u h).2 hi.1 hi.2 hmv
    have hy : soloArrivalState? s m f = some (soloDestination m y) :=
      (congrArg (soloArrivalState? s m) he.symm).trans (soloArrivalState?_append s m hm h y)
    let v := soloDestination m y
    change (if ∃ w, soloArrivalState? s m f = some w ∧ (N h ∩ w.1.val).Nonempty then F h z else 0) *
      mergedTraceMass (K γ) (K γ') z (s ++ [m]) 0 0 x f =
      (F h z * E h y) * mergedTraceMass (K γ) (K γ') z (s ++ [m]) 0 0 x f
    have hc : (∃ w, soloArrivalState? s m f = some w ∧ (N h ∩ w.1.val).Nonempty) ↔
        (N h ∩ v.1.val).Nonempty := by
      rw [hy]
      change (∃ w, some v = some w ∧ _) ↔ _
      simp
    by_cases hmem : (N h ∩ v.1.val).Nonempty
    · rw [if_pos (hc.mpr hmem)]
      have he' : E h y = 1 := by
        change (if V h ∧ (N h ∩ v.1.val).Nonempty then (1:ℝ) else 0) = 1
        exact if_pos ⟨hv,hmem⟩
      rw [he',mul_one]
    · rw [if_neg (fun ht => hmem (hc.mp ht))]
      have he' : E h y = 0 := by
        change (if V h ∧ (N h ∩ v.1.val).Nonempty then (1:ℝ) else 0) = 0
        exact if_neg (fun ht => hmem ht.2)
      rw [he',mul_zero]

end NestLayout
end NearCritical.Section10
