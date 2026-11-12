module

public import NearCritical.Section10NormalizedSpread
public import NearCritical.Section10FrozenArrivalNest
public import NearCritical.Section10MergedTubeMark
public import NearCritical.Section10NormalizedOccupation

/-! Entry of a shared physical tube from the pair occupation of the
nests saved at the two arrivals. -/

@[expose] public section
noncomputable section

namespace NearCritical.Section10

open MeasureTheory
open scoped Classical

theorem markedPrefixMass_congr_of_nonzero {d : ℕ} {X Y : Type*} [Fintype X] [Fintype Y]
    (p q : unitInterval)
    (K : ℕ → X → X → Configuration d × Configuration d → ℝ)
    (K' : ℕ → Y → Y → Configuration d × Configuration d → ℝ)
    (s : List PairMove) (t t' : ℕ) (x : X × Y)
    (F F' : NestTrace (X × Y) s.length → Configuration d × Configuration d → ℝ)
    (h : ∀ f z, mergedTraceMass K K' z s t t' x f ≠ 0 → F f z = F' f z) :
    markedPrefixMass p q K K' s t t' x F = markedPrefixMass p q K K' s t t' x F' := by
  apply integral_congr_ae
  refine Filter.Eventually.of_forall fun z => Finset.sum_congr rfl fun f _ => ?_
  by_cases he : mergedTraceMass K K' z s t t' x f = 0
  · simp only [he,mul_zero]
  · rw [h f z he]

namespace NestLayout

set_option maxHeartbeats 500000 in
/-- Pair occupation at the recorded arrival rows controls the mass of
a fresh shared-tube mark. The prefix weight may restrict to histories
whose preceding shared bridge mark is absent. -/
theorem firstGood_tube_entry_of_arrival_occupation
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
    (hj : leftCount s < 2*M) (hj' : rightCount s < 2*M)
    (F : NestTrace (Λ.X × Λ.X) s.length → Configuration d × Configuration d → ℝ)
    {A K₀ : ℝ} (hA : 0 ≤ A) :
    let G := refineReveal Λ.ρ₀ Λ.S₀ z₀
    let B (δ : SourceRoute D M) i := Λ.Bl₀ G.1 (routeLab M δ.position i)
    let K (δ : SourceRoute D M) := (Λ.ruleFirstGood M p q ρ κ hκ hs hsite).toNestRule.kernel δ G
    let R := Λ.S₀ G.1
    let j := leftCount s
    let j' := rightCount s
    let ℓ := routeLab M γ.position j
    let ℓ' := routeLab M γ'.position j'
    let a := routeArrivalRank γ.position ℓ.site
    let b := routeArrivalRank γ'.position ℓ'.site
    let S := Λ.fam G ℓ.site
    let μ := (percolation d p).prod (percolation d q)
    let r := s ++ [PairMove.both]
    let e := mergedTraceAppend (Λ.X × Λ.X) s [PairMove.both]
    ℓ'.site = ℓ.site →
    PairFresh (B γ) (B γ') r 0 0 R →
    (∀ h, IsLocal (R ∪ mergedTraceBlocks (B γ) (B γ') s 0 0) (F h)) →
    (∀ h z, 0 ≤ F h z) →
    (∀ C ∈ S, ∀ C' ∈ S, markedPrefixMass p q (K γ) (K γ') s 0 0 x
      (fun h z => if ∃ y, mergedArrivalStates? s a b h = some y ∧ C ∈ y.1.1.val ∧ C' ∈ y.2.1.val
        then F h z else 0) / ρ ^ sharedCount s ≤ A) →
    (∀ C ∈ S, ∀ c c' : Bool,
      (∑ C' ∈ S.erase C, μ.real {z | Λ.firstGoodSharedTubeMark G ℓ {C} {C'} c c' z}) ≤ K₀) →
    markedPrefixMass p q (K γ) (K γ') r 0 0 x (fun h z =>
      if Λ.mergedTubeMark G ℓ false r (j-1) (j'-1) h z then F (e.symm h).1 z else 0) /
        ρ ^ sharedCount r ≤ ρ * ((S.card:ℝ) * (A * (1+4*K₀))) := by
  intro G B K R j j' ℓ ℓ' a b S μ r e hSite hFresh hF hF₀ hocc hrow
  let u := mergedTraceLast s x
  let H := NestTrace (Λ.X × Λ.X) s.length
  have hFresh₀ := PairFresh.prefix_of_append (B γ) (B γ') s [PairMove.both] 0 0 R hFresh
  have hd₀ := PairFresh.disjoint_blocks (B γ) (B γ') s 0 0 R hFresh₀
  have hd : Disjoint (R ∪ mergedTraceBlocks (B γ) (B γ') s 0 0) (B γ (0+j)) :=
    Finset.disjoint_of_subset_right Finset.subset_union_left
      (PairFresh.suffix_of_append (B γ) (B γ') s [PairMove.both] 0 0 R hFresh).1
  have hk₀ (δ : SourceRoute D M) (i : ℕ) (u v : Λ.X) (z : Configuration d × Configuration d) :
      0 ≤ K δ i u v z :=
    stepKernel_nonneg _ _ _ ((inv_nonneg.mpr hρ.le).trans (hs δ G i u)) v z
  have hvalid (h : H) (z : Configuration d × Configuration d)
      (hn : F h z * mergedTraceMass (K γ) (K γ') z s 0 0 x h ≠ 0) :
      (u h).1.1.val ⊆ S ∧ (u h).2.1.val ⊆ S := by
    have hp := lt_of_le_of_ne (mergedTraceMass_nonneg _ _ (hk₀ γ) (hk₀ γ') z s 0 0 x h)
      (right_ne_zero_of_mul hn).symm
    obtain ⟨hl,hr⟩ := Λ.firstGood_frozen_prefix_valid p q ρ κ hκ hρ hs hsite γ γ' z₀ z
      hbox hpre hcount s x h hd₀ hp
    refine ⟨(hl hj₀ hj).2,?_⟩
    have hh := (hr hj'₀ hj').2
    change (u h).2.1.val ⊆ Λ.fam G ℓ'.site at hh
    rwa [hSite] at hh
  have hspread (C : Finset (Vertex d)) (hC : C ∈ S) (C' : Finset (Vertex d)) (hC' : C' ∈ S) :
      markedPrefixMass p q (K γ) (K γ') s 0 0 x
        (fun h z => if C ∈ (u h).1.1.val ∧ C' ∈ (u h).2.1.val then F h z else 0) /
          ρ ^ sharedCount s ≤ A := by
    refine le_trans (le_of_eq (congrArg (fun z : ℝ => z / ρ ^ sharedCount s) ?_)) (hocc C hC C' hC')
    refine markedPrefixMass_congr_of_nonzero p q (K γ) (K γ') s 0 0 x _ _ ?_
    intro h z hn
    have hArr : mergedArrivalStates? s a b h = some (u h) :=
      Λ.firstGood_mergedTraceLast_eq_arrivals p q ρ κ hκ hs hsite γ γ' G z
        s x h hj₀ hj hj'₀ hj' hn
    simp only [hArr, Option.some.injEq, exists_eq_left']
  have hbound := Λ.firstGood_spread_pending_prefix_le p q ρ κ hκ hs hsite hρ G γ γ' s 0 0 x R F hA
    hF hF₀ hd (by simpa only [Nat.zero_add] using hvalid)
    (by simpa only [Nat.zero_add] using hspread) (by simpa only [Nat.zero_add] using hrow)
  have heq :
      markedPrefixMass p q (K γ) (K γ') r 0 0 x (fun h z =>
        if Λ.mergedTubeMark G ℓ false r (j-1) (j'-1) h z then F (e.symm h).1 z else 0) =
      markedPrefixMass p q (K γ) (K γ') r 0 0 x (fun h z =>
        let f := (e.symm h).1
        if Λ.firstGoodSharedTubeMark G ℓ (u f).1.1.val (u f).2.1.val (u f).1.2 (u f).2.2 z
        then F f z else 0) := by
    refine markedPrefixMass_congr_of_nonzero p q (K γ) (K γ') r 0 0 x _ _ ?_
    intro f z hn
    let h := (e.symm f).1
    let y := (e.symm f).2.1
    have ht : (h,(y,PUnit.unit)) = e.symm f := by
      dsimp [h,y]
      rcases e.symm f with ⟨g,v,w⟩
      cases w
      rfl
    have he : e (h,(y,PUnit.unit)) = f := (congrArg e ht).trans (e.apply_symm_apply f)
    have hp : mergedTraceMass (K γ) (K γ') z s 0 0 x h ≠ 0 := by
      intro hz
      apply hn
      exact (congrArg (mergedTraceMass (K γ) (K γ') z r 0 0 x) he.symm).trans
        ((mergedTraceMass_snoc (K γ) (K γ') z s .both 0 0 x y h).trans (by rw [hz,zero_mul]))
    have hm := Λ.mergedTubeMark_snoc_both_of_nonzero G ℓ false (K γ) (K γ') s 0 0 x y h z hj₀ hj'₀ hp
    let mark := fun g => Λ.mergedTubeMark G ℓ false r (j-1) (j'-1) g z
    have htube : mark f =
        Λ.firstGoodSharedTubeMark G ℓ (u h).1.1.val (u h).2.1.val (u h).1.2 (u h).2.2 z :=
      (congrArg mark he.symm).trans (by simpa only [mark,Bool.false_eq_true,if_false] using hm)
    change (if mark f then F h z else 0) = _
    rw [htube]
  exact (le_of_eq (congrArg (fun m : ℝ => m / ρ ^ sharedCount r) heq)).trans
    (by simpa only [Nat.zero_add] using hbound)

end NestLayout
end NearCritical.Section10
