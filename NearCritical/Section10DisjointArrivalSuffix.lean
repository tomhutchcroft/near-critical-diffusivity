module

public import NearCritical.Section10ActualPrefixMass
public import NearCritical.Section10MergedTubeMark
public import NearCritical.Section10MergedArrivalAppend
public import NearCritical.Section10SharedMarkRecurrence

@[expose] public section
noncomputable section

namespace NearCritical.Section10

open MeasureTheory
open scoped Classical

namespace NestRule

/-- Transport a local prefix mark through the actual normalized nest
rule, using its one-route and two-route row bounds. -/
theorem marked_prefix_mass_suffix_le
    {D M d : ℕ} {X Φ : Type} [Fintype X] [Fintype Φ]
    {p q : unitInterval} {ρ κ : ℝ} (Rule : NestRule D M d p q ρ κ X Φ)
    (hρ : 0 < ρ) (γ γ' : SourceRoute D M) (G : Φ)
    (s r : List PairMove) (x : X × X) :
    let B (δ : SourceRoute D M) i := Rule.Bl G (routeLab M δ.position i)
    PairFresh (B γ) (B γ') (s ++ r) 0 0 (Rule.S G) →
    ∀ F : NestTrace (X × X) s.length → Configuration d × Configuration d → ℝ,
    (∀ h, IsLocal (Rule.S G ∪ mergedTraceBlocks (B γ) (B γ') s 0 0) (F h)) →
    (∀ h z, 0 ≤ F h z) →
    markedPrefixMass p q (Rule.kernel γ G) (Rule.kernel γ' G) (s ++ r) 0 0 x
      (fun h => F ((mergedTraceAppend (X × X) s r).symm h).1) /
        ρ ^ sharedCount (s ++ r) ≤
    markedPrefixMass p q (Rule.kernel γ G) (Rule.kernel γ' G) s 0 0 x F / ρ ^ sharedCount s := by
  intro B hFresh F hFloc hF₀
  have hk (δ : SourceRoute D M) (i : ℕ) (u v : X) :
      IsLocal (B δ i) (Rule.kernel δ G i u v) := stepKernel_isLocal _ _ _ _ v
  have hn (δ : SourceRoute D M) (i : ℕ) (u v : X) (z : Configuration d × Configuration d) :
      0 ≤ Rule.kernel δ G i u v z :=
    stepKernel_nonneg _ _ _ ((inv_nonneg.mpr hρ.le).trans (Rule.hs δ G i u)) v z
  exact markedPrefixMass_normalized_suffix_le p q (B γ) (B γ') (Rule.kernel γ G) (Rule.kernel γ' G)
    (hk γ) (hk γ') (hn γ) (hn γ') hρ
    (fun i y => (Rule.kernel_row_integral_eq_one hρ γ G i y).le)
    (fun i y => (Rule.kernel_row_integral_eq_one hρ γ' G i y).le)
    (fun i i' y y' => Rule.kernel_pair_row_integral_le hρ γ γ' G i i' y y')
    s r 0 0 x (Rule.S G) hFresh F hFloc hF₀

/-- Once both arrivals are in the prefix, the normalized mass of a
prescribed pair of occupations can only decrease through fresh rows. -/
theorem arrival_pair_mass_suffix_le
    {D M d : ℕ} {X Φ : Type} [Fintype X] [Fintype Φ]
    {p q : unitInterval} {ρ κ : ℝ} (Rule : NestRule D M d p q ρ κ X Φ)
    (hρ : 0 < ρ) (γ γ' : SourceRoute D M) (G : Φ) (x : X × X)
    (s r : List PairMove) (a b : ℕ) (ha : a < leftCount s) (hb : b < rightCount s)
    (P : X × X → Prop) :
    let B (δ : SourceRoute D M) i := Rule.Bl G (routeLab M δ.position i)
    let F (t : List PairMove) (h : NestTrace (X × X) t.length)
        (_ : Configuration d × Configuration d) :=
      if ∃ y, mergedArrivalStates? t a b h = some y ∧ P y then (1:ℝ) else 0
    PairFresh (B γ) (B γ') (s ++ r) 0 0 (Rule.S G) →
    markedPrefixMass p q (Rule.kernel γ G) (Rule.kernel γ' G) (s ++ r) 0 0 x (F (s ++ r)) /
      ρ ^ sharedCount (s ++ r) ≤
    markedPrefixMass p q (Rule.kernel γ G) (Rule.kernel γ' G) s 0 0 x (F s) /
      ρ ^ sharedCount s := by
  intro B F hFresh
  let e := mergedTraceAppend (X × X) s r
  have heq : F (s ++ r) = fun h => F s (e.symm h).1 := by
    funext h z
    have he : e ((e.symm h).1, (e.symm h).2) = h := e.apply_symm_apply h
    have hy := (congrArg (mergedArrivalStates? (s ++ r) a b) he.symm).trans
      (mergedArrivalStates?_append_of_present s r (e.symm h).1 (e.symm h).2 a b ha hb)
    unfold F
    rw [hy]
  rw [heq]
  exact Rule.marked_prefix_mass_suffix_le hρ γ γ' G s r x hFresh (F s)
    (fun _ => isLocal_const _ _) (fun _ _ => by unfold F; split_ifs <;> norm_num)

end NestRule

namespace NestLayout

variable {D d M : ℕ} (Λ : NestLayout D d) [LinearOrder (Finset (Vertex d))]
  (p q : unitInterval) (ρ κ : ℝ) (hκ : 0 < κ)
  (hs : ∀ (γ : SourceRoute D M) (G : Λ.Φ) (j : ℕ) (x : Λ.X), ρ⁻¹ ≤
    localSuccessProbability p q (Λ.Bl₀ G.1 (routeLab M γ.position j))
      (bitSet G.2 (fun z => Λ.succσ G (routeLab M γ.position j) x
        (Λ.view G.1 (routeLab M γ.position j) z))))
  (hsite : ∀ s, κ⁻¹ ≤ coupledProb p q (Λ.siteEvent s))

/-- The normalized mass of an earlier shared-tube mark can only
decrease on extension by fresh rows. -/
theorem firstGood_tube_mark_mass_suffix_le
    (hρ : 0 < ρ) (γ γ' : SourceRoute D M) (G : Λ.Φ)
    (s r : List PairMove) (x : Λ.X × Λ.X) (ℓ : RouteLabel D)
    (a b : ℕ) (ha : a+1 < leftCount s) (hb : b+1 < rightCount s) :
    let B (δ : SourceRoute D M) k := Λ.Bl₀ G.1 (routeLab M δ.position k)
    let K (δ : SourceRoute D M) := (Λ.ruleFirstGood M p q ρ κ hκ hs hsite).toNestRule.kernel δ G
    let F (t : List PairMove) (h : NestTrace (Λ.X × Λ.X) t.length) z :=
      if Λ.mergedTubeMark G ℓ false t a b h z then (1:ℝ) else 0
    PairFresh (B γ) (B γ') (s ++ r) 0 0 (Λ.S₀ G.1) →
    Λ.Bl₀ G.1 ℓ ⊆ mergedTraceBlocks (B γ) (B γ') s 0 0 →
    markedPrefixMass p q (K γ) (K γ') (s ++ r) 0 0 x (F (s ++ r)) /
      ρ ^ sharedCount (s ++ r) ≤
    markedPrefixMass p q (K γ) (K γ') s 0 0 x (F s) / ρ ^ sharedCount s := by
  intro B K F hFresh hRead
  let Rule := (Λ.ruleFirstGood M p q ρ κ hκ hs hsite).toNestRule
  let e := mergedTraceAppend (Λ.X × Λ.X) s r
  have hFloc (h : NestTrace (Λ.X × Λ.X) s.length) :
      IsLocal (Λ.S₀ G.1 ∪ mergedTraceBlocks (B γ) (B γ') s 0 0) (F s h) := by
    have hF : ReadsOnly (Λ.Bl₀ G.1 ℓ) (F s h) := by
      intro z z' hz
      unfold F
      rw [Λ.mergedTubeMark_readsOnly G ℓ false s a b h z z' hz]
    exact (isLocal_of_readsOnly hF id).mono (hRead.trans Finset.subset_union_right)
  have hF₀ (h : NestTrace (Λ.X × Λ.X) s.length) (z : Configuration d × Configuration d) :
      0 ≤ F s h z := by unfold F; split_ifs <;> norm_num
  have heq : F (s ++ r) = fun h => F s (e.symm h).1 := by
    funext h z
    have he : e ((e.symm h).1, (e.symm h).2) = h := e.apply_symm_apply h
    have ht := (congrArg (fun f => Λ.mergedTubeMark G ℓ false (s ++ r) a b f z) he.symm).trans
      (Λ.mergedTubeMark_append G ℓ false s r a b (e.symm h).1 (e.symm h).2 ha hb z)
    unfold F
    rw [ht]
  rw [heq]
  exact Rule.marked_prefix_mass_suffix_le hρ γ γ' G s r x hFresh (F s) hFloc hF₀

/-- The occupation bound on a disjoint shared arrival survives further
fresh rows. Both the arrival nests and the disjointness mark are read
from the history up to the arrival. -/
theorem firstGood_disjoint_arrival_mass_suffix_le
    (hρ : 0 < ρ) (γ γ' : SourceRoute D M) (G : Λ.Φ)
    (s r : List PairMove) (x : Λ.X × Λ.X) (ℓ : RouteLabel D)
    (a b i j : ℕ) (ha : a+1 < leftCount s) (hb : b+1 < rightCount s)
    (hi : i < leftCount s) (hj : j < rightCount s)
    (C C' : Finset (Vertex d)) :
    let B (δ : SourceRoute D M) k := Λ.Bl₀ G.1 (routeLab M δ.position k)
    let K (δ : SourceRoute D M) := (Λ.ruleFirstGood M p q ρ κ hκ hs hsite).toNestRule.kernel δ G
    let F (t : List PairMove) (h : NestTrace (Λ.X × Λ.X) t.length) z :=
      if ¬ Λ.mergedTubeMark G ℓ false t a b h z ∧
        (∃ y, mergedArrivalStates? t i j h = some y ∧ C ∈ y.1.1.val ∧ C' ∈ y.2.1.val)
      then (1:ℝ) else 0
    PairFresh (B γ) (B γ') (s ++ r) 0 0 (Λ.S₀ G.1) →
    Λ.Bl₀ G.1 ℓ ⊆ mergedTraceBlocks (B γ) (B γ') s 0 0 →
    markedPrefixMass p q (K γ) (K γ') (s ++ r) 0 0 x (F (s ++ r)) /
      ρ ^ sharedCount (s ++ r) ≤
    markedPrefixMass p q (K γ) (K γ') s 0 0 x (F s) / ρ ^ sharedCount s := by
  intro B K F hFresh hRead
  let Rule := (Λ.ruleFirstGood M p q ρ κ hκ hs hsite).toNestRule
  let e := mergedTraceAppend (Λ.X × Λ.X) s r
  have hFloc (h : NestTrace (Λ.X × Λ.X) s.length) :
      IsLocal (Λ.S₀ G.1 ∪ mergedTraceBlocks (B γ) (B γ') s 0 0) (F s h) := by
    have hF : ReadsOnly (Λ.Bl₀ G.1 ℓ) (F s h) := by
      intro z z' hz
      unfold F
      rw [Λ.mergedTubeMark_readsOnly G ℓ false s a b h z z' hz]
    exact (isLocal_of_readsOnly hF id).mono (hRead.trans Finset.subset_union_right)
  have hF₀ (h : NestTrace (Λ.X × Λ.X) s.length) (z : Configuration d × Configuration d) :
      0 ≤ F s h z := by unfold F; split_ifs <;> norm_num
  have heq : F (s ++ r) = fun h => F s (e.symm h).1 := by
    funext h z
    have he : e ((e.symm h).1, (e.symm h).2) = h := e.apply_symm_apply h
    have ht := (congrArg (fun f => Λ.mergedTubeMark G ℓ false (s ++ r) a b f z) he.symm).trans
      (Λ.mergedTubeMark_append G ℓ false s r a b (e.symm h).1 (e.symm h).2 ha hb z)
    have hy := (congrArg (mergedArrivalStates? (s ++ r) i j) he.symm).trans
      (mergedArrivalStates?_append_of_present s r (e.symm h).1 (e.symm h).2 i j hi hj)
    unfold F
    rw [ht,hy]
  rw [heq]
  exact Rule.marked_prefix_mass_suffix_le hρ γ γ' G s r x hFresh (F s) hFloc hF₀

end NestLayout
end NearCritical.Section10
