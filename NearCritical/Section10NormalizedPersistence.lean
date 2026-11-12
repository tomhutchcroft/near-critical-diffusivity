module

public import NearCritical.Section10FirstGoodPhasePrefix
public import NearCritical.Section10SharedMarkRecurrence

/-! The contraction for a shared physical move in the normalization
used by the tube recurrence. -/

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

/-- If a previous mark is carried in `F`, the next shared bridge retains
at most two thirds of its normalized mass. -/
theorem firstGood_shared_persistence_normalized_le
    (hρ : 1 ≤ ρ) (hρ' : ρ ≤ 9/8) (G : Λ.Φ) (γ γ' : SourceRoute D M)
    (active active' : ℕ → Bool) (s : List PairMove) (t t' : ℕ) (x : Λ.X × Λ.X)
    (R : Finset (LBond d))
    (F : NestTrace (Λ.X × Λ.X) s.length → Configuration d × Configuration d → ℝ) :
    let μ := (percolation d p).prod (percolation d q)
    let j := t + leftCount s
    let j' := t' + rightCount s
    let B := fun i => Λ.Bl₀ G.1 (routeLab M γ.position i)
    let B' := fun i => Λ.Bl₀ G.1 (routeLab M γ'.position i)
    let ℓ := routeLab M γ.position j
    let ℓ' := routeLab M γ'.position j'
    let K := usedMaskedKernel active (Λ.firstGoodMaskBase p q ρ κ hκ hs hsite γ G active)
    let K' := usedMaskedKernel active' (Λ.firstGoodMaskBase p q ρ κ hκ hs hsite γ' G active')
    let E (h : NestTrace (Λ.X × Λ.X) s.length) (y : Λ.X × Λ.X)
        (z : Configuration d × Configuration d) :=
      let u := mergedTraceLast s x h
      if Λ.moveCtx G ℓ u.1 ∧ Λ.moveCtx G ℓ' u.2 ∧
          Λ.firstGoodSharedTubeMark G ℓ u.1.1.val u.2.1.val y.1.2 y.2.2 z
        then (1:ℝ) else 0
    (∀ h, IsLocal (R ∪ mergedTraceBlocks B B' s t t') (F h)) →
    (∀ h z, 0 ≤ F h z) →
    active j = true → active' j' = true →
    Disjoint (R ∪ mergedTraceBlocks B B' s t t') (pairMoveBlock B B' .both j j') →
    (∀ u v : Λ.X, Λ.moveCtx G ℓ u → Λ.moveCtx G ℓ' v → ∀ a b, a ≠ b →
      μ.real {z | Λ.firstGoodSharedTubeMark G ℓ u.1.val v.1.val a b z} ≤ 1/40) →
    markedPrefixMass p q K K' (s ++ [.both]) t t' x (fun h z =>
      let g := (mergedTraceAppend (Λ.X × Λ.X) s [.both]).symm h
      F g.1 z * E g.1 g.2.1 z) / ρ ^ sharedCount (s ++ [.both]) ≤
      (2/3:ℝ) * (markedPrefixMass p q K K' s t t' x F / ρ ^ sharedCount s) := by
  intro μ j j' B B' ℓ ℓ' K K' E hF hF₀ hj hj' hd hrare
  have hpos : 0 < ρ := zero_lt_one.trans_le hρ
  have hraw : markedPrefixMass p q K K' (s ++ [.both]) t t' x (fun h z =>
      let g := (mergedTraceAppend (Λ.X × Λ.X) s [.both]).symm h
      F g.1 z * E g.1 g.2.1 z) ≤ (2/3:ℝ) * markedPrefixMass p q K K' s t t' x F := by
    rw [markedPrefixMass_snoc p q K K' s .both t t' x (fun h y z => F h z * E h y z)]
    exact Λ.firstGood_shared_persistence_prefix p q ρ κ hκ hs hsite hpos hρ' G γ γ'
      active active' s t t' x R F hF hF₀ hj hj' hd hrare
  have hk := Λ.firstGood_usedKernel_nonneg p q ρ κ hκ hs hsite hpos γ G active
  have hk' := Λ.firstGood_usedKernel_nonneg p q ρ κ hκ hs hsite hpos γ' G active'
  have hmass : 0 ≤ markedPrefixMass p q K K' s t t' x F :=
    integral_nonneg fun z => Finset.sum_nonneg fun h _ =>
      mul_nonneg (hF₀ h z) (mergedTraceMass_nonneg K K' hk hk' z s t t' x h)
  have hden : ρ ^ sharedCount s ≤ ρ ^ sharedCount (s ++ [.both]) := by
    rw [sharedCount_append, pow_add, show sharedCount [.both] = 1 from rfl, pow_one]
    exact le_mul_of_one_le_right (pow_nonneg hpos.le _) hρ
  calc
    _ ≤ ((2/3:ℝ) * markedPrefixMass p q K K' s t t' x F) / ρ ^ sharedCount (s ++ [.both]) :=
      div_le_div_of_nonneg_right hraw (pow_nonneg hpos.le _)
    _ ≤ ((2/3:ℝ) * markedPrefixMass p q K K' s t t' x F) / ρ ^ sharedCount s :=
      div_le_div_of_nonneg_left (mul_nonneg (by norm_num) hmass) (pow_pos hpos _) hden
    _ = _ := by rw [mul_div_assoc]

end NearCritical.Section10.NestLayout
