module

public import NearCritical.Section10FirstGoodPersistence

/-! A continuing phase contracts across a fresh shared physical move. -/

@[expose] public section
noncomputable section

namespace NearCritical.Section10.NestLayout

open MeasureTheory Set
open scoped Classical

variable {D d M : ℕ} (Λ : NestLayout D d) [LinearOrder (Finset (Vertex d))]
  (p q : unitInterval) (ρ κ : ℝ) (hκ : 0 < κ)
  (hs : ∀ (γ : SourceRoute D M) (G : Λ.Φ) (t : ℕ) (x : Λ.X), ρ⁻¹ ≤
    localSuccessProbability p q (Λ.Bl₀ G.1 (routeLab M γ.position t))
      (bitSet G.2 (fun z => Λ.succσ G (routeLab M γ.position t) x
        (Λ.view G.1 (routeLab M γ.position t) z))))
  (hsiteProb : ∀ s, κ⁻¹ ≤ coupledProb p q (Λ.siteEvent s))

/-- The marked mass after appending a shared physical step is at most two
thirds of the past marked mass. Invalid incoming states are assigned zero
continuation weight. -/
theorem firstGood_shared_persistence_prefix
    (hρ : 0 < ρ) (hρ' : ρ ≤ 9/8) (G : Λ.Φ) (γ γ' : SourceRoute D M)
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
    let K := usedMaskedKernel active (Λ.firstGoodMaskBase p q ρ κ hκ hs hsiteProb γ G active)
    let K' := usedMaskedKernel active' (Λ.firstGoodMaskBase p q ρ κ hκ hs hsiteProb γ' G active')
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
    (∫ z, ∑ h : NestTrace (Λ.X × Λ.X) s.length, ∑ y : Λ.X × Λ.X,
      (F h z * E h y z) * mergedTraceMass K K' z (s ++ [.both]) t t' x
        (mergedTraceAppend (Λ.X × Λ.X) s [.both] (h,(y,PUnit.unit))) ∂μ) ≤
      (2/3:ℝ) * (∫ z, ∑ h : NestTrace (Λ.X × Λ.X) s.length,
        F h z * mergedTraceMass K K' z s t t' x h ∂μ) := by
  intro μ j j' B B' ℓ ℓ' K K' E hF hF₀ hj hj' hd hrare
  have hk := Λ.firstGood_usedKernel_isLocal p q ρ κ hκ hs hsiteProb γ G active
  have hk' := Λ.firstGood_usedKernel_isLocal p q ρ κ hκ hs hsiteProb γ' G active'
  have hk₀ := Λ.firstGood_usedKernel_nonneg p q ρ κ hκ hs hsiteProb hρ γ G active
  have hk'₀ := Λ.firstGood_usedKernel_nonneg p q ρ κ hκ hs hsiteProb hρ γ' G active'
  refine mergedTrace_marked_snoc_integral_le p q B B' K K' hk hk' hk₀ hk'₀
    s .both t t' x R F E hF hF₀ hd ?_ ?_
  · intro h y
    let u := mergedTraceLast s x h
    have hl := Λ.firstGoodSharedTubeMark_readsOnly G ℓ u.1.1.val u.2.1.val y.1.2 y.2.2
    have hv := isLocal_of_readsOnly hl
      (fun P : Prop => if Λ.moveCtx G ℓ u.1 ∧ Λ.moveCtx G ℓ' u.2 ∧ P then (1:ℝ) else 0)
    exact hv.mono Finset.subset_union_left
  · intro h
    let u := mergedTraceLast s x h
    by_cases hu : Λ.moveCtx G ℓ u.1 ∧ Λ.moveCtx G ℓ' u.2
    · have hb := Λ.firstGood_shared_persistence_row p q ρ κ hκ hs hsiteProb hρ hρ'
        G γ γ' j j' active active' hj hj' u.1 u.2 hu.1 hu.2 (hrare u.1 u.2 hu.1 hu.2)
      refine le_trans ?_ hb
      apply le_of_eq
      apply integral_congr_ae
      refine Filter.Eventually.of_forall fun z => Finset.sum_congr rfl fun y _ => ?_
      change (if Λ.moveCtx G ℓ u.1 ∧ Λ.moveCtx G ℓ' u.2 ∧
          Λ.firstGoodSharedTubeMark G ℓ u.1.1.val u.2.1.val y.1.2 y.2.2 z then (1:ℝ) else 0) *
        (K j u.1 y.1 z * K' j' u.2 y.2 z) = _
      let A : Set (Configuration d × Configuration d) :=
        {w | Λ.firstGoodSharedTubeMark G ℓ u.1.1.val u.2.1.val y.1.2 y.2.2 w}
      change _ = A.indicator (fun w => K j u.1 y.1 w * K' j' u.2 y.2 w) z
      by_cases hm : z ∈ A
      · have hmark : Λ.firstGoodSharedTubeMark G ℓ u.1.1.val u.2.1.val y.1.2 y.2.2 z := hm
        rw [if_pos ⟨hu.1,hu.2,hmark⟩, one_mul, Set.indicator_of_mem hm]
      · have hmark : ¬ Λ.firstGoodSharedTubeMark G ℓ u.1.1.val u.2.1.val y.1.2 y.2.2 z := hm
        rw [if_neg (fun h => hmark h.2.2), zero_mul, Set.indicator_of_notMem hm]
    · change (∫ z, ∑ y : Λ.X × Λ.X, E h y z * (K j u.1 y.1 z * K' j' u.2 y.2 z) ∂μ) ≤ _
      have hzero (y : Λ.X × Λ.X) (z : Configuration d × Configuration d) : E h y z = 0 := by
        change (if Λ.moveCtx G ℓ u.1 ∧ Λ.moveCtx G ℓ' u.2 ∧ _ then (1:ℝ) else 0) = 0
        exact if_neg (fun h => hu ⟨h.1,h.2.1⟩)
      simp only [hzero, zero_mul, Finset.sum_const_zero, integral_zero]
      norm_num

end NearCritical.Section10.NestLayout
