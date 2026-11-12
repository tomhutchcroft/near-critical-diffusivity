module

public import NearCritical.Section10FirstGoodInitialLaw
public import NearCritical.Section10SharedMarkRecurrence

/-! Normalized pair occupation and site collision at a common root. -/

@[expose] public section
noncomputable section

namespace NearCritical.Section10

open MeasureTheory
open scoped Classical

private theorem markedPrefixMass_one_shared {d : ℕ} {X Y : Type*} [Fintype X] [Fintype Y]
    (p q : unitInterval)
    (K : ℕ → X → X → Configuration d × Configuration d → ℝ)
    (K' : ℕ → Y → Y → Configuration d × Configuration d → ℝ)
    (x : X × Y) (E : X × Y → ℝ) :
    markedPrefixMass p q K K' [.both] 0 0 x (fun h _ => E h.1) =
      ∫ z, ∑ y : X × Y, E y * (K 0 x.1 y.1 z * K' 0 x.2 y.2 z)
        ∂((percolation d p).prod (percolation d q)) := by
  apply integral_congr_ae
  refine Filter.Eventually.of_forall fun z => ?_
  change (∑ h : (X × Y) × PUnit, E h.1 *
    mergedTraceMass K K' z [.both] 0 0 x h) = _
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp [mergedTraceMass, pairMoveKernel] <;> exact Or.inl rfl

namespace NestLayout

set_option maxHeartbeats 500000 in
/-- At a common root, the two initial nest marginals multiply. The
normalized collision mass is at most `k² / |S|`. -/
theorem firstGood_common_root_normalized_mass
    {D d M : ℕ} (Λ : NestLayout D d) [LinearOrder (Finset (Vertex d))]
    (p q : unitInterval) (ρ κ : ℝ) (hκ : 0 < κ) (hρ : 1 ≤ ρ)
    (hs : ∀ (γ : SourceRoute D M) (G : Λ.Φ) (j : ℕ) (x : Λ.X), ρ⁻¹ ≤
      localSuccessProbability p q (Λ.Bl₀ G.1 (routeLab M γ.position j))
        (bitSet G.2 (fun z => Λ.succσ G (routeLab M γ.position j) x
          (Λ.view G.1 (routeLab M γ.position j) z))))
    (hsite : ∀ s, κ⁻¹ ≤ coupledProb p q (Λ.siteEvent s))
    (γ γ' : SourceRoute D M) (G : Λ.Φ) (x x' : Λ.X) :
    let ℓ := routeLab M γ.position 0
    let S := Λ.fam G ℓ.site
    let L := (Λ.ruleFirstGood M p q ρ κ hκ hs hsite).toNestRule.kernel
    let mass (P : Λ.X × Λ.X → Prop) [DecidablePred P] :=
      markedPrefixMass p q (L γ G) (L γ' G) [.both] 0 0 (x,x')
        (fun h _ => if P h.1 then 1 else 0) / ρ ^ sharedCount [.both]
    routeLab M γ'.position 0 = ℓ → Λ.startCtx G ℓ →
    (∀ c ∈ S, ∀ c' ∈ S, mass (fun y => c ∈ y.1.1.val ∧ c' ∈ y.2.1.val) ≤ ((Λ.k:ℝ)/S.card)^2) ∧
    mass (fun y => (y.1.1.val ∩ y.2.1.val).Nonempty) ≤ (Λ.k:ℝ)^2 / S.card := by
  intro ℓ S L mass he hstart
  let μ := (percolation d p).prod (percolation d q)
  have hmass (P : Λ.X × Λ.X → Prop) [DecidablePred P] (C : ℝ) (hC : 0 ≤ C)
      (hrow : ∀ z, (∑ y : Λ.X × Λ.X,
        if P y then L γ G 0 x y.1 z * L γ' G 0 x' y.2 z else 0) ≤ C) :
      mass P ≤ C := by
    change markedPrefixMass p q (L γ G) (L γ' G) [.both] 0 0 (x,x')
      (fun h _ => if P h.1 then (1:ℝ) else 0) / ρ ^ sharedCount [.both] ≤ C
    rw [markedPrefixMass_one_shared p q (L γ G) (L γ' G) (x,x')
      (fun y => if P y then (1:ℝ) else 0), show sharedCount [.both] = 1 from rfl, pow_one]
    have hI : (∫ z, ∑ y : Λ.X × Λ.X, (if P y then (1:ℝ) else 0) *
        (L γ G 0 x y.1 z * L γ' G 0 x' y.2 z) ∂μ) ≤ C := by
      calc
        _ ≤ ∫ _z, C ∂μ := by
          refine integral_mono_of_nonneg (Filter.Eventually.of_forall ?_) (integrable_const C)
            (Filter.Eventually.of_forall ?_)
          · intro z
            refine Finset.sum_nonneg fun y _ => ?_
            have hl : 0 ≤ L γ G 0 x y.1 z := stepKernel_nonneg _ _ _
              ((inv_nonneg.mpr (zero_le_one.trans hρ)).trans (hs γ G 0 x)) y.1 z
            have hr : 0 ≤ L γ' G 0 x' y.2 z := stepKernel_nonneg _ _ _
              ((inv_nonneg.mpr (zero_le_one.trans hρ)).trans (hs γ' G 0 x')) y.2 z
            have hprod : 0 ≤ L γ G 0 x y.1 z * L γ' G 0 x' y.2 z := mul_nonneg hl hr
            split_ifs
            · simpa only [one_mul] using hprod
            · rw [zero_mul]
          · intro z
            simpa only [ite_mul, one_mul, zero_mul] using hrow z
        _ = C := by rw [integral_const, probReal_univ, one_smul]
    exact (div_le_div_of_nonneg_right hI (zero_le_one.trans hρ)).trans (div_le_self hC hρ)
  constructor
  · intro c hc c' hc'
    exact hmass (fun y => c ∈ y.1.1.val ∧ c' ∈ y.2.1.val) (((Λ.k:ℝ)/S.card)^2) (sq_nonneg _)
      (fun z => le_of_eq ((Λ.firstGood_common_root_collision p q ρ κ hκ hs hsite γ γ' G 0 0 x x' z he hstart).1
        c hc c' hc'))
  · exact hmass (fun y => (y.1.1.val ∩ y.2.1.val).Nonempty) ((Λ.k:ℝ)^2 / S.card)
      (div_nonneg (sq_nonneg _) (Nat.cast_nonneg _))
      (fun z => (Λ.firstGood_common_root_collision p q ρ κ hκ hs hsite γ γ' G 0 0 x x' z he hstart).2)

end NestLayout
end NearCritical.Section10
