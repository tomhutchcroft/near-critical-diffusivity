module

public import NearCritical.Section10FirstGoodBridgeMark
public import NearCritical.Section10FirstGoodMaskedKernel

/-! The normalized persistence row for an actual shared first-good transition. -/

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

/-- Fixing the destination sign costs exactly one half of the normalized row
bound. This holds on all fresh bits with the reveal kept fixed. -/
theorem firstGood_move_sign_row_le (hρ : 0 < ρ) (γ : SourceRoute D M)
    (G : Λ.Φ) (t : ℕ) (x : Λ.X) (z : Configuration d × Configuration d)
    (hctx : Λ.moveCtx G (routeLab M γ.position t) x) :
    let K := (Λ.ruleFirstGood M p q ρ κ hκ hs hsiteProb).toNestRule.kernel γ G
    (∀ y, 0 ≤ K t x y z) ∧ (∑ y : ↥Λ.P, K t x (y,false) z) ≤ ρ / 2 := by
  let R := (Λ.ruleFirstGood M p q ρ κ hκ hs hsiteProb).toNestRule
  let ℓ := routeLab M γ.position t
  let T := Λ.Bl₀ G.1 ℓ
  let A : Set (T → Bool) := R.a γ G t x
  let O : (T → Bool) → Finset Λ.X := R.o γ G t x
  let s := localSuccessProbability p q T A
  have hs' : ρ⁻¹ ≤ s := hs γ G t x
  have hs0 : 0 < s := (inv_pos.mpr hρ).trans_le hs'
  change (∀ y, 0 ≤ stepKernel T A O s y z) ∧
    (∑ y : ↥Λ.P, stepKernel T A O s (y,false) z) ≤ ρ / 2
  refine ⟨fun y => stepKernel_nonneg T A O hs0.le y z, ?_⟩
  have htot := stepKernel_sum T A O (R.ho γ G t x) s z
  have hupper : (∑ y : Λ.X, stepKernel T A O s y z) ≤ ρ := by
    rw [htot]
    split_ifs
    · rw [one_mul]
      exact (inv_le_comm₀ hs0 hρ).mpr hs'
    · rw [zero_mul]
      exact hρ.le
  have heq (y : ↥Λ.P) (b : Bool) :
      stepKernel T A O s (y,b) z = stepKernel T A O s (y,false) z := by
    let ξ := T.restrict (layerVal z)
    by_cases hz : ξ ∈ A
    · let v := Λ.view G.1 ℓ (gluePair G.2 ξ)
      have hsucc : Λ.succσ G ℓ x v := hz
      have hO : O ξ =
          (svFirstGoodNext v.1 x.1.val (Λ.fam G ℓ.target)
            (Λ.src G ℓ x.2) (Λ.tgt G ℓ) Λ.k Λ.P).product (Finset.univ : Finset Bool) := by
        change Λ.offFirstGood G ℓ x v = _
        rw [offFirstGood, if_pos ⟨hctx, hsucc.1 hctx⟩]
        rfl
      change O (T.restrict (layerVal z)) = _ at hO
      unfold stepKernel
      rw [hO]
      simp only [Finset.product_eq_sprod, Finset.mem_product, Finset.mem_univ, and_true]
    · unfold stepKernel
      split_ifs <;> first | rfl | (exfalso; apply hz; tauto)
  rw [Fintype.sum_prod_type] at hupper
  change (∑ y : ↥Λ.P, ∑ b : Bool, stepKernel T A O s (y,b) z) ≤ ρ at hupper
  simp_rw [heq]
    at hupper
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_bool, nsmul_eq_mul,
    Nat.cast_ofNat, ← Finset.mul_sum] at hupper
  linarith

/-- If the entire read set is fresh, the frozen intersection mark agrees
with the raw bridge event throughout the product sample. -/
theorem firstGoodSharedTubeMark_iff_raw_of_fresh (G : Λ.Φ) (ℓ : RouteLabel D)
    (hfresh : Disjoint (Λ.readSet G.1 ℓ) (Λ.S₀ G.1))
    (N N' : Finset (Finset (Vertex d))) (a b : Bool) (z : Configuration d × Configuration d) :
    Λ.firstGoodSharedTubeMark G ℓ N N' a b z ↔
      (Λ.firstGoodNestBridge G ℓ N a z ∩ Λ.firstGoodNestBridge G ℓ N' b z).Nonempty := by
  have hbridge (P : Finset (Finset (Vertex d))) (s : Bool) :
      Λ.firstGoodNestBridge G ℓ P s (gluePair G.2 ((Λ.Bl₀ G.1 ℓ).restrict (layerVal z))) =
        Λ.firstGoodNestBridge G ℓ P s z := by
    apply rawBridge_readsOnly
    intro e he
    have hr : e ∈ Λ.readSet G.1 ℓ := Finset.mem_union_left _ he
    have hs : e ∉ Λ.S₀ G.1 := fun h => (Finset.disjoint_left.mp hfresh) hr h
    have hT : e ∈ Λ.Bl₀ G.1 ℓ := Finset.mem_sdiff.mpr ⟨hr,hs⟩
    rw [layerVal_gluePair, dif_neg hs, dif_pos hT]
    rfl
  dsimp only [firstGoodSharedTubeMark]
  rw [hbridge N a, hbridge N' b]

end NearCritical.Section10.NestLayout
