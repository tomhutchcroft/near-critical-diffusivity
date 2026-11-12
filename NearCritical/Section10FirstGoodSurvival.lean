module

public import NearCritical.Section10FirstGoodStep

/-! Positive transitions of the first-good lattice rule are admissible for
the geometric certificate of the original lattice rule. -/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open MeasureTheory
open scoped Classical

private theorem stepKernel_pos_of_offspring_subset {d : ℕ} {X : Type*}
    (T : Finset (LBond d)) (a : Set (T → Bool)) (o₁ o₂ : (T → Bool) → Finset X)
    (s : ℝ) (y : X) (z : Configuration d × Configuration d)
    (hsub : ∀ b, o₁ b ⊆ o₂ b) (h : 0 < stepKernel T a o₁ s y z) :
    0 < stepKernel T a o₂ s y z := by
  obtain ⟨ha, hy⟩ := stepKernel_pos T a o₁ s y z h
  have hy₂ := hsub _ hy
  unfold stepKernel at h ⊢
  rw [if_pos ⟨ha, hy⟩] at h
  rw [if_pos ⟨ha, hy₂⟩]
  have hs := pos_of_mul_pos_left (inv_pos.mp h) (Nat.cast_nonneg _)
  exact inv_pos.mpr (mul_pos hs (Nat.cast_pos.mpr (Finset.card_pos.mpr ⟨y, hy₂⟩)))

namespace NestLayout

variable {D d : ℕ} (Λ : NestLayout D d) [LinearOrder (Finset (Vertex d))]
  (M : ℕ) (p q : unitInterval) (ϱ κ : ℝ) (hκ : 0 < κ)
  (hs : ∀ (γ : SourceRoute D M) (G : Λ.Φ) (t : ℕ) (x : Λ.X), ϱ⁻¹ ≤
    localSuccessProbability p q (Λ.Bl₀ G.1 (routeLab M γ.position t))
      (bitSet G.2 (fun z => Λ.succσ G (routeLab M γ.position t) x
        (Λ.view G.1 (routeLab M γ.position t) z))))
  (hsiteProb : ∀ s, κ⁻¹ ≤ coupledProb p q (Λ.siteEvent s))

/-- Both rules use the same success event. Restricting the offspring finset
preserves admissibility of each positive first-good transition. -/
theorem firstGood_kernel_pos_implies_rule_kernel_pos (γ : SourceRoute D M) (G : Λ.Φ)
    (t : ℕ) (x y : Λ.X) (z : Configuration d × Configuration d)
    (h : 0 < (Λ.ruleFirstGood M p q ϱ κ hκ hs hsiteProb).toNestRule.kernel γ G t x y z) :
    0 < (Λ.rule M p q ϱ κ hκ hs hsiteProb).toNestRule.kernel γ G t x y z := by
  let ℓ := routeLab M γ.position t
  let T := Λ.Bl₀ G.1 ℓ
  let a := bitSet (T := T) G.2 (fun θ => Λ.succσ G ℓ x (Λ.view G.1 ℓ θ))
  let o₁ (b : T → Bool) := Λ.offFirstGood G ℓ x (Λ.view G.1 ℓ (gluePair G.2 b))
  let o₂ (b : T → Bool) := Λ.offσ G ℓ x (Λ.view G.1 ℓ (gluePair G.2 b))
  exact stepKernel_pos_of_offspring_subset T a o₁ o₂ (localSuccessProbability p q T a) y z
    (fun b => Λ.offFirstGood_subset G ℓ x (Λ.view G.1 ℓ (gluePair G.2 b))) h

/-- A surviving first-good chain can be used in the existing lattice path
certificate, with the same route, states and configuration. -/
theorem firstGood_survives_implies_rule_survives (γ : SourceRoute D M) (G : Λ.Φ)
    (z : Configuration d × Configuration d) (m t : ℕ) (x : Λ.X)
    (h : ChainSurvives ((Λ.ruleFirstGood M p q ϱ κ hκ hs hsiteProb).toNestRule.kernel γ G)
      m t x z) :
    ChainSurvives ((Λ.rule M p q ϱ κ hκ hs hsiteProb).toNestRule.kernel γ G) m t x z := by
  induction m generalizing t x with
  | zero => exact True.intro
  | succ m ih =>
    obtain ⟨y, hpos, htail⟩ := h
    exact ⟨y, Λ.firstGood_kernel_pos_implies_rule_kernel_pos M p q ϱ κ hκ hs hsiteProb
      γ G t x y z hpos, ih (t + 1) y htail⟩

/-- At a positive moving transition, the next nest is drawn from the
offspring of the actual first good representative. -/
theorem firstGood_kernel_move_uses_representative (γ : SourceRoute D M)
    (z : Configuration d × Configuration d) (t : ℕ) (x y : Λ.X) :
    let G := refineReveal Λ.ρ₀ Λ.S₀ z
    let ℓ := routeLab M γ.position t
    let view := Λ.view G.1 ℓ z
    Λ.moveCtx G ℓ x →
    0 < (Λ.ruleFirstGood M p q ϱ κ hκ hs hsiteProb).toNestRule.kernel γ G t x y z →
    let offspring := svOffOf view.1 x.1.val (Λ.fam G ℓ.target) (Λ.src G ℓ x.2) (Λ.tgt G ℓ)
    ∃ h : (goodNestRepresentatives x.1.val offspring Λ.k).Nonempty,
      let rep := nestRepresentative x.1.val offspring Λ.k h
      rep ∈ x.1.val ∧ y.1.val.card = Λ.k ∧ y.1.val ⊆ offspring rep := by
  intro G ℓ view hctx hpos
  have hk := (Λ.ruleFirstGood M p q ϱ κ hκ hs hsiteProb).kernel_pos γ z t x y hpos
  have htyp : Λ.moveTypical G ℓ x view := hk.1.1 hctx
  have hoff : y ∈ Λ.offFirstGood G ℓ x view := hk.2
  unfold offFirstGood at hoff
  rw [if_pos ⟨hctx, htyp⟩] at hoff
  have hn := (Finset.mem_product.mp hoff).1
  unfold svFirstGoodNext at hn
  split at hn
  next h =>
    obtain ⟨_, hcard, hsub⟩ := Finset.mem_filter.mp hn
    exact ⟨h, (nestRepresentative_spec _ _ _ h).1, hcard, hsub⟩
  next _ => exact (Finset.notMem_empty _ hn).elim

end NestLayout
end NearCritical.Section10
