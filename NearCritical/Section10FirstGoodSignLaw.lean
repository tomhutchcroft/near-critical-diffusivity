module

public import NearCritical.Section10SharedStepKernel
public import NearCritical.Section10FirstGoodStep

/-! The literal fair-sign factor of the first-good lattice rule. -/
@[expose] public section
noncomputable section
namespace NearCritical.Section10.NestLayout
open scoped Classical

variable {D d : ℕ} (Λ : NestLayout D d) [LinearOrder (Finset (Vertex d))]

/-- On a successful physical move, the actual kernel samples the first-good
next nest and its pending sign independently. The sign factor is exactly
one half and is independent of the tube and the choice of next nest. -/
theorem firstGood_kernel_move_sign_factor (M : ℕ) (p q : unitInterval) (ρ κ : ℝ) (hκ : 0 < κ)
    (hs : ∀ (γ : SourceRoute D M) (G : Λ.Φ) (t : ℕ) (x : Λ.X), ρ⁻¹ ≤
      localSuccessProbability p q (Λ.Bl₀ G.1 (routeLab M γ.position t))
        (bitSet G.2 (fun z => Λ.succσ G (routeLab M γ.position t) x
          (Λ.view G.1 (routeLab M γ.position t) z))))
    (hsiteProb : ∀ s, κ⁻¹ ≤ coupledProb p q (Λ.siteEvent s))
    (γ : SourceRoute D M) (z : Configuration d × Configuration d) (t : ℕ) (x : Λ.X)
    (y : ↥Λ.P) (sign : Bool) :
    let G := refineReveal Λ.ρ₀ Λ.S₀ z
    let ℓ := routeLab M γ.position t
    let view := Λ.view G.1 ℓ z
    Λ.moveCtx G ℓ x → Λ.moveTypical G ℓ x view →
    let T := Λ.Bl₀ G.1 ℓ
    let A := bitSet (T := T) G.2 (fun θ => Λ.succσ G ℓ x (Λ.view G.1 ℓ θ))
    let O := svFirstGoodNext view.1 x.1.val (Λ.fam G ℓ.target)
      (Λ.src G ℓ x.2) (Λ.tgt G ℓ) Λ.k Λ.P
    (Λ.ruleFirstGood M p q ρ κ hκ hs hsiteProb).toNestRule.kernel γ G t x (y,sign) z =
      stepKernel T A (fun _ => O) (localSuccessProbability p q T A) y z / 2 := by
  intro G ℓ view hctx htyp T A O
  let o (b : T → Bool) := Λ.offFirstGood G ℓ x (Λ.view G.1 ℓ (gluePair G.2 b))
  change stepKernel T A o (localSuccessProbability p q T A) (y, sign) z = _
  have hv : Λ.view G.1 ℓ (gluePair G.2 (T.restrict (layerVal z))) = view :=
    glue_fun_eq (Λ.view G.1 ℓ) (Λ.view_readsOnly G.1 ℓ) z
  have hoff : o (T.restrict (layerVal z)) = O.product (Finset.univ : Finset Bool) := by
    dsimp only [o]
    rw [hv, offFirstGood, if_pos ⟨hctx, htyp⟩]
    rfl
  calc
    _ = stepKernel T A (fun _ => O.product (Finset.univ : Finset Bool))
        (localSuccessProbability p q T A) (y, sign) z := by simp only [stepKernel, hoff]
    _ = _ := stepKernel_fair_nextSign T A (fun _ => O) (localSuccessProbability p q T A) y sign z

end NearCritical.Section10.NestLayout
