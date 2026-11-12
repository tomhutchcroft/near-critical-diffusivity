module

public import NearCritical.Section10FirstGoodSignSupport
public import NearCritical.Section10MaskedSignTrace

/-! The actual first-good rows in the pending-sign representation. -/

@[expose] public section
noncomputable section

namespace NearCritical.Section10.NestLayout

open scoped Classical

variable {D d M : ℕ} (Λ : NestLayout D d) [LinearOrder (Finset (Vertex d))]
  (p q : unitInterval) (ρ κ : ℝ) (hκ : 0 < κ)
  (hs : ∀ (γ : SourceRoute D M) (G : Λ.Φ) (t : ℕ) (x : Λ.X), ρ⁻¹ ≤
    localSuccessProbability p q (Λ.Bl₀ G.1 (routeLab M γ.position t))
      (bitSet G.2 (fun z => Λ.succσ G (routeLab M γ.position t) x
        (Λ.view G.1 (routeLab M γ.position t) z))))
  (hsiteProb : ∀ s, κ⁻¹ ≤ coupledProb p q (Λ.siteEvent s))

/-- The start and physical moves draw a new sign. On all other steps the
kernel is sign-independent apart from keeping the sign unchanged. -/
def firstGoodMaskBase (γ : SourceRoute D M) (G : Λ.Φ) (active : ℕ → Bool)
    (t : ℕ) (N : ↥Λ.P) (a : Bool) (N' : ↥Λ.P)
    (z : Configuration d × Configuration d) : ℝ :=
  let K := (Λ.ruleFirstGood M p q ρ κ hκ hs hsiteProb).toNestRule.kernel γ G
  if active t = true then 2 * K t (N,a) (N',false) z
  else K t (N,false) (N',false) z

theorem firstGood_kernel_eq_pendingMasked
    (γ : SourceRoute D M) (z : Configuration d × Configuration d) (active : ℕ → Bool)
    (t : ℕ) (N N' : ↥Λ.P) (a b : Bool) :
    let G := refineReveal Λ.ρ₀ Λ.S₀ z
    let ℓ := routeLab M γ.position t
    (active t = true → Λ.startCtx G ℓ ∨ Λ.moveCtx G ℓ (N,a)) →
    (active t ≠ true → ¬ Λ.startCtx G ℓ ∧ ¬ Λ.moveCtx G ℓ (N,a)) →
    (Λ.ruleFirstGood M p q ρ κ hκ hs hsiteProb).toNestRule.kernel γ G t (N,a) (N',b) z =
      pendingMaskedKernel active (Λ.firstGoodMaskBase p q ρ κ hκ hs hsiteProb γ G active)
        t (N,a) (N',b) z := by
  intro G ℓ hactive hinactive
  let K := (Λ.ruleFirstGood M p q ρ κ hκ hs hsiteProb).toNestRule.kernel γ G
  by_cases ht : active t = true
  · have he : K t (N,a) (N',b) z = K t (N,a) (N',false) z := by
      rcases hactive ht with hstart | hmove
      · exact (Λ.firstGood_kernel_start_sign_factor M p q ρ κ hκ hs hsiteProb γ z
          t (N,a) N' b hstart).trans
          (Λ.firstGood_kernel_start_sign_factor M p q ρ κ hκ hs hsiteProb γ z
            t (N,a) N' false hstart).symm
      · by_cases htyp : Λ.moveTypical G ℓ (N,a) (Λ.view G.1 ℓ z)
        · exact (Λ.firstGood_kernel_move_sign_factor M p q ρ κ hκ hs hsiteProb γ z
            t (N,a) N' b hmove htyp).trans
            (Λ.firstGood_kernel_move_sign_factor M p q ρ κ hκ hs hsiteProb γ z
              t (N,a) N' false hmove htyp).symm
        · exact (Λ.firstGood_kernel_move_failed_zero M p q ρ κ hκ hs hsiteProb γ z
            t (N,a) (N',b) hmove htyp).trans
            (Λ.firstGood_kernel_move_failed_zero M p q ρ κ hκ hs hsiteProb γ z
              t (N,a) (N',false) hmove htyp).symm
    simp only [pendingMaskedKernel, firstGoodMaskBase, if_pos ht]
    change K t (N,a) (N',b) z = 2 * K t (N,a) (N',false) z / 2
    rw [he]
    ring
  · obtain ⟨hstart, hmove⟩ := hinactive ht
    have hmove' : ¬ Λ.moveCtx G ℓ (N,false) := hmove
    have ha := Λ.firstGood_kernel_inactive_row M p q ρ κ hκ hs hsiteProb γ z
      t N N' a b hstart hmove
    have hf := Λ.firstGood_kernel_inactive_row M p q ρ κ hκ hs hsiteProb γ z
      t N N' false false hstart hmove'
    simp only [if_true] at hf
    simp only [pendingMaskedKernel, firstGoodMaskBase, if_neg ht]
    change K t (N,a) (N',b) z = if b = a then K t (N,false) (N',false) z else 0
    change K t (N,a) (N',b) z = _ at ha
    change K t (N,false) (N',false) z = _ at hf
    rw [ha, hf]

/-- The sign present before the start is a dummy. The actual start row
ignores it, so it can be summed against an independent uniform sign. -/
theorem firstGood_kernel_start_incoming_sign
    (γ : SourceRoute D M) (z : Configuration d × Configuration d) (t : ℕ)
    (N N' : ↥Λ.P) (a b c : Bool) :
    let G := refineReveal Λ.ρ₀ Λ.S₀ z
    let ℓ := routeLab M γ.position t
    Λ.startCtx G ℓ →
    (Λ.ruleFirstGood M p q ρ κ hκ hs hsiteProb).toNestRule.kernel γ G t (N,a) (N',c) z =
      (Λ.ruleFirstGood M p q ρ κ hκ hs hsiteProb).toNestRule.kernel γ G t (N,b) (N',c) z := by
  intro G ℓ hstart
  have hkind : ∀ l : RouteLabel D, l.isStart → ¬ l.isStep ∧ ¬ l.isExit := by
    intro l
    cases l <;> simp [RouteLabel.isStart, RouteLabel.isStep, RouteLabel.isExit]
  obtain ⟨hstep, hexit⟩ := hkind ℓ hstart.1
  let T := Λ.Bl₀ G.1 ℓ
  let A (sign : Bool) := bitSet (T := T) G.2
    (fun θ => Λ.succσ G ℓ (N,sign) (Λ.view G.1 ℓ θ))
  have hfull (sign : Bool) : A sign = Set.univ := by
    ext ξ
    change Λ.succσ G ℓ (N,sign) (Λ.view G.1 ℓ (gluePair G.2 ξ)) ↔ True
    have hm : ¬ Λ.moveCtx G ℓ (N,sign) := fun h => hstep h.1
    have he : ¬ Λ.exitCtx G ℓ (N,sign) := fun h => hexit h.1
    simp [succσ, hm, he]
  have ha := Λ.firstGood_kernel_start_sign_factor M p q ρ κ hκ hs hsiteProb γ z
    t (N,a) N' c hstart
  have hb := Λ.firstGood_kernel_start_sign_factor M p q ρ κ hκ hs hsiteProb γ z
    t (N,b) N' c hstart
  let O := Λ.P.attach.filter (fun N' => N'.val.card = Λ.k ∧ N'.val ⊆ Λ.fam G ℓ.site)
  calc
    _ = stepKernel T (A a) (fun _ => O) (localSuccessProbability p q T (A a)) N' z / 2 := ha
    _ = stepKernel T (A b) (fun _ => O) (localSuccessProbability p q T (A b)) N' z / 2 := by
      rw [hfull a, hfull b]
    _ = _ := hb.symm

end NearCritical.Section10.NestLayout
