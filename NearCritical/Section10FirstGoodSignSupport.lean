module

public import NearCritical.Section10FirstGoodSignLaw

/-! Sign behavior of the actual rule at the start, on a failed physical move,
and on a row that retains the current state. -/

@[expose] public section
noncomputable section

namespace NearCritical.Section10.NestLayout

open scoped Classical

variable {D d : ℕ} (Λ : NestLayout D d) [LinearOrder (Finset (Vertex d))]
  (M : ℕ) (p q : unitInterval) (ρ κ : ℝ) (hκ : 0 < κ)
  (hs : ∀ (γ : SourceRoute D M) (G : Λ.Φ) (t : ℕ) (x : Λ.X), ρ⁻¹ ≤
    localSuccessProbability p q (Λ.Bl₀ G.1 (routeLab M γ.position t))
      (bitSet G.2 (fun z => Λ.succσ G (routeLab M γ.position t) x
        (Λ.view G.1 (routeLab M γ.position t) z))))
  (hsiteProb : ∀ s, κ⁻¹ ≤ coupledProb p q (Λ.siteEvent s))

/-- A physical move that fails its typicality test has zero mass for every
next nest and sign. -/
theorem firstGood_kernel_move_failed_zero
    (γ : SourceRoute D M) (z : Configuration d × Configuration d) (t : ℕ) (x y : Λ.X) :
    let G := refineReveal Λ.ρ₀ Λ.S₀ z
    let ℓ := routeLab M γ.position t
    Λ.moveCtx G ℓ x →
    ¬ Λ.moveTypical G ℓ x (Λ.view G.1 ℓ z) →
    (Λ.ruleFirstGood M p q ρ κ hκ hs hsiteProb).toNestRule.kernel γ G t x y z = 0 := by
  intro G ℓ hctx hfail
  let T := Λ.Bl₀ G.1 ℓ
  let S := fun θ => Λ.succσ G ℓ x (Λ.view G.1 ℓ θ)
  let A := bitSet (T := T) G.2 S
  let O := fun b : T → Bool => Λ.offFirstGood G ℓ x (Λ.view G.1 ℓ (gluePair G.2 b))
  change stepKernel T A O (localSuccessProbability p q T A) y z = 0
  have hreads : ReadsOnly (Λ.S₀ G.1 ∪ T) S :=
    (Λ.view_readsOnly G.1 ℓ).comp _
  have hA : T.restrict (layerVal z) ∉ A := by
    intro ha
    have hsucc := (bitSet_iff S hreads z).mp ha
    exact hfail (hsucc.1 hctx)
  have hz : ¬ (T.restrict (layerVal z) ∈ A ∧ y ∈ O (T.restrict (layerVal z))) :=
    fun h => hA h.1
  exact if_neg hz

/-- At the start the next sign is uniform and independent of the selected
initial nest. -/
theorem firstGood_kernel_start_sign_factor
    (γ : SourceRoute D M) (z : Configuration d × Configuration d) (t : ℕ) (x : Λ.X)
    (y : ↥Λ.P) (sign : Bool) :
    let G := refineReveal Λ.ρ₀ Λ.S₀ z
    let ℓ := routeLab M γ.position t
    Λ.startCtx G ℓ →
    let T := Λ.Bl₀ G.1 ℓ
    let A := bitSet (T := T) G.2 (fun θ => Λ.succσ G ℓ x (Λ.view G.1 ℓ θ))
    let O := Λ.P.attach.filter (fun N' => N'.val.card = Λ.k ∧ N'.val ⊆ Λ.fam G ℓ.site)
    (Λ.ruleFirstGood M p q ρ κ hκ hs hsiteProb).toNestRule.kernel γ G t x (y,sign) z =
      stepKernel T A (fun _ => O) (localSuccessProbability p q T A) y z / 2 := by
  intro G ℓ hstart T A O
  have notStep : ∀ l : RouteLabel D, l.isStart → ¬ l.isStep := by
    intro l
    cases l <;> simp [RouteLabel.isStart, RouteLabel.isStep]
  have hstep := notStep ℓ hstart.1
  have hctx : ¬ Λ.moveCtx G ℓ x := fun hm => hstep hm.1
  let o (b : T → Bool) := Λ.offFirstGood G ℓ x (Λ.view G.1 ℓ (gluePair G.2 b))
  change stepKernel T A o (localSuccessProbability p q T A) (y,sign) z = _
  have hoff : o (T.restrict (layerVal z)) = O.product (Finset.univ : Finset Bool) := by
    dsimp only [o]
    rw [offFirstGood, if_neg (fun h => hctx h.1), offσ, if_neg (fun h => hctx h.1),
      if_pos hstart] <;> rfl
  calc
    _ = stepKernel T A (fun _ => O.product (Finset.univ : Finset Bool))
        (localSuccessProbability p q T A) (y,sign) z := by simp only [stepKernel, hoff]
    _ = _ := stepKernel_fair_nextSign T A (fun _ => O) (localSuccessProbability p q T A) y sign z

/-- Outside a start or moving context, a positive transition carries forward
the existing nest and pending sign. This includes stays and exits. -/
theorem firstGood_kernel_preserves_state
    (γ : SourceRoute D M) (z : Configuration d × Configuration d) (t : ℕ) (x y : Λ.X) :
    let G := refineReveal Λ.ρ₀ Λ.S₀ z
    let ℓ := routeLab M γ.position t
    ¬ Λ.startCtx G ℓ → ¬ Λ.moveCtx G ℓ x →
    0 < (Λ.ruleFirstGood M p q ρ κ hκ hs hsiteProb).toNestRule.kernel γ G t x y z →
    y = x := by
  intro G ℓ hstart hctx hpos
  have hoff : y ∈ Λ.offFirstGood G ℓ x (Λ.view G.1 ℓ z) :=
    ((Λ.ruleFirstGood M p q ρ κ hκ hs hsiteProb).kernel_pos γ z t x y hpos).2
  rw [offFirstGood, if_neg (fun h => hctx h.1), offσ, if_neg (fun h => hctx h.1),
    if_neg hstart, Finset.mem_singleton] at hoff
  exact hoff

/-- A stay or exit carries its nest and sign forward. The nonzero mass of
that diagonal row depends on the nest and the exit test, independently of
the pending sign. -/
theorem firstGood_kernel_inactive_row
    (γ : SourceRoute D M) (z : Configuration d × Configuration d) (t : ℕ)
    (N N' : ↥Λ.P) (a b : Bool) :
    let G := refineReveal Λ.ρ₀ Λ.S₀ z
    let ℓ := routeLab M γ.position t
    ¬ Λ.startCtx G ℓ →
    ¬ Λ.moveCtx G ℓ (N,a) →
    let T := Λ.Bl₀ G.1 ℓ
    let A := bitSet (T := T) G.2 (fun θ =>
      Λ.exitCtx G ℓ (N,false) → ∃ rep ∈ N.val, ∃ y ∈ Λ.exitPatch G ℓ rep,
        y ∈ (Λ.view G.1 ℓ θ).2)
    (Λ.ruleFirstGood M p q ρ κ hκ hs hsiteProb).toNestRule.kernel γ G t (N,a) (N',b) z =
      if b = a then stepKernel T A (fun _ => {N}) (localSuccessProbability p q T A) N' z
      else 0 := by
  intro G ℓ hstart hctx T A
  let A' := bitSet (T := T) G.2 (fun θ => Λ.succσ G ℓ (N,a) (Λ.view G.1 ℓ θ))
  let O := fun ξ : T → Bool =>
    Λ.offFirstGood G ℓ (N,a) (Λ.view G.1 ℓ (gluePair G.2 ξ))
  change stepKernel T A' O (localSuccessProbability p q T A') (N',b) z = _
  have hA : A' = A := by
    ext ξ
    change (Λ.succσ G ℓ (N,a) (Λ.view G.1 ℓ (gluePair G.2 ξ))) ↔ _
    simp only [succσ, hctx, false_implies, true_and, exitCtx] <;> rfl
  have hO : O = fun _ => {(N,a)} := by
    funext ξ
    dsimp only [O]
    rw [offFirstGood, if_neg (fun h => hctx h.1), offσ, if_neg (fun h => hctx h.1),
      if_neg hstart]
  rw [hA, hO]
  by_cases hb : b = a
  · simp [stepKernel, hb]
  · simp [stepKernel, hb]

end NearCritical.Section10.NestLayout
