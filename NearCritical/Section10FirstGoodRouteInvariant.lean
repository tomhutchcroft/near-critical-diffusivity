module

public import NearCritical.Section10FirstGoodSurvival
public import NearCritical.Section10LatticeHelpers
public import NearCritical.Section10MergedRouteTraces

/-! Admissible nests along positive first-good transitions on a pre-good route. -/

@[expose] public section
noncomputable section

namespace NearCritical.Section10

/-- Kernels that agree on valid states have the same mass along every
history starting from a valid state, provided every nonzero row preserves
validity. -/
theorem routeTraceMass_congr_of_valid {Ω X : Type*}
    (K L : ℕ → X → X → Ω → ℝ) (z : Ω) (valid : ℕ → X → Prop)
    (hK : ∀ t x y, valid t x → K t x y z = L t x y z)
    (hnext : ∀ t x y, valid t x → K t x y z ≠ 0 → valid (t+1) y)
    (n t : ℕ) (x : X) (h : NestTrace X n) (hx : valid t x) :
    routeTraceMass K z n t x h = routeTraceMass L z n t x h := by
  induction n generalizing t x with
  | zero => rfl
  | succ n ih =>
    change K t x h.1 z * routeTraceMass K z n (t+1) h.1 h.2 =
      L t x h.1 z * routeTraceMass L z n (t+1) h.1 h.2
    rw [← hK t x h.1 hx]
    by_cases hz : K t x h.1 z = 0
    · simp only [hz, zero_mul]
    · rw [ih (t+1) h.1 h.2 (hnext t x h.1 hx hz)]

namespace NestLayout

open scoped Classical

variable {D d M : ℕ} (Λ : NestLayout D d)
  (γ : SourceRoute D M) (z : Configuration d × Configuration d)

theorem firstGood_route_start_context
    (hbox : (routeLab M γ.position 0).site ∈ Λ.siteBox)
    (hpre : IsPreGoodCube Λ.typ Λ.t (Λ.center (routeLab M γ.position 0).site) z.1)
    (hcount : (Λ.k : ℝ) ≤ Λ.typ.countLower * (2 * (Λ.t : ℝ)) ^ (d - 6)) :
    Λ.startCtx (refineReveal Λ.ρ₀ Λ.S₀ z) (routeLab M γ.position 0) := by
  refine ⟨by rw [routeLab_zero]; trivial, hbox, ?_⟩
  rw [Λ.fam_eq z hbox]
  exact_mod_cast hcount.trans hpre.1

theorem firstGood_route_move_context {t : ℕ} (ht : 1 ≤ t) (ht' : t + 1 < 2 * M)
    (hbox : ∀ i, i < 2 * M → (routeLab M γ.position i).site ∈ Λ.siteBox)
    (hpre : ∀ i, i < 2 * M →
      IsPreGoodCube Λ.typ Λ.t (Λ.center (routeLab M γ.position i).site) z.1)
    (x : Λ.X) (hcard : x.1.val.card = Λ.k)
    (hfamily : x.1.val ⊆ Λ.fam (refineReveal Λ.ρ₀ Λ.S₀ z) (routeLab M γ.position t).site)
    (hmove : (routeLab M γ.position t).target ≠ (routeLab M γ.position t).site) :
    Λ.moveCtx (refineReveal Λ.ρ₀ Λ.S₀ z) (routeLab M γ.position t) x := by
  have hnext := routeLab_next_site γ.position ht'
  have hsrc := hbox t (by omega)
  have htgt : (routeLab M γ.position t).target ∈ Λ.siteBox := by
    rw [← hnext]
    exact hbox _ ht'
  refine ⟨routeLab_isStep γ.position ht (by omega), hmove, hsrc, htgt, hcard, hfamily,
    (Λ.goodCube_iff z hsrc).mpr (hpre t (by omega)), (Λ.goodCube_iff z htgt).mpr ?_, ⟨z,rfl⟩⟩
  rw [← hnext]
  exact hpre _ ht'

variable [LinearOrder (Finset (Vertex d))]
  (p q : unitInterval) (ρ κ : ℝ) (hκ : 0 < κ)
  (hs : ∀ (γ : SourceRoute D M) (G : Λ.Φ) (t : ℕ) (x : Λ.X), ρ⁻¹ ≤
    localSuccessProbability p q (Λ.Bl₀ G.1 (routeLab M γ.position t))
      (bitSet G.2 (fun z => Λ.succσ G (routeLab M γ.position t) x
        (Λ.view G.1 (routeLab M γ.position t) z))))
  (hsiteProb : ∀ s, κ⁻¹ ≤ coupledProb p q (Λ.siteEvent s))

/-- A positive transition into an interior route position produces a valid
nest there. At the first step this follows from the initial uniform choice.
For later steps it follows from the actual first good representative or from
carrying the nest through a stay. -/
theorem firstGood_route_next_valid
    (hbox : ∀ i, i < 2 * M → (routeLab M γ.position i).site ∈ Λ.siteBox)
    (hpre : ∀ i, i < 2 * M →
      IsPreGoodCube Λ.typ Λ.t (Λ.center (routeLab M γ.position i).site) z.1)
    (hcount : (Λ.k : ℝ) ≤ Λ.typ.countLower * (2 * (Λ.t : ℝ)) ^ (d - 6))
    (t : ℕ) (ht : t + 1 < 2 * M) (x y : Λ.X) :
    let G := refineReveal Λ.ρ₀ Λ.S₀ z
    (1 ≤ t → x.1.val.card = Λ.k ∧ x.1.val ⊆ Λ.fam G (routeLab M γ.position t).site) →
    0 < (Λ.ruleFirstGood M p q ρ κ hκ hs hsiteProb).toNestRule.kernel γ G t x y z →
    y.1.val.card = Λ.k ∧ y.1.val ⊆ Λ.fam G (routeLab M γ.position (t+1)).site := by
  intro G hInv hpos
  let ℓ := routeLab M γ.position t
  have hnext : (routeLab M γ.position (t+1)).site = ℓ.target := routeLab_next_site γ.position ht
  have hoff : y ∈ Λ.offFirstGood G ℓ x (Λ.view G.1 ℓ z) :=
    ((Λ.ruleFirstGood M p q ρ κ hκ hs hsiteProb).kernel_pos γ z t x y hpos).2
  by_cases hz : t = 0
  · have hstart : Λ.startCtx G ℓ := by
      dsimp only [ℓ]
      rw [hz]
      exact Λ.firstGood_route_start_context γ z (hbox 0 (by omega))
        (hpre 0 (by omega)) hcount
    have hnostep : ¬ ℓ.isStep := by
      dsimp only [ℓ]
      rw [hz, routeLab_zero]
      exact fun h => h
    have hctx : ¬ Λ.moveCtx G ℓ x := fun h => hnostep h.1
    rw [offFirstGood, if_neg (fun h => hctx h.1), offσ, if_neg (fun h => hctx h.1),
      if_pos hstart] at hoff
    obtain ⟨_, hcard, hsub⟩ := Finset.mem_filter.mp (Finset.mem_product.mp hoff).1
    have hstay : ℓ.target = ℓ.site := by
      dsimp only [ℓ]
      rw [hz, routeLab_zero]
      rfl
    exact ⟨hcard, by rw [hnext, hstay]; exact hsub⟩
  · obtain ⟨hcard, hfamily⟩ := hInv (by omega)
    have hstep : ℓ.isStep := routeLab_isStep γ.position (by omega) (by omega)
    by_cases hm : ℓ.target = ℓ.site
    · have hctx : ¬ Λ.moveCtx G ℓ x := fun h => h.2.1 hm
      have notStart : ∀ l : RouteLabel D, l.isStep → ¬ l.isStart := by
        intro l
        cases l <;> simp [RouteLabel.isStart, RouteLabel.isStep]
      have hstart : ¬ Λ.startCtx G ℓ := fun h => notStart ℓ hstep h.1
      rw [offFirstGood, if_neg (fun h => hctx h.1), offσ, if_neg (fun h => hctx h.1),
        if_neg hstart, Finset.mem_singleton] at hoff
      rw [hoff, hnext, hm]
      exact ⟨hcard, hfamily⟩
    · have hctx : Λ.moveCtx G ℓ x :=
        Λ.firstGood_route_move_context γ z (by omega) ht hbox hpre x hcard hfamily hm
      obtain ⟨h, _, hycard, hysub⟩ :=
        Λ.firstGood_kernel_move_uses_representative M p q ρ κ hκ hs hsiteProb γ z t x y hctx hpos
      refine ⟨hycard, ?_⟩
      rw [hnext]
      exact hysub.trans (svOffOf_subset_cand _ _ _ _ _ _)

end NestLayout
end NearCritical.Section10
