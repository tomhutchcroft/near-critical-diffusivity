module

public import NearCritical.Section10FirstGoodMaskedKernel
public import NearCritical.Section10FirstGoodRouteInvariant

/-! Reindex the signs in the actual chronological first-good histories on
pre-good routes. -/

@[expose] public section
noncomputable section

namespace NearCritical.Section10.NestLayout

open MeasureTheory
open scoped Classical

variable {D d M : ℕ} (Λ : NestLayout D d) [LinearOrder (Finset (Vertex d))]
  (p q : unitInterval) (ρ κ : ℝ) (hκ : 0 < κ)
  (hs : ∀ (γ : SourceRoute D M) (G : Λ.Φ) (t : ℕ) (x : Λ.X), ρ⁻¹ ≤
    localSuccessProbability p q (Λ.Bl₀ G.1 (routeLab M γ.position t))
      (bitSet G.2 (fun z => Λ.succσ G (routeLab M γ.position t) x
        (Λ.view G.1 (routeLab M γ.position t) z))))
  (hsiteProb : ∀ s, κ⁻¹ ≤ coupledProb p q (Λ.siteEvent s))

/-- The start draws the first pending sign. Later draws occur precisely at
physical moves between different coarse sites. -/
def routeSignDraw {D M : ℕ} (γ : SourceRoute D M) (t : ℕ) : Bool :=
  decide (t = 0 ∨
    (1 ≤ t ∧ t + 1 < 2 * M ∧ (routeLab M γ.position t).target ≠ (routeLab M γ.position t).site))

theorem firstGood_routeTraceMass_pendingMasked
    (γ : SourceRoute D M) (z : Configuration d × Configuration d) (hM : 1 ≤ M)
    (hbox : ∀ t, t < 2 * M → (routeLab M γ.position t).site ∈ Λ.siteBox)
    (hpre : ∀ t, t < 2 * M →
      IsPreGoodCube Λ.typ Λ.t (Λ.center (routeLab M γ.position t).site) z.1)
    (hcount : (Λ.k : ℝ) ≤ Λ.typ.countLower * (2 * (Λ.t : ℝ)) ^ (d - 6))
    (n : ℕ) (x : Λ.X) (h : NestTrace Λ.X n) :
    let G := refineReveal Λ.ρ₀ Λ.S₀ z
    let K := (Λ.ruleFirstGood M p q ρ κ hκ hs hsiteProb).toNestRule.kernel γ G
    let B := Λ.firstGoodMaskBase p q ρ κ hκ hs hsiteProb γ G (routeSignDraw γ)
    routeTraceMass K z n 0 x h = routeTraceMass (pendingMaskedKernel (routeSignDraw γ) B) z n 0 x h := by
  intro G K B
  let good := fun t (x : Λ.X) => 1 ≤ t → t < 2 * M →
    x.1.val.card = Λ.k ∧ x.1.val ⊆ Λ.fam G (routeLab M γ.position t).site
  refine routeTraceMass_congr_of_valid K _ z good ?_ ?_ n 0 x h ?_
  · rintro t ⟨N,a⟩ ⟨N',b⟩ hg
    let ℓ := routeLab M γ.position t
    refine Λ.firstGood_kernel_eq_pendingMasked p q ρ κ hκ hs hsiteProb γ z
      (routeSignDraw γ) t N N' a b ?_ ?_
    · intro ht
      have ht' : t = 0 ∨ (1 ≤ t ∧ t + 1 < 2 * M ∧ ℓ.target ≠ ℓ.site) := by
        simpa only [routeSignDraw, decide_eq_true_eq] using ht
      rcases ht' with hz | ⟨ht₁, ht₂, hmove⟩
      · subst t
        exact Or.inl (Λ.firstGood_route_start_context γ z (hbox 0 (by omega))
          (hpre 0 (by omega)) hcount)
      · obtain ⟨hc,hf⟩ := hg ht₁ (by omega)
        exact Or.inr (Λ.firstGood_route_move_context γ z ht₁ ht₂ hbox hpre (N,a) hc hf hmove)
    · intro ht
      have ht' : ¬ (t = 0 ∨ (1 ≤ t ∧ t + 1 < 2 * M ∧ ℓ.target ≠ ℓ.site)) := by
        intro hp
        exact ht (by simpa only [routeSignDraw, decide_eq_true_eq] using hp)
      have hnz : t ≠ 0 := fun hz => ht' (Or.inl hz)
      have hns : ¬ ℓ.isStart := by
        dsimp only [ℓ]
        unfold routeLab
        rw [if_neg hnz]
        split_ifs <;> simp [RouteLabel.isStart]
      refine ⟨fun h => hns h.1, ?_⟩
      intro hm
      apply ht'
      refine Or.inr ⟨by omega, ?_, hm.2.1⟩
      have hn : t < 2 * M := by
        by_contra hh
        have hstep := hm.1
        change (routeLab M γ.position t).isStep at hstep
        unfold routeLab at hstep
        rw [if_neg hnz, if_pos (by omega)] at hstep
        exact hstep
      by_contra hh
      have he : t = 2 * M - 1 := by omega
      have hstep := hm.1
      change (routeLab M γ.position t).isStep at hstep
      rw [he, routeLab_last hM] at hstep
      exact hstep
  · intro t x y hg hn _ hlt
    have hk0 : 0 ≤ K t x y z := by
      apply stepKernel_nonneg
      unfold localSuccessProbability
      refine integral_nonneg fun θ => ?_
      change (0:ℝ) ≤ if _ then 1 else 0
      split_ifs <;> norm_num
    exact Λ.firstGood_route_next_valid γ z p q ρ κ hκ hs hsiteProb hbox hpre hcount
      t hlt x y (fun ht => hg ht (by omega)) (lt_of_le_of_ne hk0 (Ne.symm hn))
  · intro ht
    omega

/-- The weighted sum of actual first-good histories on a pre-good route
can use the current-move signs. The initial dummy sign is averaged out. -/
theorem firstGood_route_marked_sum_usedMasked
    (γ : SourceRoute D M) (z : Configuration d × Configuration d) (hM : 1 ≤ M)
    (hbox : ∀ t, t < 2 * M → (routeLab M γ.position t).site ∈ Λ.siteBox)
    (hpre : ∀ t, t < 2 * M →
      IsPreGoodCube Λ.typ Λ.t (Λ.center (routeLab M γ.position t).site) z.1)
    (hcount : (Λ.k : ℝ) ≤ Λ.typ.countLower * (2 * (Λ.t : ℝ)) ^ (d - 6))
    (n : ℕ) (N : ↥Λ.P) (b : Bool) (F : NestTrace Λ.X n → ℝ) :
    let G := refineReveal Λ.ρ₀ Λ.S₀ z
    let K := (Λ.ruleFirstGood M p q ρ κ hκ hs hsiteProb).toNestRule.kernel γ G
    let B := Λ.firstGoodMaskBase p q ρ κ hκ hs hsiteProb γ G (routeSignDraw γ)
    (∑ h : Bool × NestTrace Λ.X n,
      F (usedMaskedTrace (routeSignDraw γ) n 0 h.1 h.2) *
        routeTraceMass K z n 0 (N,h.1) h.2 / 2) =
    ∑ h : NestTrace Λ.X n, F h *
      routeTraceMass (usedMaskedKernel (routeSignDraw γ) B) z n 0 (N,b) h := by
  intro G K B
  calc
    _ = ∑ h : Bool × NestTrace Λ.X n,
      F (usedMaskedTrace (routeSignDraw γ) n 0 h.1 h.2) *
        routeTraceMass (pendingMaskedKernel (routeSignDraw γ) B) z n 0 (N,h.1) h.2 / 2 := by
      apply Finset.sum_congr rfl
      intro h _
      have he := Λ.firstGood_routeTraceMass_pendingMasked p q ρ κ hκ hs hsiteProb γ z hM
        hbox hpre hcount n (N,h.1) h.2
      change routeTraceMass K z n 0 (N,h.1) h.2 =
        routeTraceMass (pendingMaskedKernel (routeSignDraw γ) B) z n 0 (N,h.1) h.2 at he
      rw [he]
    _ = _ := routeTraceMass_marked_sum_usedMasked (routeSignDraw γ) B z n 0 N b F

/-- Remove the placeholder at the start before evaluating a path mark. -/
def eraseInitialUsedSign {X : Type*} : (n : ℕ) → NestTrace (X × Bool) n → NestTrace (X × Bool) n
  | 0, h => h
  | _+1, h => ((h.1.1,false),h.2)

/-- Fixing the incoming dummy sign of the source does not change any
weighted mark of its chronological nests and physical move signs. -/
theorem firstGood_route_marked_sum_fixedStart
    (γ : SourceRoute D M) (z : Configuration d × Configuration d) (hM : 1 ≤ M)
    (hbox : ∀ t, t < 2 * M → (routeLab M γ.position t).site ∈ Λ.siteBox)
    (hpre : ∀ t, t < 2 * M →
      IsPreGoodCube Λ.typ Λ.t (Λ.center (routeLab M γ.position t).site) z.1)
    (hcount : (Λ.k : ℝ) ≤ Λ.typ.countLower * (2 * (Λ.t : ℝ)) ^ (d - 6))
    (n : ℕ) (N : ↥Λ.P) (a b : Bool) (F : NestTrace Λ.X n → ℝ) :
    let G := refineReveal Λ.ρ₀ Λ.S₀ z
    let K := (Λ.ruleFirstGood M p q ρ κ hκ hs hsiteProb).toNestRule.kernel γ G
    let B := Λ.firstGoodMaskBase p q ρ κ hκ hs hsiteProb γ G (routeSignDraw γ)
    (∑ h : NestTrace Λ.X n,
      F (eraseInitialUsedSign n (usedMaskedTrace (routeSignDraw γ) n 0 a h)) *
        routeTraceMass K z n 0 (N,a) h) =
    ∑ h : NestTrace Λ.X n, F (eraseInitialUsedSign n h) *
      routeTraceMass (usedMaskedKernel (routeSignDraw γ) B) z n 0 (N,b) h := by
  intro G K B
  let f := fun (c : Bool) (h : NestTrace Λ.X n) =>
    F (eraseInitialUsedSign n (usedMaskedTrace (routeSignDraw γ) n 0 c h)) *
      routeTraceMass K z n 0 (N,c) h
  have he (c : Bool) (h : NestTrace Λ.X n) : f c h = f a h := by
    have hmark : eraseInitialUsedSign n (usedMaskedTrace (routeSignDraw γ) n 0 c h) =
        eraseInitialUsedSign n (usedMaskedTrace (routeSignDraw γ) n 0 a h) := by
      cases n <;> rfl
    have hmass : routeTraceMass K z n 0 (N,c) h = routeTraceMass K z n 0 (N,a) h := by
      cases n with
      | zero => rfl
      | succ n =>
        change K 0 (N,c) h.1 z * routeTraceMass K z n 1 h.1 h.2 =
          K 0 (N,a) h.1 z * routeTraceMass K z n 1 h.1 h.2
        have hstart := Λ.firstGood_route_start_context γ z (hbox 0 (by omega))
          (hpre 0 (by omega)) hcount
        have hrow : K 0 (N,c) h.1 z = K 0 (N,a) h.1 z :=
          Λ.firstGood_kernel_start_incoming_sign p q ρ κ hκ hs hsiteProb γ z
            0 N h.1.1 c a h.1.2 hstart
        rw [hrow]
    dsimp only [f]
    rw [hmark, hmass]
  calc
    _ = ∑ h : Bool × NestTrace Λ.X n, f h.1 h.2 / 2 := by
      rw [Fintype.sum_prod_type, Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro h _
      simp only [he, Finset.sum_const, Finset.card_univ, Fintype.card_bool, nsmul_eq_mul,
        Nat.cast_ofNat]
      ring
    _ = _ := Λ.firstGood_route_marked_sum_usedMasked p q ρ κ hκ hs hsiteProb γ z hM
      hbox hpre hcount n N b (fun h => F (eraseInitialUsedSign n h))

end NearCritical.Section10.NestLayout
