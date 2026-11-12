module

public import NearCritical.Section10ActualOffspring
public import NearCritical.Section10MoveAssembly

/-! `prop.proba.k-nest` for a moving step of the actual layout.

`actualLayout_hmove_step` combines the offspring half
(`actualLayout_offspring_failure`) and the diameter half
(`actualLayout_move_success`): in dimension `m + 6 >= 9`, with the Section 9
constants in their order, for every moving step (`moveCtx`, label with a tube)

  `1 - eps - (1 + C t^2)/(K_diam + 1) <= (conditional success probability)`.

Parameter order made explicit by the quantifiers: `r, eps` -> `cSize` ->
`mo` (number of offspring demanded, `2 k^4 <= mo + 1`) -> `Lambda` -> `CB, KA`
-> `N₀` -> `t >= N₀`, and `q` in the two-sided window
`Lambda / t^2 <= q <= q0 / t^2`; `K_diam` is free and chosen last.

Remaining hypotheses: numeric size conditions on the source and target
boundaries, `M_off, M_coal >=` cube volume, `10 <= 2 k^4`, the Green bound,
`0 < p_c < 1`, and the three cited Section 9 inputs.
-/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open MeasureTheory
open scoped Classical

theorem actualLayout_hmove_step (m : ℕ) (hd : 9 ≤ m + 5 + 1)
    (asymptotics : TwoPointAsymptotics (m + 5 + 1))
    (rectangle : RestrictedRectangleLowerInput (m + 5 + 1)) (reimer : FiniteBernoulliBKRInput)
    (hp0 : 0 < (criticalPoint (m + 5 + 1) : ℝ)) (hp1 : (criticalPoint (m + 5 + 1) : ℝ) < 1)
    {G₀ : ℝ} (hG0 : 0 ≤ G₀) (hG : CriticalSupGreenUpper (m + 5 + 1) G₀) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ r : ℕ, 1 ≤ r → ∀ ε : ℝ, 0 < ε →
      ∃ cSize : ℝ, 0 < cSize ∧ ∀ mo : ℕ, ∃ Lambda : ℝ, 0 < Lambda ∧
      ∀ CB KA : ℝ, 0 < CB → 0 < KA →
      ∃ N₀ : ℕ, 16*(r+1) ≤ N₀ ∧
      ∀ (typ : TypicalParameters) (t : ℕ) (ht : 9 ≤ t), N₀ ≤ t →
      typ.regularRadius = r → typ.regularTolerance ≤ δ →
      0 ≤ typ.boundaryUpper → 0 ≤ typ.countUpper →
      ∀ (q : unitInterval) (q0 : ℝ), 0 ≤ q0 → Lambda ≤ (q : ℝ)*(t : ℝ)^2 →
      (q : ℝ) ≤ q0 / (t : ℝ)^2 →
      ∀ (k : ℕ) (hk : 0 < k), 10 ≤ 2 * k ^ 4 → 2 * k ^ 4 ≤ mo + 1 →
      ∀ (MOff Mcoal Kdiam M : ℕ),
      (∀ c : Vertex (m + 5 + 1), (typicalCube t c).card ≤ MOff) →
      (∀ c : Vertex (m + 5 + 1), (typicalCube t c).card ≤ Mcoal) →
      ∀ (Λ : NestLayout (m + 5) (m + 5 + 1))
        (hΛ : Λ = actualLayout (m + 5) typ t ht k hk MOff Mcoal Kdiam M)
        (G : Λ.Φ) (ℓ : RouteLabel (m + 5)) (hℓ : HasTube M ℓ) (x : Λ.X)
        (hctx : Λ.moveCtx G ℓ x),
      ((sprinklingTargetBoundary x.1.val (Λ.src G ℓ x.2)).card : ℝ) ≤ KA*(t : ℝ)^2 →
      (∀ c ∈ Λ.fam G ℓ.target, ((Λ.tgt G ℓ c).card : ℝ) ≤ CB*(t : ℝ)^2) →
      cSize*(t : ℝ)^2 ≤ ((sprinklingTargetBoundary x.1.val (Λ.src G ℓ x.2)).card : ℝ) →
      cSize*(t : ℝ)^2 ≤
        ((sprinklingTargetBoundary (Λ.fam G ℓ.target) (Λ.tgt G ℓ)).card : ℝ) →
      cSize*(t : ℝ)^((((m + 5 + 1 : ℕ) : ℝ))-2) ≤
        ((sprinklingTargetBoundary x.1.val (Λ.src G ℓ x.2)).card : ℝ) *
        ((sprinklingTargetBoundary (Λ.fam G ℓ.target) (Λ.tgt G ℓ)).card : ℝ) →
      1 - ε - (1 + diamConst m k typ G₀ q0 * (t : ℝ) ^ 2) / ((Kdiam : ℝ) + 1) ≤
        localSuccessProbability (criticalPoint (m + 5 + 1)) q (Λ.Bl₀ G.1 ℓ)
          (bitSet G.2 (fun z => Λ.moveTypical G ℓ x (Λ.view G.1 ℓ z))) := by
  obtain ⟨δ, hδ, hmain⟩ := actualLayout_offspring_failure (D := m + 5) hd asymptotics rectangle
    reimer hp0 hp1
  refine ⟨δ, hδ, ?_⟩
  intro r hr ε hε
  obtain ⟨cSize, hSize, hm⟩ := hmain r hr ε hε
  refine ⟨cSize, hSize, ?_⟩
  intro mo
  obtain ⟨Lambda, hLambda, hCB⟩ := hm mo
  refine ⟨Lambda, hLambda, ?_⟩
  intro CB KA hCBpos hKApos
  obtain ⟨N₀, hN₀, hrest⟩ := hCB CB KA hCBpos hKApos
  refine ⟨N₀, hN₀, ?_⟩
  intro typ t ht hNt hrad htol hbU hcU q q0 hq0 hqlo hqhi k hk hk10 hkmo MOff Mcoal Kdiam M
    hMOff hMcoal Λ hΛ G ℓ hℓ x hctx hAup hTup hAlo hBlo hAB
  have hctx' := hctx
  obtain ⟨_, _, hsite, htarget, _, _, _, _, ⟨z, hz⟩⟩ := hctx'
  subst hz
  have hN : 2 * Λ.k ^ 4 ≤ mo + 1 := by
    subst hΛ
    exact hkmo
  have hoff := hrest typ t ht hNt hrad htol q hqlo k hk MOff Mcoal Kdiam M Λ hΛ z ℓ hℓ
    hsite htarget x hAup hTup hAlo hBlo hAB (2 * Λ.k ^ 4) hN
  exact actualLayout_move_success m hG0 hG q hq0 typ t ht hqhi hbU hcU k hk hk10 MOff Mcoal
    Kdiam M hMOff hMcoal Λ hΛ _ ℓ hℓ x hctx hoff

end NearCritical.Section10
