module

public import NearCritical.Section10MoveStep
public import NearCritical.Section10StepSizes

/-! `prop.proba.k-nest` in the shape of the hypothesis `hmove` of the
time-constant capstones.

`actualLayout_hmove`: with the Section 9 constants in their order and explicit
relations between `k`, the typicality constants and those constants, for every
box size `M`, every route `gamma`, reveal `G`, time `t'` and state `x`:

  `moveCtx G (routeLab M gamma.position t') x ->
     rho^{-1} <= localSuccessProbability p_c q (Bl₀ ..) (bitSet G.2 (moveTypical ..))`.

The size conditions come from `NestLayout.step_sizes`, the tube from
`routeLab_hasTube`, and the probability bound from `actualLayout_hmove_step`.
Remaining hypotheses: the parameter relations (stated), the Green bound,
`0 < p_c < 1`, and the three cited Section 9 inputs.
-/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open MeasureTheory
open scoped Classical

theorem actualLayout_hmove (m : ℕ) (hd : 9 ≤ m + 5 + 1)
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
      0 ≤ typ.boundaryLower → 0 ≤ typ.countLower →
      ∀ (q : unitInterval) (q0 : ℝ), 0 ≤ q0 → Lambda ≤ (q : ℝ)*(t : ℝ)^2 →
      (q : ℝ) ≤ q0 / (t : ℝ)^2 →
      ∀ (k : ℕ) (hk : 0 < k), 10 ≤ 2 * k ^ 4 → 2 * k ^ 4 ≤ mo + 1 →
      4 * (k : ℝ) * typ.boundaryUpper ≤ KA → 8 * typ.boundaryUpper ≤ CB →
      cSize ≤ 4 * (k : ℝ) * typ.boundaryLower →
      cSize ≤ 4 * typ.countLower * typ.boundaryLower * (2 * (t : ℝ)) ^ (m + 5 + 1 - 6) →
      cSize ≤ 16 * (k : ℝ) * typ.countLower * typ.boundaryLower ^ 2 →
      ∀ (MOff Mcoal Kdiam : ℕ),
      (∀ c : Vertex (m + 5 + 1), (typicalCube t c).card ≤ MOff) →
      (∀ c : Vertex (m + 5 + 1), (typicalCube t c).card ≤ Mcoal) →
      ∀ {ϱ : ℝ},
      ϱ⁻¹ ≤ 1 - ε - (1 + diamConst m k typ G₀ q0 * (t : ℝ) ^ 2) / ((Kdiam : ℝ) + 1) →
      ∀ (M : ℕ) (γ : SourceRoute (m + 5) M)
        (G : (actualLayout (m + 5) typ t ht k hk MOff Mcoal Kdiam M).Φ) (t' : ℕ)
        (x : (actualLayout (m + 5) typ t ht k hk MOff Mcoal Kdiam M).X),
        (actualLayout (m + 5) typ t ht k hk MOff Mcoal Kdiam M).moveCtx G
          (routeLab M γ.position t') x → ϱ⁻¹ ≤
        localSuccessProbability (criticalPoint (m + 5 + 1)) q
          ((actualLayout (m + 5) typ t ht k hk MOff Mcoal Kdiam M).Bl₀ G.1
            (routeLab M γ.position t'))
          (bitSet G.2 (fun z =>
            (actualLayout (m + 5) typ t ht k hk MOff Mcoal Kdiam M).moveTypical G
              (routeLab M γ.position t') x
              ((actualLayout (m + 5) typ t ht k hk MOff Mcoal Kdiam M).view G.1
                (routeLab M γ.position t') z))) := by
  obtain ⟨δ, hδ, hmain⟩ := actualLayout_hmove_step m hd asymptotics rectangle reimer hp0 hp1
    hG0 hG
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
  intro typ t ht hNt hrad htol hbU hcU hbL hcL q q0 hq0 hqlo hqhi k hk hk10 hkmo hKA hCBr
    hc1 hc2 hc3 MOff Mcoal Kdiam hMOff hMcoal ϱ hϱ M γ G t' x hctx
  have hℓ : HasTube M (routeLab M γ.position t') :=
    routeLab_hasTube γ.1.1 γ.2 hctx.1 hctx.2.1
  have hcard : x.1.val.card = k := hctx.2.2.2.2.1
  have hnest := hctx.2.2.2.2.2.1
  have hgoodT := hctx.2.2.2.2.2.2.2.1
  have hsz := (actualLayout (m + 5) typ t ht k hk MOff Mcoal Kdiam M).step_sizes
    (by omega) (by show 1 ≤ t; omega) G (routeLab M γ.position t') x.2 x.1.val hnest hgoodT
    hbL hcL (KA := KA) (CB := CB) (cSize := cSize)
    (by rw [hcard]; exact hKA) hCBr (by rw [hcard]; exact hc1) hc2 (by rw [hcard]; exact hc3)
  obtain ⟨hs1, hs2, hs3, hs4, hs5⟩ := hsz
  have hstep := hrest typ t ht hNt hrad htol hbU hcU q q0 hq0 hqlo hqhi k hk hk10 hkmo
    MOff Mcoal Kdiam M hMOff hMcoal _ rfl G (routeLab M γ.position t') hℓ x hctx
    hs1 hs2 hs3 hs4 hs5
  exact hϱ.trans hstep

end NearCritical.Section10
