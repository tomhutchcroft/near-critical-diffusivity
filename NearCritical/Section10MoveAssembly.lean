module

public import NearCritical.Section10StepDiameterSmall

/-! `prop.proba.k-nest` for the actual layout, modulo the offspring bound.

`actualLayout_move_success`: for a moving step of the actual layout (label with
a tube, `moveCtx`), in dimension `m + 6`, with `q <= q0 / t^2`, `M_off` and
`M_coal` at least the cube volume and `10 <= 2 k^4`,

  `1 - eps1 - (1 + C t^2)/(K_diam + 1) <= (conditional success probability)`,

where `eps1` bounds the probability of fewer than `2 k^4` offspring. All other
ingredients are proved: the step reads no revealed bond
(`actualLayout_readSet_disjoint`), the offspring upper bound and coalescence
bound are deterministic (`moveTypical_view_iff`), and the diameter bound is
`actualLayout_diamFailure_small`.
-/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open MeasureTheory
open scoped Classical

lemma RouteLabel.not_isExit_of_isStep {D : ℕ} {ℓ : RouteLabel D} (h : ℓ.isStep) : ¬ ℓ.isExit := by
  cases ℓ <;> simp_all [RouteLabel.isStep, RouteLabel.isExit]

theorem NestLayout.faceAll_card_le_cube {D d : ℕ} (Λ : NestLayout D d) (G : Λ.Φ)
    (ℓ : RouteLabel D) (pl : Bool) :
    (Λ.faceAll G ℓ pl).card ≤ (typicalCube Λ.t (Λ.center ℓ.site)).card := by
  refine Finset.card_le_card ?_
  unfold NestLayout.faceAll sprinklingTargetBoundary
  refine Finset.biUnion_subset.mpr (fun C _ => ?_)
  exact typicalRegularPatch_subset_cube _ _ _ _ _ _ _

/-- **Success probability of a moving step of the actual layout.** -/
theorem actualLayout_move_success (m : ℕ) {G₀ : ℝ} (hG0 : 0 ≤ G₀)
    (hG : CriticalSupGreenUpper (m + 5 + 1) G₀) (q : unitInterval) {q0 : ℝ} (hq0 : 0 ≤ q0)
    (typ : TypicalParameters) (t : ℕ) (ht : 9 ≤ t) (hq : (q : ℝ) ≤ q0 / (t : ℝ) ^ 2)
    (hbU : 0 ≤ typ.boundaryUpper) (hcU : 0 ≤ typ.countUpper)
    (k : ℕ) (hk : 0 < k) (hk10 : 10 ≤ 2 * k ^ 4) (MOff Mcoal Kdiam M : ℕ)
    (hMOff : ∀ c : Vertex (m + 5 + 1), (typicalCube t c).card ≤ MOff)
    (hMcoal : ∀ c : Vertex (m + 5 + 1), (typicalCube t c).card ≤ Mcoal)
    (Λ : NestLayout (m + 5) (m + 5 + 1))
    (hΛ : Λ = actualLayout (m + 5) typ t ht k hk MOff Mcoal Kdiam M)
    (G : Λ.Φ) (ℓ : RouteLabel (m + 5)) (hℓ : HasTube M ℓ) (x : Λ.X)
    (hctx : Λ.moveCtx G ℓ x) {ε₁ : ℝ}
    (hoff : ((percolation (m + 5 + 1) (criticalPoint (m + 5 + 1))).prod
        (percolation (m + 5 + 1) q)).real
      {z | ¬ 2 * Λ.k ^ 4 ≤ (sprinklingOffspring (Λ.view G.1 ℓ z).1.1 (Λ.view G.1 ℓ z).1.2.1
        (sprinklingTargetBoundary x.1.val (Λ.src G ℓ x.2)) (Λ.fam G ℓ.target) (Λ.tgt G ℓ)
        (svPivots (Λ.view G.1 ℓ z).1 x.1.val (Λ.fam G ℓ.target) (Λ.src G ℓ x.2)
          (Λ.tgt G ℓ))).card} ≤ ε₁) :
    1 - ε₁ - (1 + diamConst m k typ G₀ q0 * (t : ℝ) ^ 2) / ((Kdiam : ℝ) + 1) ≤
      localSuccessProbability (criticalPoint (m + 5 + 1)) q (Λ.Bl₀ G.1 ℓ)
        (bitSet G.2 (fun z => Λ.moveTypical G ℓ x (Λ.view G.1 ℓ z))) := by
  obtain ⟨hstep, _, _, _, hcard, hnest, _, hgoodT, _⟩ := hctx
  have hdiam := actualLayout_diamFailure_small m hG0 hG q hq0 typ t ht hq hbU hcU k hk
    MOff Mcoal Kdiam M Λ hΛ G ℓ hℓ x hnest (by rw [hcard, hΛ]; rfl) hgoodT
  subst hΛ
  exact NestLayout.moveSuccess_ge _ (criticalPoint (m + 5 + 1)) q G ℓ x
    (actualLayout_readSet_disjoint (m + 5) typ t ht k hk MOff Mcoal Kdiam M G.1 ℓ
      (RouteLabel.not_isExit_of_isStep hstep))
    ((typicalClusterFamily_card_le_cube _ _ _ _).trans (hMOff _))
    ((NestLayout.faceAll_card_le_cube _ G ℓ x.2).trans (hMcoal _)) hk10 hoff hdiam

end NearCritical.Section10
