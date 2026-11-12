module

public import NearCritical.ChemicalUpperActual
public import NearCritical.Section10StepBoundReduction

/-! Source `prop.chem.upper`, with its two probability inputs in paper form.

`chemical_timeConstant_upper_reduced`: as `chemical_timeConstant_upper_actual`,
but the hypotheses on the nest rule are reduced to

* `hmove` (`prop.proba.k-nest`): for all large `M`, for every moving step of a
  route from a `k`-nest of typical clusters between two cubes of the box, the
  sprinkling cluster of the nest is typical with conditional probability at
  least `1/rho` (as a probability of the fresh bits of the tube);
* `hpre` (`prop.proba.pregood`): every lattice cube is pre-good with
  `P_{pc}`-probability at least `1/kappa`;
* `hexitParam`: `((1 - pc)(1 - q))^m <= 1 - 1/rho` for `m >= c_b l0^2`;
* `2 <= k` and `2 k^4 <= c l0^(d-6)`: without them `hmove` cannot hold (typicality
  needs `10 <= 2 k^4` offspring, and a pre-good target cube must have at least
  `2 k^4` typical clusters). Found by an independent audit.

Trivial steps, the exit step and the passage from the coupled law to `P_{pc}`
are proved (`NestLayout.hs_of_move`, `NestLayout.hsite_of_pre`).
-/
@[expose] public section
noncomputable section
namespace NearCritical
open Set MeasureTheory Filter
open NearCritical.Section10
open scoped Classical

namespace Section10.NestLayout
variable {D d : ℕ} (Λ : NestLayout D d)

/-- The cube events have the single-layer pre-good probability. -/
theorem hsite_of_pre (p q : unitInterval) {κ : ℝ} (hκ : 1 ≤ κ)
    (hpre : ∀ s ∈ Λ.siteBox, κ⁻¹ ≤ ∫ ω, (if IsPreGoodCube Λ.typ Λ.t (Λ.center s) ω
      then (1:ℝ) else 0) ∂(percolation d p)) :
    ∀ s, κ⁻¹ ≤ coupledProb p q (Λ.siteEvent s) := by
  intro s
  have hinv1 : κ⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hκ
  unfold coupledProb
  by_cases hs : s ∈ Λ.siteBox
  · obtain ⟨g, hg⟩ : ∃ g : Configuration d → ℝ, g = fun ω =>
        if IsPreGoodCube Λ.typ Λ.t (Λ.center s) ω then (1:ℝ) else 0 := ⟨_, rfl⟩
    have hfun : (fun z : Configuration d × Configuration d =>
        if z ∈ Λ.siteEvent s then (1:ℝ) else 0) = fun z => g z.1 := by
      funext z
      have hiff : z ∈ Λ.siteEvent s ↔ IsPreGoodCube Λ.typ Λ.t (Λ.center s) z.1 := by
        unfold siteEvent
        simp only [Set.mem_setOf_eq, hs, forall_true_left]
      rw [hg]
      show (if z ∈ Λ.siteEvent s then (1:ℝ) else 0) =
        if IsPreGoodCube Λ.typ Λ.t (Λ.center s) z.1 then (1:ℝ) else 0
      by_cases hz : z ∈ Λ.siteEvent s
      · rw [if_pos hz, if_pos (hiff.mp hz)]
      · rw [if_neg hz, if_neg (fun h => hz (hiff.mpr h))]
    have hint : Integrable (fun z : Configuration d × Configuration d => g z.1)
        ((percolation d p).prod (percolation d q)) := by
      rw [← hfun]
      exact (Λ.hsite s).integrable p q
    rw [hfun, integral_fst_layer p q g hint, hg]
    exact hpre s hs
  · have hfun : (fun z : Configuration d × Configuration d =>
        if z ∈ Λ.siteEvent s then (1:ℝ) else 0) = fun _ => 1 := by
      funext z
      have hz : z ∈ Λ.siteEvent s := fun h => absurd h hs
      rw [if_pos hz]
    rw [hfun]
    simp only [integral_const, probReal_univ, one_smul]
    exact hinv1

end Section10.NestLayout

theorem chemical_timeConstant_upper_reduced {D : ℕ} (hD : 3 ≤ D) :
    ∃ q0 : ℝ, 0 < q0 ∧ q0 < 1 ∧
    ∀ (pc q : unitInterval) (N : Seminorm ℝ (Fin (D + 1) → ℝ))
      (_hunit : ∀ j, N (Pi.single j 1) = 1)
      (_hreflect : ∀ j x, N (coordinateReflection j x) = N x)
      {μ Asp Ask : ℝ} (_hμ : 0 ≤ μ) (_hAsp : 0 ≤ Asp) (_hAsk : 0 ≤ Ask)
      {ϱ κ : ℝ} (_hϱ : 1 ≤ ϱ) (_hκ : 1 ≤ κ) (_hΛq : (ϱ * κ) ^ 2 * q0 < 1)
      (typ : TypicalParameters) (t : ℕ) (ht : 9 ≤ t) (k : ℕ) (hk : 0 < k)
      (MOff Mcoal Kdiam : ℕ) {n0 ellStar : ℕ} (_hscale : 2 * t = n0 * ellStar)
      (_hstar : 1 ≤ ellStar)
      (_hA : 2 * (typ.diameterUpper * (2 * (t : ℝ)) ^ 2) = Asp * ((2 * t : ℕ) : ℝ) ^ 2)
      (_hB : (Kdiam : ℝ) = Ask * ((2 * t : ℕ) : ℝ) ^ 2)
      (_hk2 : 2 ≤ k)
      (_hcount : 2 * (k : ℝ) ^ 4 ≤ typ.countLower * (2 * (t : ℝ)) ^ (D + 1 - 6))
      (_hexitParam : ∀ m : ℕ, typ.boundaryLower * (2 * (t : ℝ)) ^ 2 ≤ (m : ℝ) →
        ((1 - (pc:ℝ)) * (1 - (q:ℝ))) ^ m ≤ 1 - ϱ⁻¹)
      (_hmove : ∀ᶠ M in atTop, ∀ (γ : SourceRoute D M)
        (G : (actualLayout D typ t ht k hk MOff Mcoal Kdiam M).Φ) (t' : ℕ)
        (x : (actualLayout D typ t ht k hk MOff Mcoal Kdiam M).X),
        (actualLayout D typ t ht k hk MOff Mcoal Kdiam M).moveCtx G
          (routeLab M γ.position t') x → ϱ⁻¹ ≤
        localSuccessProbability pc q
          ((actualLayout D typ t ht k hk MOff Mcoal Kdiam M).Bl₀ G.1
            (routeLab M γ.position t'))
          (bitSet G.2 (fun z =>
            (actualLayout D typ t ht k hk MOff Mcoal Kdiam M).moveTypical G
              (routeLab M γ.position t') x
              ((actualLayout D typ t ht k hk MOff Mcoal Kdiam M).view G.1
                (routeLab M γ.position t') z))))
      (_hpre : ∀ a : Vertex (D + 1), κ⁻¹ ≤
        ∫ ω, (if IsPreGoodCube typ t (coarseCenter t a) ω then (1:ℝ) else 0)
          ∂(percolation (D + 1) pc))
      (_hGM : ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ B : ℝ, 0 < B ∧ ∃ R : ℝ,
        UniformChemicalLowerTail (D + 1) (orParameter pc q) N μ ε B R),
      μ ≤ 2 * ((4 * (Asp + Ask) * (n0 : ℝ) + 1) * (ellStar : ℝ)) := by
  obtain ⟨q0, hq0, hq1, hmain⟩ := chemical_timeConstant_upper_actual hD
  refine ⟨q0, hq0, hq1, ?_⟩
  intro pc q N hunit hreflect μ Asp Ask hμ hAsp hAsk ϱ κ hϱ hκ hΛq typ t ht k hk MOff Mcoal
    Kdiam n0 ellStar hscale hstar hA hB hk2 hcount hexitParam hmove hpre hGM
  have hkle : (k : ℝ) ≤ 2 * (k : ℝ) ^ 4 := by
    have h1 : (1:ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    nlinarith [pow_le_pow_left₀ (by linarith : (0:ℝ) ≤ 1) h1 3, pow_nonneg (by linarith : (0:ℝ) ≤ (k:ℝ)) 3,
      pow_succ (k : ℝ) 3]
  refine hmain pc q N hunit hreflect hμ hAsp hAsk hϱ hκ hΛq typ t ht k hk MOff Mcoal Kdiam
    hscale hstar hA hB (hkle.trans hcount) ?_ ?_ hGM
  · filter_upwards [hmove] with M hM
    exact (actualLayout D typ t ht k hk MOff Mcoal Kdiam M).hs_of_move (by show 0 < t; omega)
      M pc q hϱ hexitParam hM
  · exact Filter.Eventually.of_forall (fun M =>
      (actualLayout D typ t ht k hk MOff Mcoal Kdiam M).hsite_of_pre pc q hκ
        (fun s _ => hpre (vecSite s)))

end NearCritical
