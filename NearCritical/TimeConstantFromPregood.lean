import NearCritical.TimeConstantFromPaperProps
import NearCritical.Section10MoveCapstone
import NearCritical.CriticalPointInterior
import NearCritical.ThreePointDiagram

/-!
`thm.time_constant` in dimension `d = m + 6 >= 9` with `prop.proba.k-nest` DISCHARGED.

`time_constant_sandwich_of_pregood` is `time_constant_sandwich_of_paper_props`
with its hypothesis `hmove` replaced by `Section10.actualLayout_hmove`. What
remains per `p` in `(p_c, p₁]` is

* `prop.proba.pregood` (`hpre`), and
* explicit PARAMETER RELATIONS between the sprinkle parameter, the mesh, `k`,
  the typicality constants and the constants of the Section 9 theorem, which
  appear here in their order of choice
  (`G₀`; `delta`; `r`, `eps`; `cSize`; `mo`; `Lambda`; `CB`, `KA`; `N₀`).

CITED inputs: assumption (A) (`TwoPointAsymptotics`), the restricted rectangle
lower bound, Reimer's inequality, the subcritical ray decay, the chemical
limit and its lower tail. `0 < p_c < 1` and the Green bound are derived.

The joint satisfiability of the parameter relations is NOT proved here.
-/

namespace NearCritical
open Set MeasureTheory Filter
open NearCritical.Section10
open scoped Classical

theorem time_constant_sandwich_of_pregood (m : ℕ) (hm : 3 ≤ m)
    (asymptotics : TwoPointAsymptotics (m + 5 + 1))
    (rectangle : RestrictedRectangleLowerInput (m + 5 + 1)) (reimer : FiniteBernoulliBKRInput) :
    ∃ q0 : ℝ, (0 < q0 ∧ q0 < 1) ∧ ∃ G₀ : ℝ, 0 < G₀ ∧
    ∃ δ : ℝ, 0 < δ ∧ ∀ r : ℕ, 1 ≤ r → ∀ ε : ℝ, 0 < ε →
      ∃ cSize : ℝ, 0 < cSize ∧ ∀ mo : ℕ, ∃ Lambda : ℝ, 0 < Lambda ∧
      ∀ CB KA : ℝ, 0 < CB → 0 < KA →
      ∃ N₀ : ℕ, 16*(r+1) ≤ N₀ ∧
    ∀ {cH CH : ℝ} (_hcH : 0 < cH)
      (_hHMS : ∀ q : unitInterval, 0 < (q : ℝ) → (q : ℝ) ≤ (criticalPoint (m + 5 + 1) : ℝ) →
        RayExponentialConnectionBound (m + 5 + 1) q (Pi.single 0 1) CH
          (cH * Real.sqrt ((criticalPoint (m + 5 + 1) : ℝ) - (q : ℝ))))
      (M : unitInterval → ℝ) (N : unitInterval → Seminorm ℝ (Fin (m + 5 + 1) → ℝ))
      (_hlimit : ∀ p : unitInterval, criticalPoint (m + 5 + 1) < p →
        AEConnectedChemicalLimit (m + 5 + 1) p (Pi.single 0 1) (M p))
      (p₁ : unitInterval) (_h₁ : criticalPoint (m + 5 + 1) < p₁)
      (_hunit : ∀ p : unitInterval, criticalPoint (m + 5 + 1) < p →
        ∀ j, (N p) (Pi.single j 1) = 1)
      (_hreflect : ∀ p : unitInterval, criticalPoint (m + 5 + 1) < p → ∀ j x,
        (N p) (coordinateReflection j x) = (N p) x)
      (_hGM : ∀ p : unitInterval, criticalPoint (m + 5 + 1) < p → ∀ ε : ℝ, ε ∈ Ioo 0 1 →
        ∃ B : ℝ, 0 < B ∧ ∃ R : ℝ, UniformChemicalLowerTail (m + 5 + 1) p (N p) (M p) ε B R)
      {Asp Ask ϱ κ : ℝ} (_hAsp : 0 ≤ Asp) (_hAsk : 0 ≤ Ask) (_hϱ : 1 ≤ ϱ) (_hκ : 1 ≤ κ)
      (_hΛq : (ϱ * κ) ^ 2 * q0 < 1) (n0 : ℕ)
      (_hpaper : ∀ p : unitInterval, criticalPoint (m + 5 + 1) < p → p ≤ p₁ →
        ∃ (q : unitInterval) (typ : TypicalParameters) (t : ℕ) (_ht : 9 ≤ t) (k : ℕ)
          (_hk : 0 < k) (MOff Mcoal Kdiam : ℕ) (q0' : ℝ),
          orParameter (criticalPoint (m + 5 + 1)) q = p ∧
          2 * t = n0 * chemicalCorrelationScale (m + 5 + 1) p ∧
          1 ≤ chemicalCorrelationScale (m + 5 + 1) p ∧
          2 * (typ.diameterUpper * (2 * (t : ℝ)) ^ 2) = Asp * ((2 * t : ℕ) : ℝ) ^ 2 ∧
          (Kdiam : ℝ) = Ask * ((2 * t : ℕ) : ℝ) ^ 2 ∧
          2 ≤ k ∧
          2 * (k : ℝ) ^ 4 ≤ typ.countLower * (2 * (t : ℝ)) ^ (m + 5 + 1 - 6) ∧
          (∀ j : ℕ, typ.boundaryLower * (2 * (t : ℝ)) ^ 2 ≤ (j : ℝ) →
            ((1 - (criticalPoint (m + 5 + 1) : ℝ)) * (1 - (q:ℝ))) ^ j ≤ 1 - ϱ⁻¹) ∧
          (N₀ ≤ t ∧ typ.regularRadius = r ∧ typ.regularTolerance ≤ δ ∧
            0 ≤ typ.boundaryUpper ∧ 0 ≤ typ.countUpper ∧
            0 ≤ typ.boundaryLower ∧ 0 ≤ typ.countLower ∧
            0 ≤ q0' ∧ Lambda ≤ (q : ℝ)*(t : ℝ)^2 ∧ (q : ℝ) ≤ q0' / (t : ℝ)^2 ∧
            10 ≤ 2 * k ^ 4 ∧ 2 * k ^ 4 ≤ mo + 1 ∧
            4 * (k : ℝ) * typ.boundaryUpper ≤ KA ∧ 8 * typ.boundaryUpper ≤ CB ∧
            cSize ≤ 4 * (k : ℝ) * typ.boundaryLower ∧
            cSize ≤ 4 * typ.countLower * typ.boundaryLower * (2 * (t : ℝ)) ^ (m + 5 + 1 - 6) ∧
            cSize ≤ 16 * (k : ℝ) * typ.countLower * typ.boundaryLower ^ 2 ∧
            (∀ c : Vertex (m + 5 + 1), (typicalCube t c).card ≤ MOff) ∧
            (∀ c : Vertex (m + 5 + 1), (typicalCube t c).card ≤ Mcoal) ∧
            ϱ⁻¹ ≤ 1 - ε - (1 + diamConst m k typ G₀ q0' * (t : ℝ) ^ 2) / ((Kdiam : ℝ) + 1)) ∧
          (∀ a : Vertex (m + 5 + 1), κ⁻¹ ≤
            ∫ ω, (if IsPreGoodCube typ t (coarseCenter t a) ω then (1:ℝ) else 0)
              ∂(percolation (m + 5 + 1) (criticalPoint (m + 5 + 1))))),
      ∃ cl Cu : ℝ, 0 < cl ∧ 0 < Cu ∧ ∀ p : unitInterval, criticalPoint (m + 5 + 1) < p →
        cl / Real.sqrt ((p : ℝ) - (criticalPoint (m + 5 + 1) : ℝ)) ≤ M p ∧
          M p ≤ Cu / Real.sqrt ((p : ℝ) - (criticalPoint (m + 5 + 1) : ℝ)) := by
  obtain ⟨q0, hq0, hq1, hmain⟩ :=
    time_constant_sandwich_of_paper_props (D := m + 5) (by omega)
  obtain ⟨G₀, hG₀, hG⟩ := criticalSupGreenUpper_of_asymptotics (d := m + 5 + 1) (by omega)
    asymptotics
  have hp0 : 0 < (criticalPoint (m + 5 + 1) : ℝ) :=
    External.criticalPoint_pos (Nat.succ_pos (m + 5))
  have hp1 : (criticalPoint (m + 5 + 1) : ℝ) < 1 :=
    criticalPoint_lt_one_of_twoPointAsymptotics (by omega) (0 : Fin (m + 5 + 1)) asymptotics
  obtain ⟨δ, hδ, hmv⟩ := actualLayout_hmove m (by omega) asymptotics rectangle reimer hp0 hp1
    hG₀.le hG
  refine ⟨q0, ⟨hq0, hq1⟩, G₀, hG₀, δ, hδ, ?_⟩
  intro r hr ε hε
  obtain ⟨cSize, hSize, hmo⟩ := hmv r hr ε hε
  refine ⟨cSize, hSize, ?_⟩
  intro mo
  obtain ⟨Lambda, hLambda, hCBKA⟩ := hmo mo
  refine ⟨Lambda, hLambda, ?_⟩
  intro CB KA hCBpos hKApos
  obtain ⟨N₀, hN₀, hrest⟩ := hCBKA CB KA hCBpos hKApos
  refine ⟨N₀, hN₀, ?_⟩
  intro cH CH hcH hHMS M N hlimit p₁ h₁ hunit hreflect hGM Asp Ask ϱ κ hAsp hAsk hϱ hκ hΛq n0
    hpaper
  refine hmain hcH hHMS M N hlimit p₁ h₁ hunit hreflect hGM hAsp hAsk hϱ hκ hΛq n0 ?_
  intro p hp hpp
  obtain ⟨q, typ, t, ht, k, hk, MOff, Mcoal, Kdiam, q0', h1, h2, h3, h4, h5, h6, h7, h8,
    ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20⟩,
    hpre⟩ := hpaper p hp hpp
  refine ⟨q, typ, t, ht, k, hk, MOff, Mcoal, Kdiam, h1, h2, h3, h4, h5, h6, h7, h8, ?_, hpre⟩
  exact Filter.Eventually.of_forall (fun Mb γ G t' x hctx =>
    hrest typ t ht a1 a2 a3 a4 a5 a6 a7 q q0' a8 a9 a10 k hk a11 a12 a13 a14 a15 a16 a17
      MOff Mcoal Kdiam a18 a19 a20 Mb γ G t' x hctx)

end NearCritical
