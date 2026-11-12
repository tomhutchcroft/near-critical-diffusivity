import NearCritical.TimeConstantFromPregood
import NearCritical.Section10RelationsWitness
import NearCritical.Section10LowerScale

/-!
`thm.time_constant` in dimension `d = m + 6 >= 9` from the cited inputs and
`prop.proba.pregood` ONLY.

`time_constant_sandwich_final`: there are `q0` in `(0,1)` and `delta > 0`
(depending on the dimension and the cited inputs) such that for every choice of
typicality parameters `typ` with regularity radius `>= 1`, tolerance
`<= delta`, positive lower constants, and every `kappa >= 1` with
`kappa^2 q0 < 1`, if every cube at every scale `t >= t₀` is pre-good with
`P_{p_c}`-probability at least `1/kappa`, then

  `c / sqrt(p - p_c) <= mu(p) <= C / sqrt(p - p_c)`   for all `p > p_c`.

All parameter relations of `time_constant_sandwich_of_pregood` are discharged
here by `Section10.move_relations_witness`; the statement is therefore
non-vacuous as soon as the pre-good hypothesis holds.

CITED inputs: assumption (A), the restricted rectangle lower bound, Reimer's
inequality, the subcritical ray decay, the chemical limit and its lower tail.
PAPER-INTERNAL input still assumed: `prop.proba.pregood` (`hpre`).
-/

namespace NearCritical
open Set MeasureTheory Filter
open NearCritical.Section10
open scoped Classical

theorem time_constant_sandwich_final (m : ℕ) (hm : 3 ≤ m)
    (asymptotics : TwoPointAsymptotics (m + 5 + 1))
    (rectangle : RestrictedRectangleLowerInput (m + 5 + 1)) (reimer : FiniteBernoulliBKRInput) :
    ∃ q0 : ℝ, 0 < q0 ∧ q0 < 1 ∧ ∃ δ : ℝ, 0 < δ ∧
    ∀ (typ : TypicalParameters), 1 ≤ typ.regularRadius → typ.regularTolerance ≤ δ →
      0 < typ.boundaryLower → 0 < typ.countLower → 0 ≤ typ.boundaryUpper →
      0 ≤ typ.countUpper → 0 ≤ typ.diameterUpper →
    ∀ {κ : ℝ}, 1 ≤ κ → κ ^ 2 * q0 < 1 → ∀ (t₀ : ℕ),
      (∀ t : ℕ, t₀ ≤ t → ∀ a : Vertex (m + 5 + 1), κ⁻¹ ≤
        ∫ ω, (if IsPreGoodCube typ t (coarseCenter t a) ω then (1:ℝ) else 0)
          ∂(percolation (m + 5 + 1) (criticalPoint (m + 5 + 1)))) →
    ∀ {cH CH : ℝ} (_hcH : 0 < cH)
      (_hHMS : ∀ q : unitInterval, 0 < (q : ℝ) → (q : ℝ) ≤ (criticalPoint (m + 5 + 1) : ℝ) →
        RayExponentialConnectionBound (m + 5 + 1) q (Pi.single 0 1) CH
          (cH * Real.sqrt ((criticalPoint (m + 5 + 1) : ℝ) - (q : ℝ))))
      (M : unitInterval → ℝ) (N : unitInterval → Seminorm ℝ (Fin (m + 5 + 1) → ℝ))
      (_hlimit : ∀ p : unitInterval, criticalPoint (m + 5 + 1) < p →
        AEConnectedChemicalLimit (m + 5 + 1) p (Pi.single 0 1) (M p))
      (_hunit : ∀ p : unitInterval, criticalPoint (m + 5 + 1) < p →
        ∀ j, (N p) (Pi.single j 1) = 1)
      (_hreflect : ∀ p : unitInterval, criticalPoint (m + 5 + 1) < p → ∀ j x,
        (N p) (coordinateReflection j x) = (N p) x)
      (_hGM : ∀ p : unitInterval, criticalPoint (m + 5 + 1) < p → ∀ ε : ℝ, ε ∈ Ioo 0 1 →
        ∃ B : ℝ, 0 < B ∧ ∃ R : ℝ, UniformChemicalLowerTail (m + 5 + 1) p (N p) (M p) ε B R),
      ∃ cl Cu : ℝ, 0 < cl ∧ 0 < Cu ∧ ∀ p : unitInterval, criticalPoint (m + 5 + 1) < p →
        cl / Real.sqrt ((p : ℝ) - (criticalPoint (m + 5 + 1) : ℝ)) ≤ M p ∧
          M p ≤ Cu / Real.sqrt ((p : ℝ) - (criticalPoint (m + 5 + 1) : ℝ)) := by
  obtain ⟨q0, ⟨hq0, hq1⟩, G₀, hG₀, δ, hδ, hcap⟩ :=
    time_constant_sandwich_of_pregood m hm asymptotics rectangle reimer
  have hp0 : 0 < (criticalPoint (m + 5 + 1) : ℝ) :=
    External.criticalPoint_pos (Nat.succ_pos (m + 5))
  have hp1 : (criticalPoint (m + 5 + 1) : ℝ) < 1 :=
    criticalPoint_lt_one_of_twoPointAsymptotics (by omega) (0 : Fin (m + 5 + 1)) asymptotics
  refine ⟨q0, hq0, hq1, δ, hδ, ?_⟩
  intro typ hrad htol hbL hcL hbU hcU hdU κ hκ hκq t₀ hpre cH CH hcH hHMS M N hlimit hunit
    hreflect hGM
  -- choice of rho
  have hκ0 : 0 < κ := by linarith
  set s : ℝ := κ ^ 2 * q0 with hs
  have hs0 : 0 < s := by positivity
  obtain ⟨ϱ, hϱdef⟩ : ∃ ϱ : ℝ, ϱ = Real.sqrt ((1 + s) / (2 * s)) := ⟨_, rfl⟩
  have harg : 1 < (1 + s) / (2 * s) := by
    rw [lt_div_iff₀ (by positivity)]
    linarith
  have hϱ1 : 1 < ϱ := by
    have hlt : Real.sqrt 1 < Real.sqrt ((1 + s) / (2 * s)) :=
      Real.sqrt_lt_sqrt (by norm_num) harg
    rw [Real.sqrt_one] at hlt
    rw [hϱdef]
    exact hlt
  have hϱsq : ϱ ^ 2 = (1 + s) / (2 * s) := by
    rw [hϱdef]
    exact Real.sq_sqrt (by positivity)
  have hΛq : (ϱ * κ) ^ 2 * q0 < 1 := by
    have h1 : (ϱ * κ) ^ 2 * q0 = ϱ ^ 2 * s := by
      rw [hs]
      ring
    rw [h1, hϱsq, div_mul_eq_mul_div, div_lt_one (by positivity)]
    nlinarith
  have hϱinv : ϱ⁻¹ < 1 := inv_lt_one_of_one_lt₀ hϱ1
  -- constants of the capstone, in order
  obtain ⟨cSize, hSize, hmo⟩ := hcap typ.regularRadius hrad ((1 - ϱ⁻¹) / 2) (by linarith)
  obtain ⟨k, hk2, hk10, hc1, hc3, hwit⟩ := move_relations_witness m (by omega) hp0 hp1 typ hbL hcL
    hbU hcU hϱ1 hG₀.le hSize
  obtain ⟨Lambda, hLambda, hCBKA⟩ := hmo (2 * k ^ 4 - 1)
  obtain ⟨N₀, _, hrest⟩ := hCBKA (8 * typ.boundaryUpper + 1) (4 * (k : ℝ) * typ.boundaryUpper + 1)
    (by positivity) (by positivity)
  obtain ⟨a, AskN, p₁, ha1, hp₁, hper⟩ := hwit Lambda hLambda (max N₀ t₀)
  have hk0 : 0 < k := by omega
  have hexp : m + 5 + 1 - 6 = m := by omega
  refine hrest hcH hHMS M N hlimit p₁ hp₁ hunit hreflect hGM (Asp := 2 * typ.diameterUpper)
    (Ask := (AskN : ℝ)) (ϱ := ϱ) (κ := κ) (by positivity) (Nat.cast_nonneg _) hϱ1.le hκ hΛq
    (2 * a) ?_
  intro p hp hpp
  obtain ⟨q, hq, hmesh, ht9, htN, hcount, hcs2, hexit, hqlo, hqhi, hprob⟩ := hper p hp hpp
  have htN₀ : N₀ ≤ a * chemicalCorrelationScale (m + 5 + 1) p := (le_max_left _ _).trans htN
  have htt₀ : t₀ ≤ a * chemicalCorrelationScale (m + 5 + 1) p := (le_max_right _ _).trans htN
  have hcube : ∀ c : Vertex (m + 5 + 1),
      (typicalCube (a * chemicalCorrelationScale (m + 5 + 1) p) c).card ≤
      (typicalCube (a * chemicalCorrelationScale (m + 5 + 1) p) (0 : Vertex (m + 5 + 1))).card := by
    intro c
    have h := typicalCube_translate (a * chemicalCorrelationScale (m + 5 + 1) p) c
      (0 : Vertex (m + 5 + 1))
    rw [add_zero] at h
    rw [h, card_translateSites]
  refine ⟨q, typ, a * chemicalCorrelationScale (m + 5 + 1) p, ht9, k, hk0,
    (typicalCube (a * chemicalCorrelationScale (m + 5 + 1) p) (0 : Vertex (m + 5 + 1))).card,
    (typicalCube (a * chemicalCorrelationScale (m + 5 + 1) p) (0 : Vertex (m + 5 + 1))).card,
    AskN * (2 * (a * chemicalCorrelationScale (m + 5 + 1) p)) ^ 2,
    ((2 * a : ℕ) : ℝ) ^ 2 / (4 * (1 - (criticalPoint (m + 5 + 1) : ℝ))),
    hq, hmesh, chemicalCorrelationScale_pos p hp, ?_, ?_, hk2, ?_, hexit, ?_, ?_⟩
  · push_cast
    ring
  · push_cast
    ring
  · rw [hexp]
    exact hcount
  · refine ⟨htN₀, rfl, htol, hbU, hcU, hbL.le, hcL.le, ?_, hqlo, hqhi, hk10, ?_, ?_, ?_, hc1, ?_,
      hc3, hcube, hcube, hprob⟩
    · have h1 : (0:ℝ) < 1 - (criticalPoint (m + 5 + 1) : ℝ) := by linarith
      positivity
    · have : 1 ≤ 2 * k ^ 4 := by omega
      omega
    · linarith
    · linarith
    · rw [hexp]
      exact hcs2
  · intro a'
    exact hpre _ htt₀ a'

end NearCritical
