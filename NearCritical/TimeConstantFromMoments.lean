import NearCritical.TimeConstantFinal
import NearCritical.Section10PreGoodFromMoments

/-!
`thm.time_constant` from the cited inputs and ONE moment package.

`time_constant_of_moments`: in dimension `d = m + 6`, `m >= 3`, the two-sided
bound `c/sqrt(p - p_c) <= M(p) <= C/sqrt(p - p_c)` on the time constant, with
the pre-good hypothesis of `time_constant_sandwich_final` DISCHARGED by
`pregood_hypothesis_of_moments`.

Hypotheses: the cited inputs of both halves (assumption (A), restricted
rectangle lower bound, BKR, split crossing, far-face tail, boundary first moment
[derivable from the half-space pioneers: `boxFaceFirstMoment_of_normalized`],
eq.cluster_size, one arm, ray decay, chemical limit and lower tail), fractions
`a_i > 0` with sum `< 1`, and the moment package `hmom` at the tolerance `δ`
produced by the theorem: the regularity-energy moment bounds of prop.choice_c
(two conditional means, centred second moments, hitting probability, marked
boundary size), which are NOT derived here.
-/

namespace NearCritical
open Set MeasureTheory Filter
open NearCritical.Section10
open scoped Classical

set_option maxHeartbeats 800000 in
theorem time_constant_of_moments (m : ℕ) (hm : 3 ≤ m) {d : ℕ} (hdm : d = m + 5 + 1)
    (hA : TwoPointAsymptotics d) (rectangle : RestrictedRectangleLowerInput d)
    (reimer : FiniteBernoulliBKRInput) :
    ∃ q0 : ℝ, 0 < q0 ∧ q0 < 1 ∧ ∃ δ : ℝ, 0 < δ ∧
    ∀ {c₀ K B Carm α A c : ℝ} (hc₀ : 0 < c₀) (hK : 0 ≤ K) (hB0 : 0 ≤ B) (hCarm : 0 < Carm)
    (hcross : SplitCrossInput d c₀)
    (htail : ∀ (N : ℕ) (x : Vertex d), x ∈ centeredBox d N →
      ∀ (f : Fin d × Bool) (T : ℝ), 0 < T →
        (percolation d (criticalPoint d)).real (Section7.farFaceEvent N x f T) ≤ K / T)
    (hBm : BoxFaceFirstMoment d B) (hsize : ClusterSizeInput d α A c) (ordinary : OrdinaryArmWindowInput d Carm)
    {a₁ a₂ a₃ : ℝ}
    (ha₁ : 0 ≤ a₁) (ha₂ : 0 ≤ a₂) (ha₃ : 0 ≤ a₃) (hsum : a₁ + a₂ + a₃ < 1)
    (hc : 0 < c) (ha₁' : 0 < a₁) (ha₂' : 0 < a₂) (ha₃' : 0 < a₃)
    (hmom : ∃ cc : ℝ, 0 < cc ∧ cc ≤ 1 / 16 ∧ ∃ Cm Cp Cb : ℝ, 0 ≤ Cm ∧ 0 ≤ Cp ∧ 0 ≤ Cb ∧
      ∃ rstar : ℕ, ∀ typ : TypicalParameters, typ.heartRatio = cc →
        typ.regularTolerance = δ → rstar ≤ typ.regularRadius →
        ∃ t₁ : ℕ, ∀ t : ℕ, t₁ ≤ t →
          (∀ x ∈ typMark t (0 : Vertex d),
      heartConditionalMean (criticalPoint d) (typicalCube t 0)
        (typicalHeart t 0 typ.heartRatio)
        (fun F => regularityEnergyOne F (typicalInnerCube t 0) typ.regularRadius x) x ≤
          typ.regularTolerance / 2) ∧
          (∀ x ∈ typMark t (0 : Vertex d),
      heartConditionalMean (criticalPoint d) (typicalCube t 0)
        (typicalHeart t 0 typ.heartRatio)
        (fun F => regularityEnergyTwo F (typicalBoundary t 0) typ.regularRadius x) x ≤
          typ.regularTolerance / 2) ∧
          (∀ x ∈ typMark t (0 : Vertex d),
      heartCenteredMoment (criticalPoint d) (typicalCube t 0)
        (typicalHeart t 0 typ.heartRatio)
        (fun F => regularityEnergyOne F (typicalInnerCube t 0) typ.regularRadius x) x +
      heartCenteredMoment (criticalPoint d) (typicalCube t 0)
        (typicalHeart t 0 typ.heartRatio)
        (fun F => regularityEnergyTwo F (typicalBoundary t 0) typ.regularRadius x) x ≤
      (Cm / (typ.regularRadius : ℝ) ^ (d - 6)) * (percolation d (criticalPoint d)).real
        {ω | x ∈ heartClusterUnion ω (typicalCube t 0) (typicalHeart t 0 typ.heartRatio)}) ∧
          (∀ x ∈ typMark t (0 : Vertex d), (percolation d (criticalPoint d)).real
        {ω | x ∈ heartClusterUnion ω (typicalCube t 0) (typicalHeart t 0 typ.heartRatio)} ≤
      Cp / (2 * (t : ℝ)) ^ 3) ∧
          (((typMark t (0 : Vertex d)).card : ℝ) ≤ Cb * (2 * (t : ℝ)) ^ (d - 1))),
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
  subst hdm
  obtain ⟨q0, hq0, hq1, δ, hδ, hcap⟩ := time_constant_sandwich_final m hm hA rectangle reimer
  refine ⟨q0, hq0, hq1, δ, hδ, ?_⟩
  intro c₀ K B Carm α A c hc₀ hK hB0 hCarm hcross htail hBm hsize ordinary a₁ a₂ a₃ ha₁ ha₂ ha₃
    hsum hc ha₁' ha₂' ha₃' hmom
  obtain ⟨typ, κ, t₀, h1, h2, h3, h4, h5, h6, h7, h8, h9, hpre⟩ :=
    pregood_hypothesis_of_moments (by omega) hA hc₀ hK hB0 hCarm hcross htail hBm hsize ordinary
      ha₁ ha₂ ha₃ hsum hc ha₁' ha₂' ha₃' hq0 hq1 hδ hmom
  exact hcap typ h1 h2 h3 h4 h5 h6 h7 h8 h9 t₀ (fun t ht a => hpre t ht _)

end NearCritical
