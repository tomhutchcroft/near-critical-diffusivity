module

public import NearCritical.ChemicalTimeConstant
public import NearCritical.CriticalPointInterior

/-! The conditional thm.time_constant sandwich with `p_c > 0` derived from the paper's standing
assumption (A) (`TwoPointAsymptotics d`, via `criticalPoint_pos_of_twoPointAsymptotics`) instead of
assumed. All other inputs of `time_constant_sandwich_conditional` remain explicit, including the
OPEN lem.chem.crossing input `hcross`. Not a proof of thm.time_constant. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Set MeasureTheory Filter

theorem time_constant_sandwich_of_assumptionA {d : ℕ} (i : Fin d)
    (hA : TwoPointAsymptotics d)
    {cH CH : ℝ} (hcH : 0 < cH)
    (hHMS : ∀ q : unitInterval, 0 < (q : ℝ) → (q : ℝ) ≤ (criticalPoint d : ℝ) →
      RayExponentialConnectionBound d q (Pi.single i 1) CH
        (cH * Real.sqrt ((criticalPoint d : ℝ) - (q : ℝ))))
    (M : unitInterval → ℝ) (N : unitInterval → Seminorm ℝ (Fin d → ℝ))
    (huniq : ∀ p : unitInterval, criticalPoint d < p → AEInfiniteClusterUniqueness d p)
    (hlimit : ∀ p : unitInterval, criticalPoint d < p →
      AEConnectedChemicalLimit d p (Pi.single i 1) (M p))
    (p₁ : unitInterval) (h₁ : criticalPoint d < p₁) {C c : ℝ} (hC : 0 ≤ C) (hc : 0 < c)
    (hunit : ∀ p : unitInterval, criticalPoint d < p → ∀ j, (N p) (Pi.single j 1) = 1)
    (hreflect : ∀ p : unitInterval, criticalPoint d < p → ∀ j x,
      (N p) (coordinateReflection j x) = (N p) x)
    (hGM : ∀ p : unitInterval, criticalPoint d < p → ∀ ε : ℝ, ε ∈ Ioo 0 1 →
      ∃ B : ℝ, 0 < B ∧ ∃ R : ℝ, UniformChemicalLowerTail d p (N p) (M p) ε B R)
    (scales : unitInterval → ℕ → ℕ)
    (hscales : ∀ p : unitInterval, criticalPoint d < p → p ≤ p₁ →
      Tendsto (scales p) atTop atTop)
    (hcross : ∀ p : unitInterval, criticalPoint d < p → p ≤ p₁ → ∀ᶠ n : ℕ in atTop,
      c ≤ (percolation d p).real (chemicalSpanEvent i (scales p n)
        (C * (chemicalCorrelationScale d p : ℝ)))) :
    ∃ cl Cu : ℝ, 0 < cl ∧ 0 < Cu ∧ ∀ p : unitInterval, criticalPoint d < p →
      cl / Real.sqrt ((p : ℝ) - (criticalPoint d : ℝ)) ≤ M p ∧
        M p ≤ Cu / Real.sqrt ((p : ℝ) - (criticalPoint d : ℝ)) :=
  time_constant_sandwich_conditional i (criticalPoint_pos_of_twoPointAsymptotics i hA) hcH hHMS
    M N huniq hlimit p₁ h₁ hC hc hunit hreflect hGM scales hscales hcross

end NearCritical
