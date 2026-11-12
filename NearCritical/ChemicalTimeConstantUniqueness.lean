import NearCritical.ChemicalTimeConstant
import NearCritical.ExternalUniquenessActual
import NearCritical.ExternalCriticalPointPos

/-!
`thm.time_constant` sandwich with two of its named inputs discharged:
`0 < p_c` (`External.criticalPoint_pos`) and almost-sure uniqueness of the
infinite cluster (`External.aeInfiniteClusterUniqueness`, the imported
Burton--Keane theorem transferred through the model-law bridge).

Remaining inputs are those of `time_constant_sandwich_conditional`: the cited
subcritical decay `hHMS`, the cited chemical limit and lower tail, and the
crossing probability `hcross` (for which see
`chemical_timeConstant_upper_of_nestRules`).
-/

namespace NearCritical
open Set MeasureTheory Filter

theorem time_constant_sandwich_unique {d : ℕ} (i : Fin d)
    -- lower-bound inputs (prop.chem.lower)
    {cH CH : ℝ} (hcH : 0 < cH)
    (hHMS : ∀ q : unitInterval, 0 < (q : ℝ) → (q : ℝ) ≤ (criticalPoint d : ℝ) →
      RayExponentialConnectionBound d q (Pi.single i 1) CH
        (cH * Real.sqrt ((criticalPoint d : ℝ) - (q : ℝ))))
    -- shared standard inputs
    (M : unitInterval → ℝ) (N : unitInterval → Seminorm ℝ (Fin d → ℝ))
    (hlimit : ∀ p : unitInterval, criticalPoint d < p →
      AEConnectedChemicalLimit d p (Pi.single i 1) (M p))
    -- upper-bound inputs (prop.chem.upper)
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
  time_constant_sandwich_conditional i (External.criticalPoint_pos (Fin.pos i)) hcH hHMS M N
    (fun p _ => External.aeInfiniteClusterUniqueness d p) hlimit p₁ h₁ hC hc hunit hreflect
    hGM scales hscales hcross

end NearCritical
