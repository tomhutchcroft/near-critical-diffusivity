import NearCritical.Section7LowerWaterAll
import NearCritical.ExternalCriticalPointPos

/-!
Source `prop.lower_water` with the hypothesis `0 < p_c` removed, using the
unconditional `External.criticalPoint_pos`. The only remaining input is the
paper lemma `lem.spanning.diam` (`SpanningDiamStatement`).

-/

namespace NearCritical.Section7

/-- **Source `prop.lower_water`, `eq.lower_water_general`, at every scale**, from
`lem.spanning.diam` alone. -/
theorem lower_water_general_all_of_spanningDiam {d : ℕ} (hd : 6 ≤ d) (i : Fin d)
    (hS : SpanningDiamStatement d) :
    ∃ c : ℝ, 0 < c ∧ ∀ r : ℕ,
      c / (2*(r:ℝ)+1)^6 ≤ annealedRelaxed (centeredBox d r) i (criticalPoint d : ℝ) :=
  lower_water_general_all hd i (External.criticalPoint_pos (by omega)) hS

/-- **Source `prop.lower_water`, `eq.lower_water`, for every `p > p_c`**, from
`lem.spanning.diam` alone. -/
theorem lower_water_all_of_spanningDiam {d : ℕ} (hd : 6 ≤ d) (i : Fin d)
    (hS : SpanningDiamStatement d) :
    ∃ c : ℝ, 0 < c ∧ ∀ p : unitInterval, criticalPoint d < p →
      ∀ r : ℕ, 2*r+1 ≤ chemicalCorrelationScale d p →
        c * ((p:ℝ) - (criticalPoint d : ℝ))^3 ≤
          annealedRelaxed (centeredBox d r) i (p:ℝ) :=
  lower_water_all hd i (External.criticalPoint_pos (by omega)) hS

end NearCritical.Section7
