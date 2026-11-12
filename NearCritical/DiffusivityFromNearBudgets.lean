import NearCritical.DiffusivityEinsteinLower
import NearCritical.DiffusivityLowerExtension
import NearCritical.Section10AllRadiusLimit

/-!
`thm.main` for the Einstein-relation diffusivity from the output of source
`prop.nw.main` on a near-critical window.

`einsteinDiffusivity_two_sided_of_near_flowBudgets`: the cited pioneer and
one-arm inputs, `p_c < 1`, the cited density upper bound, and

  `hbudget`: there are `p_1 > p_c` and constants `a, C > 0` such that for every
  `p` in `(p_c, p_1]` the flow budget `cubeFlowBudget p i R a C` holds along the
  affine source radii `R = chemicalCoarseRadius M t r`, eventually in `M`
  (the scales `t, r` may depend on `p`),

give `c (p - p_c)^2 <= 2 kappa(p)/theta(p) <= C (p - p_c)^2` on all of
`(p_c, 1]`. `hbudget` is the conclusion of the Section 10 flow construction
(main.tex 5758--5807) and is the only non-cited hypothesis. It is OPEN.
-/

namespace NearCritical
noncomputable section
open Filter

theorem fullCubeLimit_lowerPowerBound_of_near_flowBudgets {d : ℕ} (i : Fin d)
    (hbudget : ∃ p1 a C : ℝ, (criticalPoint d : ℝ) < p1 ∧ p1 ≤ 1 ∧ 0 < a ∧ 0 < C ∧
      ∀ p : unitInterval, criticalPoint d < p → (p : ℝ) ≤ p1 →
        ∃ t r : ℕ, 1 ≤ t ∧
          ∀ᶠ M : ℕ in atTop, Section10.cubeFlowBudget p i (chemicalCoarseRadius M t r) a C) :
    LowerPowerBound (criticalPoint d : ℝ) (fullCubeLimit d i) 3 := by
  obtain ⟨p1, a, C, hp1, hp1', ha, hC, hbud⟩ := hbudget
  refine fullCubeLimit_lowerPowerBound_of_near i hp1 hp1' (c := a ^ 2 / C) (by positivity) ?_
  intro p hp hple
  have hp0 : 0 ≤ p := le_trans (criticalPoint d).2.1 hp.le
  obtain ⟨t, r, ht, hev⟩ := hbud ⟨p, hp0, hple.trans hp1'⟩ (Subtype.coe_lt_coe.mp hp) hple
  exact Section10.coefficient_cubic_lower_of_triadic_affine_budgets i
    (triadicDirichletLimitInput_fullCubeLimit d i) ⟨p, hp0, hple.trans hp1'⟩
    (Subtype.coe_lt_coe.mp hp) ht r ha hC hev

/-- **`thm.main` (Einstein-relation diffusivity) from near-critical flow
budgets and cited inputs.** -/
theorem einsteinDiffusivity_two_sided_of_near_flowBudgets {d : ℕ} (i : Fin d) {B b Co : ℝ}
    (hB : 0 < B) (hb : 0 < b) (hCo : 0 ≤ Co)
    (hpc1 : (criticalPoint d : ℝ) < 1)
    (pioneers : HalfSpacePioneerExponentialInput i B b)
    (ordinary : OrdinaryArmWindowInput d Co)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hθ : UpperPowerBound (criticalPoint d : ℝ) (densityReal d) 1)
    (hbudget : ∃ p1 a C : ℝ, (criticalPoint d : ℝ) < p1 ∧ p1 ≤ 1 ∧ 0 < a ∧ 0 < C ∧
      ∀ p : unitInterval, criticalPoint d < p → (p : ℝ) ≤ p1 →
        ∃ t r : ℕ, 1 ≤ t ∧
          ∀ᶠ M : ℕ in atTop, Section10.cubeFlowBudget p i (chemicalCoarseRadius M t r) a C) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ p : ℝ, (criticalPoint d : ℝ) < p → p ≤ 1 →
      c * (p - (criticalPoint d : ℝ)) ^ 2 ≤ einsteinDiffusivity d i p ∧
        einsteinDiffusivity d i p ≤ C * (p - (criticalPoint d : ℝ)) ^ 2 :=
  einsteinDiffusivity_two_sided i hB hb hCo hpc1 pioneers ordinary δ hδ hδ1
    (fullCubeLimit_lowerPowerBound_of_near_flowBudgets i hbudget) hθ

end
end NearCritical
