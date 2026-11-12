import NearCritical.DiffusivityFromCoupledBudgets
import NearCritical.Section10TranslatedCoupledBudget
import NearCritical.ConductivityPermutation

/-!
`thm.main` for the Einstein-relation diffusivity from coupled flow budgets on
TRANSLATED cubes along a FIXED axis (the symmetry adapter).

The Section 10 construction produces, for `p = p0 OR q` near `p_c`, a budget
`Section10.translatedCoupledCubeFlowBudget p0 q aC i0 R a C` in the box
`translateSites aC (centeredBox d R)` along the axis `i0` of the layout
(`i0 = 0` for `actualLayout`), with `aC` free to depend on everything.

* `fullCubeLimit_lowerPowerBound_of_near_translatedBudgets`: such budgets on a
  window `(p_c, p_1]`, eventually along the affine source radii, give
  `LowerPowerBound p_c (fullCubeLimit d i) 3` for EVERY axis `i`
  (translation: `annealedFull_translation`; axis:
  `annealedFull_centeredBox_axis`).
* `einsteinDiffusivity_two_sided_of_near_translatedBudgets`: with the cited
  inputs, the two-sided bound of `thm.main` on `(p_c, 1]` for every axis.

The budgets themselves (source `prop.nw.main`) are OPEN.
-/

namespace NearCritical
noncomputable section
open MeasureTheory Filter
open scoped Classical

theorem fullCubeLimit_lowerPowerBound_of_near_translatedBudgets {d : ℕ} (i i0 : Fin d)
    (hbudget : ∃ p1 a C : ℝ, (criticalPoint d : ℝ) < p1 ∧ p1 ≤ 1 ∧ 0 < a ∧ 0 < C ∧
      ∀ p : unitInterval, criticalPoint d < p → (p : ℝ) ≤ p1 →
        ∃ p0 q : unitInterval, orParameter p0 q = p ∧ ∃ t r : ℕ, 1 ≤ t ∧
          ∀ᶠ M : ℕ in atTop, ∃ aC : Vertex d,
            Section10.translatedCoupledCubeFlowBudget p0 q aC i0
              (chemicalCoarseRadius M t r) a C) :
    LowerPowerBound (criticalPoint d : ℝ) (fullCubeLimit d i) 3 := by
  obtain ⟨p1, a, C, hp1, hp1', ha, hC, hbud⟩ := hbudget
  refine fullCubeLimit_lowerPowerBound_of_near i hp1 hp1' (c := a ^ 2 / C) (by positivity) ?_
  intro p hp hple
  have hp0 : 0 ≤ p := le_trans (criticalPoint d).2.1 hp.le
  obtain ⟨p0, q, hpq, t, r, ht, hev⟩ :=
    hbud ⟨p, hp0, hple.trans hp1'⟩ (Subtype.coe_lt_coe.mp hp) hple
  have hcrit : criticalPoint d < orParameter p0 q := by
    rw [hpq]
    exact Subtype.coe_lt_coe.mp hp
  have hmean := (Section10.annealedFull_centeredBox_tendsto i
    (triadicDirichletLimitInput_fullCubeLimit d i) (orParameter p0 q) hcrit).comp
    (Section10.chemicalCoarseRadius_tendsto ht r)
  have hfin : (a^2/C) * (((orParameter p0 q : unitInterval) : ℝ) - (criticalPoint d : ℝ))^3 ≤
      fullCubeLimit d i ((orParameter p0 q : unitInterval) : ℝ) :=
    ge_of_tendsto hmean (hev.mono (fun M hM => by
      obtain ⟨aC, hM⟩ := hM
      have h := Section10.annealed_cube_cubic_lower_of_translatedBudget p0 q aC i0 hcrit _ ha hC hM
      rw [annealedFull_centeredBox_axis _ i0 i] at h
      exact h))
  rw [hpq] at hfin
  exact hfin

/-- **`thm.main` (Einstein-relation diffusivity) from near-critical coupled flow
budgets on translated cubes along one axis, and cited inputs.** -/
theorem einsteinDiffusivity_two_sided_of_near_translatedBudgets {d : ℕ} (i i0 : Fin d)
    {B b Co : ℝ} (hB : 0 < B) (hb : 0 < b) (hCo : 0 ≤ Co)
    (hpc1 : (criticalPoint d : ℝ) < 1)
    (pioneers : HalfSpacePioneerExponentialInput i B b)
    (ordinary : OrdinaryArmWindowInput d Co)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hθ : UpperPowerBound (criticalPoint d : ℝ) (densityReal d) 1)
    (hbudget : ∃ p1 a C : ℝ, (criticalPoint d : ℝ) < p1 ∧ p1 ≤ 1 ∧ 0 < a ∧ 0 < C ∧
      ∀ p : unitInterval, criticalPoint d < p → (p : ℝ) ≤ p1 →
        ∃ p0 q : unitInterval, orParameter p0 q = p ∧ ∃ t r : ℕ, 1 ≤ t ∧
          ∀ᶠ M : ℕ in atTop, ∃ aC : Vertex d,
            Section10.translatedCoupledCubeFlowBudget p0 q aC i0
              (chemicalCoarseRadius M t r) a C) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ p : ℝ, (criticalPoint d : ℝ) < p → p ≤ 1 →
      c * (p - (criticalPoint d : ℝ)) ^ 2 ≤ einsteinDiffusivity d i p ∧
        einsteinDiffusivity d i p ≤ C * (p - (criticalPoint d : ℝ)) ^ 2 :=
  einsteinDiffusivity_two_sided i hB hb hCo hpc1 pioneers ordinary δ hδ hδ1
    (fullCubeLimit_lowerPowerBound_of_near_translatedBudgets i i0 hbudget) hθ

end
end NearCritical
