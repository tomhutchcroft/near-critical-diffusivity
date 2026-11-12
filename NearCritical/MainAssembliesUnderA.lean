module

public import NearCritical.SlabUpperOneStepAssembly
public import NearCritical.DiffusivityTwoSided
public import NearCritical.DiffusivityCoefficientCubic
public import NearCritical.CriticalPointInterior

/-! Plumbing for the main-theorem assemblies: derive `0 < p_c < 1` from the paper's standing
assumption (A) (`TwoPointAsymptotics d`), instead of assuming it.

* `sigma_sq_two_sided_fullCubeLimit_of_A` (thm.main, two-sided). The homogenized coefficient
  is INSTANTIATED as the constructed `fullCubeLimit d i`, so `limitInput` is discharged by
  `triadicDirichletLimitInput_fullCubeLimit`. `hpc`/`hpc1` come from (A). Remaining explicit
  inputs: cited pioneer/ordinary-arm estimates, the cubic coefficient lower bound `hκlo`
  (Section 10 prop.lower; open), the density bounds `hθ` (barsky1991) and the Einstein
  identification `hEin` (lem.basic).
* `slab_theorem_of_oneStep_inputs_of_A` (thm.slab). `hpc`/`hpc1` come from (A). All other
  inputs of `slab_theorem_of_oneStep_inputs` remain.

Both statements are CONDITIONAL and are not proofs of the main theorems. Read-only imports.
 -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory unitInterval
open scoped ENNReal Classical BigOperators

/-- thm.main two-sided, with `κ = fullCubeLimit d i` and `0 < p_c < 1` from (A). -/
theorem sigma_sq_two_sided_fullCubeLimit_of_A {d : ℕ} (hd : 2 < d) (i : Fin d)
    (hA : TwoPointAsymptotics d)
    (density variance : ℝ → ℝ) {B b Co cκ : ℝ}
    (hB : 0 < B) (hb : 0 < b) (hCo : 0 ≤ Co)
    (pioneers : HalfSpacePioneerExponentialInput i B b)
    (ordinary : OrdinaryArmWindowInput d Co)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hcκ : 0 < cκ)
    (hκlo : ∀ p : ℝ, (criticalPoint d : ℝ) < p → p ≤ 1 →
      cκ * (p - (criticalPoint d : ℝ)) ^ 3 ≤ fullCubeLimit d i p)
    (hθ : UniformPowerBounds (criticalPoint d : ℝ) density 1)
    (hEin : ∀ p : ℝ, (criticalPoint d : ℝ) < p → p ≤ 1 →
      variance p / 2 = fullCubeLimit d i p / density p) :
    UniformPowerBounds (criticalPoint d : ℝ) variance 2 := by
  obtain ⟨hpc, hpc1⟩ := criticalPoint_interior_of_twoPointAsymptotics hd i hA
  exact sigma_sq_two_sided_of_standard_inputs i (fullCubeLimit d i) density variance hB hb hCo
    hpc hpc1 pioneers ordinary δ hδ hδ1 (triadicDirichletLimitInput_fullCubeLimit d i) hcκ hκlo
    hθ hEin

/-- thm.slab with `0 < p_c < 1` from (A). -/
theorem slab_theorem_of_oneStep_inputs_of_A {d : ℕ} (hd : 3 ≤ d)
    (hA : TwoPointAsymptotics d)
    {C c : ℝ} (hC : 0 < C) (hc : 0 < c)
    (decay : WeightedPositiveHeightPioneerDecay (criticalPoint d)
      (⟨d-1, by omega⟩ : Fin d) C c)
    {lam : ℝ} (hlam : 0 < lam) (n₀ : ℕ)
    (κ : Measure Bool) [IsProbabilityMeasure κ] {θ : ℝ≥0∞} (hθ0 : θ ≠ 0)
    (hθ : MixedSiteBondPercolationInput 2 κ θ)
    (hmodel : ∀ n : ℕ, n₀ ≤ n → 1 ≤ n → ∀ p : I,
      (p : ℝ) = (criticalPoint d : ℝ) + lam / (n : ℝ) ^ 2 →
        ∃ s : I, orParameter (criticalPoint d) s = p ∧ ∃ F : Finset (Vertex d),
          ∀ R, Nonempty (SlabOneStepInputs d n R (criticalPoint d) s (slabVertices d 2 n) F κ)) :
    ∃ a A : ℝ, 0 < a ∧ ∀ n : ℕ, 1 ≤ n →
      a / (n : ℝ) ^ 2 ≤
          (restrictedCriticalPoint d (slabVertices d (d-1) n) : ℝ) - criticalPoint d ∧
        (restrictedCriticalPoint d (slabVertices d (d-1) n) : ℝ) - criticalPoint d ≤
          (restrictedCriticalPoint d (slabVertices d 2 n) : ℝ) - criticalPoint d ∧
        (restrictedCriticalPoint d (slabVertices d 2 n) : ℝ) - criticalPoint d ≤
          A / (n : ℝ) ^ 2 := by
  obtain ⟨hpc, hpc1⟩ :=
    criticalPoint_interior_of_twoPointAsymptotics (by omega) (⟨0, by omega⟩ : Fin d) hA
  exact slab_theorem_of_oneStep_inputs hd hC hc hpc hpc1 decay hlam n₀ κ hθ0 hθ hmodel

end NearCritical
