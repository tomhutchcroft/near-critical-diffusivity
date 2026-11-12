import NearCritical.DiffusivityEinsteinLower
import NearCritical.DiffusivityLowerExtension
import NearCritical.Section10AllRadiusLimit
import NearCritical.Section10CoupledCubic

/-!
`thm.main` for the Einstein-relation diffusivity from flow budgets on the
COUPLED law, on a near-critical window.

The Section 10 construction lives on the pair (critical layer, sprinkle): its
flow and its good event depend on both layers, while `cubeFlowBudget` asks for
a flow depending on the OR-configuration only. `coupledCubeFlowBudget` is the
two-layer budget, exactly the hypothesis list of
`annealed_cube_cubic_lower_coupled`:

* a finite set `R` of layered bonds and a map `orb` recovering the issued bonds
  of the OR-configuration from the layered bits;
* for every bit pattern in `A`, a unit flow across the box supported on open
  bonds of the OR-configuration;
* `P[A] >= a` and `E[energy; A] <= C * normalization * l_*(p)^6`
  under the product law.

`einsteinDiffusivity_two_sided_of_near_coupledBudgets`: cited inputs plus such
budgets for every `p = p0 OR q` in a window `(p_c, p_1]`, eventually along the
affine source radii, give the two-sided bound of `thm.main` on `(p_c, 1]`.
No passage from the coupled flow to a single-layer flow is needed.

The budgets themselves (source `prop.nw.main`) are OPEN.
-/

namespace NearCritical
noncomputable section
open MeasureTheory Filter
open scoped Classical

namespace Section10

/-- Flow budget on the coupled law (source `eq.lowerObject`). -/
def coupledCubeFlowBudget {d : ℕ} (p0 q : unitInterval) (i : Fin d) (r : ℕ) (a C : ℝ) : Prop :=
  ∃ (R : Finset (LBond d))
    (orb : (R → Bool) → IssuedBond (centeredBox d r) → Bool)
    (θ : (R → Bool) → IssuedBond (centeredBox d r) → ℝ) (A : Set (R → Bool)),
    (∀ z : Configuration d × Configuration d, orb (R.restrict (layerVal z)) =
      (issuedBondSet (centeredBox d r)).restrict (sprinkleOrConfiguration z.1 z.2)) ∧
    (∀ b ∈ A, Network.FlowSupported (cubeFlowWeights (orb b)) (θ b) ∧
      (issuedNetwork (centeredBox d r)).IsBoundaryUnitFlow
        (negativeFace (centeredBox d r) i) (positiveFace (centeredBox d r) i) (θ b)) ∧
    a ≤ (∫ z : Configuration d × Configuration d,
      (if R.restrict (layerVal z) ∈ A then (1:ℝ) else 0)
        ∂((percolation d p0).prod (percolation d q))) ∧
    (∫ z : Configuration d × Configuration d,
      (if R.restrict (layerVal z) ∈ A then
        Network.flowEnergy (cubeFlowWeights (orb (R.restrict (layerVal z))))
          (θ (R.restrict (layerVal z))) else 0)
        ∂((percolation d p0).prod (percolation d q))) ≤
      C * cubeFlowNormalization d r *
        (chemicalCorrelationScale d (orParameter p0 q) : ℝ) ^ 6

theorem annealed_cube_cubic_lower_of_coupledBudget {d : ℕ} (p0 q : unitInterval) (i : Fin d)
    (hp : criticalPoint d < orParameter p0 q) (r : ℕ) {a C : ℝ} (ha : 0 < a) (hC : 0 < C)
    (hbudget : coupledCubeFlowBudget p0 q i r a C) :
    (a^2/C) * (((orParameter p0 q : unitInterval) : ℝ) - (criticalPoint d : ℝ))^3 ≤
      annealedFull (centeredBox d r) i ((orParameter p0 q : unitInterval) : ℝ) := by
  obtain ⟨R, orb, θ, A, horb, hflow, hA, henergy⟩ := hbudget
  exact annealed_cube_cubic_lower_coupled i p0 q hp ha hC R orb horb θ A hflow hA henergy

end Section10

theorem fullCubeLimit_lowerPowerBound_of_near_coupledBudgets {d : ℕ} (i : Fin d)
    (hbudget : ∃ p1 a C : ℝ, (criticalPoint d : ℝ) < p1 ∧ p1 ≤ 1 ∧ 0 < a ∧ 0 < C ∧
      ∀ p : unitInterval, criticalPoint d < p → (p : ℝ) ≤ p1 →
        ∃ p0 q : unitInterval, orParameter p0 q = p ∧ ∃ t r : ℕ, 1 ≤ t ∧
          ∀ᶠ M : ℕ in atTop,
            Section10.coupledCubeFlowBudget p0 q i (chemicalCoarseRadius M t r) a C) :
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
    ge_of_tendsto hmean (hev.mono (fun M hM =>
      Section10.annealed_cube_cubic_lower_of_coupledBudget p0 q i hcrit _ ha hC hM))
  rw [hpq] at hfin
  exact hfin

/-- **`thm.main` (Einstein-relation diffusivity) from near-critical flow
budgets on the coupled law and cited inputs.** -/
theorem einsteinDiffusivity_two_sided_of_near_coupledBudgets {d : ℕ} (i : Fin d) {B b Co : ℝ}
    (hB : 0 < B) (hb : 0 < b) (hCo : 0 ≤ Co)
    (hpc1 : (criticalPoint d : ℝ) < 1)
    (pioneers : HalfSpacePioneerExponentialInput i B b)
    (ordinary : OrdinaryArmWindowInput d Co)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hθ : UpperPowerBound (criticalPoint d : ℝ) (densityReal d) 1)
    (hbudget : ∃ p1 a C : ℝ, (criticalPoint d : ℝ) < p1 ∧ p1 ≤ 1 ∧ 0 < a ∧ 0 < C ∧
      ∀ p : unitInterval, criticalPoint d < p → (p : ℝ) ≤ p1 →
        ∃ p0 q : unitInterval, orParameter p0 q = p ∧ ∃ t r : ℕ, 1 ≤ t ∧
          ∀ᶠ M : ℕ in atTop,
            Section10.coupledCubeFlowBudget p0 q i (chemicalCoarseRadius M t r) a C) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ p : ℝ, (criticalPoint d : ℝ) < p → p ≤ 1 →
      c * (p - (criticalPoint d : ℝ)) ^ 2 ≤ einsteinDiffusivity d i p ∧
        einsteinDiffusivity d i p ≤ C * (p - (criticalPoint d : ℝ)) ^ 2 :=
  einsteinDiffusivity_two_sided i hB hb hCo hpc1 pioneers ordinary δ hδ hδ1
    (fullCubeLimit_lowerPowerBound_of_near_coupledBudgets i hbudget) hθ

end
end NearCritical
