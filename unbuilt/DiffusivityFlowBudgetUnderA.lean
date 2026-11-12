module

public import NearCritical.MainAssembliesUnderA
public import NearCritical.Section10AllRadiusLimit

/-! thm.main (two-sided diffusivity) with the cubic coefficient lower bound `hκlo` replaced by its
actual Section-10 source object: eventual flow budgets `cubeFlowBudget` on the affine source
radii, with constants `a, C` UNIFORM in `p`. The scale parameters `t, r` may depend on `p`.
`hκlo` is derived via the verified `coefficient_cubic_lower_of_triadic_affine_budgets` with
`κ := fullCubeLimit` and `c_κ = a²/C`.

The remaining explicit inputs are:
* (A) (`TwoPointAsymptotics`);
* the cited pioneer and ordinary-arm estimates;
* `hθ` (barsky1991) and `hEin` (lem.basic), both registered cited inputs;
* `hbudget`, the source prop.lower flow construction, which is OPEN in Lean.
CONDITIONAL; not a proof of thm.main. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory Filter
open scoped BigOperators

theorem sigma_sq_two_sided_of_flowBudgets_of_A {d : ℕ} (hd : 2 < d) (i : Fin d)
    (hA : TwoPointAsymptotics d)
    (density variance : ℝ → ℝ) {B b Co : ℝ}
    (hB : 0 < B) (hb : 0 < b) (hCo : 0 ≤ Co)
    (pioneers : HalfSpacePioneerExponentialInput i B b)
    (ordinary : OrdinaryArmWindowInput d Co)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hbudget : ∃ a C : ℝ, 0 < a ∧ 0 < C ∧ ∀ p : unitInterval, criticalPoint d < p →
      ∃ t r : ℕ, 1 ≤ t ∧
        ∀ᶠ M : ℕ in atTop, Section10.cubeFlowBudget p i (chemicalCoarseRadius M t r) a C)
    (hθ : UniformPowerBounds (criticalPoint d : ℝ) density 1)
    (hEin : ∀ p : ℝ, (criticalPoint d : ℝ) < p → p ≤ 1 →
      variance p / 2 = fullCubeLimit d i p / density p) :
    UniformPowerBounds (criticalPoint d : ℝ) variance 2 := by
  obtain ⟨a, C, ha, hC, hbud⟩ := hbudget
  refine sigma_sq_two_sided_fullCubeLimit_of_A hd i hA density variance hB hb hCo pioneers
    ordinary δ hδ hδ1 (cκ := a ^ 2 / C) (by positivity) ?_ hθ hEin
  intro p hp hp1
  have hp0 : 0 ≤ p := le_trans (criticalPoint d).2.1 hp.le
  let q : unitInterval := ⟨p, hp0, hp1⟩
  have hq : criticalPoint d < q := Subtype.coe_lt_coe.mp hp
  obtain ⟨t, r, ht, hev⟩ := hbud q hq
  exact Section10.coefficient_cubic_lower_of_triadic_affine_budgets i
    (triadicDirichletLimitInput_fullCubeLimit d i) q hq ht r ha hC hev

end NearCritical
