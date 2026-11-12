module

public import NearCritical.DiffusivityUpperCubic
public import NearCritical.Einstein

/-! Two-sided diffusivity bound `σ²(p) ≍ (p-pc)²` (the diffusivity exponent = 2),
reduced to its remaining percolation input.

Combines the NO-LOG homogenized conductivity UPPER bound (mine, via
`homogenized_global_cubic_upper_of_standard_inputs`) with a conductivity LOWER
bound `cκ·(p-pc)³ ≤ κ(p)` — the output of the Section-10 lower branch
(`prop.lower`) — to form the two-sided `UniformPowerBounds κ 3`,
then applies the existing two-sided `uniform_einstein_bounds` (`Einstein.lean`)
with a two-sided density bound (`barsky1991`) and the Einstein identity
(`lem.basic`). Result: `UniformPowerBounds σ² 2`, i.e. `c·(p-pc)² ≤ σ²(p) ≤
C·(p-pc)²` on `(pc,1]`.

The ONLY genuinely-open percolation input isolated here is `hκlo` (the
conductivity lower bound = `prop.lower`); everything else is the named standard
literature set already used by the upper branch. -/
@[expose] public section
noncomputable section
namespace NearCritical
open scoped BigOperators

/-- Two-sided diffusivity bound from the conductivity lower bound (`prop.lower`)
plus the named standard inputs already driving the upper branch. -/
theorem sigma_sq_two_sided_of_standard_inputs {d : ℕ} (i : Fin d)
    (κ density variance : ℝ → ℝ) {B b Co cκ : ℝ}
    (hB : 0 < B) (hb : 0 < b) (hCo : 0 ≤ Co)
    (hpc : 0 < (criticalPoint d : ℝ)) (hpc1 : (criticalPoint d : ℝ) < 1)
    (pioneers : HalfSpacePioneerExponentialInput i B b)
    (ordinary : OrdinaryArmWindowInput d Co)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (limitInput : TriadicDirichletLimitInput d i κ)
    (hcκ : 0 < cκ)
    (hκlo : ∀ p : ℝ, (criticalPoint d : ℝ) < p → p ≤ 1 →
      cκ * (p - (criticalPoint d : ℝ)) ^ 3 ≤ κ p)
    (hθ : UniformPowerBounds (criticalPoint d : ℝ) density 1)
    (hEin : ∀ p : ℝ, (criticalPoint d : ℝ) < p → p ≤ 1 →
      variance p / 2 = κ p / density p) :
    UniformPowerBounds (criticalPoint d : ℝ) variance 2 := by
  obtain ⟨Cκ, hCκ, hκup⟩ := homogenized_global_cubic_upper_of_standard_inputs i κ hB hb hCo
    hpc hpc1 pioneers ordinary δ hδ hδ1 limitInput
  refine uniform_einstein_bounds (⟨cκ, hcκ, Cκ, hCκ, ?_⟩ :
    UniformPowerBounds (criticalPoint d : ℝ) κ 3) hθ hEin
  intro p hp hp1
  refine ⟨hκlo p hp hp1, ?_⟩
  have hmem : p ∈ Set.Icc (0 : ℝ) 1 := ⟨le_of_lt (lt_trans hpc hp), hp1⟩
  exact hκup ⟨p, hmem⟩ (Subtype.coe_lt_coe.mp hp)

end NearCritical
