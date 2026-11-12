module

public import NearCritical.DiffusivityUpper
public import NearCritical.MaskedHomogenizedCubicUpper

/-! Sharp (no-log) standard-inputs → diffusivity-upper chain.

Instantiates `uniform_einstein_upper` (`DiffusivityUpper.lean`) with the compiled
NO-LOG homogenized conductivity bound `homogenized_global_cubic_upper_of_standard_inputs`
(`MaskedHomogenizedCubicUpper.lean`, `κ ≤ C·(p-pc)³`), giving the sharp diffusivity
upper bound `σ²(p) ≤ C'·(p-pc)²` on `(pc,1]` from the named standard inputs plus
the density-lower and Einstein hypotheses. Companion to the up-to-log
`sigma_sq_upper_log_of_standard_inputs`. -/
@[expose] public section
noncomputable section
namespace NearCritical
open scoped BigOperators

/-- Sharp diffusivity upper bound `UpperPowerBound pc σ² 2` (i.e. `σ²(p) ≤ C'(p-pc)²`
on `(pc,1]`), from the no-log conductivity bound + a linear density lower bound
(`barsky1991`) + the Einstein identity (`lem.basic`). -/
theorem sigma_sq_upper_cubic_of_standard_inputs {d : ℕ} (i : Fin d)
    (κ density variance : ℝ → ℝ) {B b Co cθ : ℝ}
    (hB : 0 < B) (hb : 0 < b) (hCo : 0 ≤ Co)
    (hpc : 0 < (criticalPoint d : ℝ)) (hpc1 : (criticalPoint d : ℝ) < 1)
    (pioneers : HalfSpacePioneerExponentialInput i B b)
    (ordinary : OrdinaryArmWindowInput d Co)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (limitInput : TriadicDirichletLimitInput d i κ)
    (hcθ : 0 < cθ)
    (hκ0 : ∀ p : ℝ, (criticalPoint d : ℝ) < p → p ≤ 1 → 0 ≤ κ p)
    (hθlo : ∀ p : ℝ, (criticalPoint d : ℝ) < p → p ≤ 1 →
      cθ * (p - (criticalPoint d : ℝ)) ≤ density p)
    (hEin : ∀ p : ℝ, (criticalPoint d : ℝ) < p → p ≤ 1 →
      variance p / 2 = κ p / density p) :
    UpperPowerBound (criticalPoint d : ℝ) variance 2 := by
  refine uniform_einstein_upper ?_ hκ0 ?_ hEin
  · obtain ⟨C, hC, hκ⟩ := homogenized_global_cubic_upper_of_standard_inputs i κ hB hb hCo
      hpc hpc1 pioneers ordinary δ hδ hδ1 limitInput
    refine ⟨C, hC, fun p hp hp1 => ?_⟩
    have hmem : p ∈ Set.Icc (0 : ℝ) 1 := ⟨le_of_lt (lt_trans hpc hp), hp1⟩
    exact hκ ⟨p, hmem⟩ (Subtype.coe_lt_coe.mp hp)
  · exact ⟨cθ, hcθ, fun p hp hp1 => by simpa using hθlo p hp hp1⟩

end NearCritical
