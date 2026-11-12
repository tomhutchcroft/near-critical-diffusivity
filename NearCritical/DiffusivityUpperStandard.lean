module

public import NearCritical.DiffusivityUpper
public import NearCritical.HomogenizedGlobalLogUpper

/-! Complete standard-inputs → diffusivity-upper chain.

Instantiates the scalar reduction `sigma_sq_upper_of_conductivity_log`
(`DiffusivityUpper.lean`) with the frozen homogenized conductivity log bound
`homogenized_global_log_upper_of_standard_inputs` (`HomogenizedGlobalLogUpper.lean`),
giving the diffusivity upper bound up to the logarithm directly from the named
standard inputs plus the density-lower and Einstein hypotheses. Kept in its own
leaf so `DiffusivityUpper.lean` keeps its narrow (Mathlib-only) imports.
 -/
@[expose] public section
noncomputable section
namespace NearCritical
open scoped BigOperators

/-- `σ²(p) ≤ D'·(p-pc)²·|log(p-pc)|` on `(pc, 1]`, from the named standard arm /
pioneer / entropic / triadic-limit inputs (via the frozen conductivity log bound),
a linear density lower bound (`barsky1991`), and the Einstein identity
(`lem.basic`). -/
theorem sigma_sq_upper_log_of_standard_inputs {d : ℕ} (i : Fin d)
    (κ density variance : ℝ → ℝ) {C G β E A B b cθ : ℝ}
    (hC : 1 ≤ C) (hG : 0 ≤ G) (hβ : 0 < β) (hEent : 0 < E) (hA : 0 < A) (hB : 0 < B) (hb : 0 < b)
    (hpc : 0 < (criticalPoint d : ℝ)) (hpc1 : (criticalPoint d : ℝ) < 1)
    (ordinary : OrdinaryArmWindowInput d C)
    (subordinary : OrdinaryArmSubcriticalInput d G β)
    (criticalArm : HalfSpaceCriticalArmInput i A)
    (pioneers : HalfSpacePioneerExponentialInput i B b)
    (entropic : FiniteHalfSpaceEntropicInput i E)
    (limitInput : TriadicDirichletLimitInput d i κ)
    (hcθ : 0 < cθ)
    (hκ0 : ∀ p : ℝ, (criticalPoint d : ℝ) < p → p ≤ 1 → 0 ≤ κ p)
    (hθlo : ∀ p : ℝ, (criticalPoint d : ℝ) < p → p ≤ 1 →
      cθ * (p - (criticalPoint d : ℝ)) ≤ density p)
    (hEin : ∀ p : ℝ, (criticalPoint d : ℝ) < p → p ≤ 1 →
      variance p / 2 = κ p / density p) :
    ∃ D' : ℝ, 0 < D' ∧ ∀ p : ℝ, (criticalPoint d : ℝ) < p → p ≤ 1 →
      variance p ≤ D' * (p - (criticalPoint d : ℝ)) ^ 2 * |Real.log (p - (criticalPoint d : ℝ))| := by
  refine sigma_sq_upper_of_conductivity_log (pc := (criticalPoint d : ℝ)) hcθ ?_ hκ0 hθlo hEin
  obtain ⟨D, hD, hκ⟩ := homogenized_global_log_upper_of_standard_inputs i κ hC hG hβ hEent hA hB hb
    hpc hpc1 ordinary subordinary criticalArm pioneers entropic limitInput
  refine ⟨D, hD, ?_⟩
  intro p hp hp1
  have hmem : p ∈ Set.Icc (0 : ℝ) 1 := ⟨le_of_lt (lt_trans hpc hp), hp1⟩
  have hqlt : criticalPoint d < (⟨p, hmem⟩ : unitInterval) := Subtype.coe_lt_coe.mp hp
  exact hκ ⟨p, hmem⟩ hqlt

end NearCritical
