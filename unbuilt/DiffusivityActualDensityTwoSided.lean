module

public import NearCritical.DiffusivityFlowBudgetUnderA
public import NearCritical.ExternalMeanField

/-! thm.main (two-sided diffusivity) with the density instantiated as the project's ACTUAL
`density d`, extended to ℝ by `Set.projIcc`. The LOWER density bound `θ(p) ≥ p - p_c` is no longer
an input: it is the verified mean-field `density_lower_real` (Duminil-Copin–Tassion via
the model-law bridge). Only the UPPER half `θ(p) ≤ C(p - p_c)` remains a cited input
(Barsky–Aizenman / barsky1991).

Remaining explicit inputs are:
* (A);
* the cited pioneer and ordinary-arm estimates;
* the Section-10 flow budgets `hbudget` (prop.lower, OPEN);
* the cited density upper bound `hθup`;
* the Einstein identification `hEin` for the actual density (lem.basic; Dario–Gu).
CONDITIONAL; not a proof of thm.main. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory Filter
open scoped BigOperators

/-- The actual density, extended to all real `p`. -/
def actualDensityReal (d : ℕ) (p : ℝ) : ℝ := density d (Set.projIcc 0 1 zero_le_one p)

theorem sigma_sq_two_sided_actual_density_of_A {d : ℕ} (hd : 2 < d) (i : Fin d)
    (hA : TwoPointAsymptotics d)
    (variance : ℝ → ℝ) {B b Co : ℝ}
    (hB : 0 < B) (hb : 0 < b) (hCo : 0 ≤ Co)
    (pioneers : HalfSpacePioneerExponentialInput i B b)
    (ordinary : OrdinaryArmWindowInput d Co)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hbudget : ∃ a C : ℝ, 0 < a ∧ 0 < C ∧ ∀ p : unitInterval, criticalPoint d < p →
      ∃ t r : ℕ, 1 ≤ t ∧
        ∀ᶠ M : ℕ in atTop, Section10.cubeFlowBudget p i (chemicalCoarseRadius M t r) a C)
    (hθup : ∃ Cθ : ℝ, 0 < Cθ ∧ ∀ p : ℝ, (criticalPoint d : ℝ) < p → p ≤ 1 →
      actualDensityReal d p ≤ Cθ * (p - (criticalPoint d : ℝ)))
    (hEin : ∀ p : ℝ, (criticalPoint d : ℝ) < p → p ≤ 1 →
      variance p / 2 = fullCubeLimit d i p / actualDensityReal d p) :
    UniformPowerBounds (criticalPoint d : ℝ) variance 2 := by
  obtain ⟨Cθ, hCθ, hup⟩ := hθup
  have hθ : UniformPowerBounds (criticalPoint d : ℝ) (actualDensityReal d) 1 := by
    refine ⟨1, one_pos, Cθ, hCθ, fun p hp hp1 => ⟨?_, ?_⟩⟩
    · rw [pow_one]
      exact External.density_lower_real d p hp hp1
    · rw [pow_one]
      exact hup p hp hp1
  exact sigma_sq_two_sided_of_flowBudgets_of_A hd i hA (actualDensityReal d) variance hB hb hCo
    pioneers ordinary δ hδ hδ1 hbudget hθ hEin

end NearCritical
