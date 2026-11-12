module

public import NearCritical.DiffusivityUpperCubic
public import NearCritical.TriadicLimitExistence

/-! The no-log diffusivity upper bound with the homogenized coefficient
INSTANTIATED as the constructed `fullCubeLimit d i`: the triadic convergence
input and coefficient nonnegativity are proved, not assumed. Remaining inputs:
cited pioneer/ordinary-arm estimates, `0 < p_c < 1`, the density lower bound
(barsky1991) and the Einstein identification `σ²/2 = κ/θ` (lem.basic). -/

@[expose] public section
noncomputable section

namespace NearCritical

lemma fullCubeLimit_nonneg {d : ℕ} (i : Fin d) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    0 ≤ fullCubeLimit d i p :=
  le_ciInf fun _ => annealedFull_nonneg _ i hp0 hp1

theorem sigma_sq_upper_cubic_fullCubeLimit {d : ℕ} (i : Fin d)
    (density variance : ℝ → ℝ) {B b Co cθ : ℝ}
    (hB : 0 < B) (hb : 0 < b) (hCo : 0 ≤ Co)
    (hpc : 0 < (criticalPoint d : ℝ)) (hpc1 : (criticalPoint d : ℝ) < 1)
    (pioneers : HalfSpacePioneerExponentialInput i B b)
    (ordinary : OrdinaryArmWindowInput d Co)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hcθ : 0 < cθ)
    (hθlo : ∀ p : ℝ, (criticalPoint d : ℝ) < p → p ≤ 1 →
      cθ * (p - (criticalPoint d : ℝ)) ≤ density p)
    (hEin : ∀ p : ℝ, (criticalPoint d : ℝ) < p → p ≤ 1 →
      variance p / 2 = fullCubeLimit d i p / density p) :
    UpperPowerBound (criticalPoint d : ℝ) variance 2 :=
  sigma_sq_upper_cubic_of_standard_inputs i (fullCubeLimit d i) density variance hB hb hCo
    hpc hpc1 pioneers ordinary δ hδ hδ1 (triadicDirichletLimitInput_fullCubeLimit d i) hcθ
    (fun p hp hp1 => fullCubeLimit_nonneg i (le_of_lt (lt_of_le_of_lt (criticalPoint d).2.1 hp)) hp1)
    hθlo hEin

end NearCritical
