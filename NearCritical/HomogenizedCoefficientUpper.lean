module

public import NearCritical.TriadicLimitExistence
public import NearCritical.MaskedHomogenizedCubicUpper

/-! The no-log conductivity upper bound for the CONSTRUCTED homogenized
coefficient `fullCubeLimit d i`, with the triadic convergence input discharged by
`triadicDirichletLimitInput_fullCubeLimit`. Remaining inputs are the cited
pioneer/ordinary-arm estimates and `0 < p_c < 1`. -/

@[expose] public section
noncomputable section

namespace NearCritical

theorem fullCubeLimit_cubic_upper_of_standard_inputs {d : ℕ} (i : Fin d)
    {B b Co : ℝ} (hB : 0 < B) (hb : 0 < b) (hCo : 0 ≤ Co)
    (hpc : 0 < (criticalPoint d : ℝ)) (hpc1 : (criticalPoint d : ℝ) < 1)
    (pioneers : HalfSpacePioneerExponentialInput i B b)
    (ordinary : OrdinaryArmWindowInput d Co)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ p : unitInterval, criticalPoint d < p →
      fullCubeLimit d i (p : ℝ) ≤ C * ((p : ℝ) - (criticalPoint d : ℝ)) ^ 3 :=
  homogenized_global_cubic_upper_of_standard_inputs i (fullCubeLimit d i) hB hb hCo hpc hpc1
    pioneers ordinary δ hδ hδ1 (triadicDirichletLimitInput_fullCubeLimit d i)

end NearCritical
