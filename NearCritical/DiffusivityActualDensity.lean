import NearCritical.DiffusivityCoefficientCubic
import NearCritical.ExternalCriticalPointPos

/-!
The diffusivity upper bound of `thm.main` with the ACTUAL percolation density.

`sigma_sq_upper_cubic_fullCubeLimit` takes the density as a free function with
an assumed mean-field lower bound, and assumes `0 < p_c`. Both are now theorems
(`External.density_lower_real`, `External.criticalPoint_pos`), so the bound can
be stated for `theta(p) = density d p` itself.

* `sigma_sq_upper_cubic_actual_density`: for any `variance` satisfying the
  Einstein identity `sigma^2/2 = kappa/theta` with the constructed coefficient
  `kappa = fullCubeLimit d i` and the actual density, `sigma^2 <= C (p-p_c)^2`.
* `einsteinDiffusivity d i p := 2 kappa(p) / theta(p)` is the diffusivity given
  by the Einstein relation; for it the identity holds by definition and the
  bound has no density or Einstein hypothesis at all.

Remaining inputs: the cited half-space pioneer and ordinary one-arm estimates
and `p_c < 1`. The identification of `einsteinDiffusivity` with the variance
of the random walk on the infinite cluster is source `lem.basic` (cited) and is
NOT formalized: there is no random walk in the library.

-/

namespace NearCritical
noncomputable section

/-- The actual density read on real parameters (clamped to `[0,1]`). -/
def densityReal (d : ℕ) (p : ℝ) : ℝ := density d (Set.projIcc 0 1 zero_le_one p)

/-- The diffusivity defined by the Einstein relation from the constructed
homogenized coefficient and the actual density. -/
def einsteinDiffusivity (d : ℕ) (i : Fin d) (p : ℝ) : ℝ :=
  2 * fullCubeLimit d i p / densityReal d p

/-- Diffusivity upper bound with the actual density: no density hypothesis and
no `0 < p_c` hypothesis. -/
theorem sigma_sq_upper_cubic_actual_density {d : ℕ} (i : Fin d)
    (variance : ℝ → ℝ) {B b Co : ℝ}
    (hB : 0 < B) (hb : 0 < b) (hCo : 0 ≤ Co)
    (hpc1 : (criticalPoint d : ℝ) < 1)
    (pioneers : HalfSpacePioneerExponentialInput i B b)
    (ordinary : OrdinaryArmWindowInput d Co)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hEin : ∀ p : ℝ, (criticalPoint d : ℝ) < p → p ≤ 1 →
      variance p / 2 = fullCubeLimit d i p / densityReal d p) :
    UpperPowerBound (criticalPoint d : ℝ) variance 2 :=
  sigma_sq_upper_cubic_fullCubeLimit i (densityReal d) variance hB hb hCo
    (External.criticalPoint_pos (Fin.pos i)) hpc1 pioneers ordinary δ hδ hδ1 one_pos
    (External.density_lower_real d) hEin

/-- **Upper bound of `thm.main` for the Einstein-relation diffusivity**:
`2 kappa(p)/theta(p) <= C (p - p_c)^2` on `(p_c, 1]`, from the cited pioneer
and one-arm inputs and `p_c < 1` only. -/
theorem einsteinDiffusivity_upper {d : ℕ} (i : Fin d) {B b Co : ℝ}
    (hB : 0 < B) (hb : 0 < b) (hCo : 0 ≤ Co)
    (hpc1 : (criticalPoint d : ℝ) < 1)
    (pioneers : HalfSpacePioneerExponentialInput i B b)
    (ordinary : OrdinaryArmWindowInput d Co)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    UpperPowerBound (criticalPoint d : ℝ) (einsteinDiffusivity d i) 2 :=
  sigma_sq_upper_cubic_actual_density i (einsteinDiffusivity d i) hB hb hCo hpc1
    pioneers ordinary δ hδ hδ1 (fun p _ _ => by
      unfold einsteinDiffusivity
      ring)

end
end NearCritical
