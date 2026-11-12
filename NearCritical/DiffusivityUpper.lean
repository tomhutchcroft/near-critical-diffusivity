module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Tactic

/-! One-sided (upper) Einstein-relation algebra for the diffusivity upper bound.

`Einstein.lean` only provides the TWO-sided `einstein_bounds` / `uniform_einstein_bounds`,
which require a conductivity LOWER bound (to get `0 < conductivity`). The diffusivity
UPPER branch has no κ-lower bound, so a one-sided version is genuinely missing, not
redundant. This leaf supplies it and the `σ²`-from-`κ` reductions.

`variance` denotes σ² (not σ). The Einstein identity `σ²/2 = κ/θ`, the density lower
bound `θ ≳ (p-pc)`, and the conductivity upper bound are all EXPLICIT hypotheses
(literature inputs `lem.basic`/`eq.def_sigma`, `barsky1991percolation`); nothing
probabilistic is asserted here. -/
@[expose] public section

namespace NearCritical
open scoped BigOperators

/-- One-sided Einstein algebra: from `0 ≤ κ`, an arbitrary conductivity upper bound
`κ ≤ U`, a density lower bound `cθ·δ ≤ θ` with `cθ,δ > 0`, and `σ²/2 = κ/θ`, we get
`σ² ≤ 2U/(cθ·δ)`. (Taking `U = CA·δ³` or `U = D·δ³·|log δ|` gives the power / log
diffusivity upper bounds.) -/
theorem einstein_upper {δ conductivity density variance U cθ : ℝ}
    (hδ : 0 < δ) (hcθ : 0 < cθ) (hκ0 : 0 ≤ conductivity)
    (hAhi : conductivity ≤ U) (hθlo : cθ * δ ≤ density)
    (hEinstein : variance / 2 = conductivity / density) :
    variance ≤ 2 * U / (cθ * δ) := by
  have hθpos : 0 < density := lt_of_lt_of_le (mul_pos hcθ hδ) hθlo
  have hcθδ : 0 < cθ * δ := mul_pos hcθ hδ
  have hσ0 : 0 ≤ variance := by
    have h := div_nonneg hκ0 hθpos.le
    rw [← hEinstein] at h
    linarith
  have hid : variance * density = 2 * conductivity := by
    have := (div_eq_iff (ne_of_gt hθpos)).mp hEinstein.symm
    linarith
  rw [le_div_iff₀ hcθδ]
  have hstep : variance * (cθ * δ) ≤ variance * density :=
    mul_le_mul_of_nonneg_left hθlo hσ0
  linarith

/-- One-sided upper power bound on `(pc, 1]`, companion to `UniformPowerBounds`. -/
def UpperPowerBound (pc : ℝ) (f : ℝ → ℝ) (k : ℕ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ p : ℝ, pc < p → p ≤ 1 → f p ≤ C * (p - pc) ^ k

/-- One-sided lower power bound on `(pc, 1]`. -/
def LowerPowerBound (pc : ℝ) (f : ℝ → ℝ) (k : ℕ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ p : ℝ, pc < p → p ≤ 1 → c * (p - pc) ^ k ≤ f p

/-- Uniform one-sided Einstein upper bound: a cubic conductivity upper bound and a
linear density lower bound give a quadratic diffusivity upper bound. -/
theorem uniform_einstein_upper {pc : ℝ} {conductivity density variance : ℝ → ℝ}
    (hA : UpperPowerBound pc conductivity 3)
    (hAnn : ∀ p : ℝ, pc < p → p ≤ 1 → 0 ≤ conductivity p)
    (hθ : LowerPowerBound pc density 1)
    (hE : ∀ p : ℝ, pc < p → p ≤ 1 → variance p / 2 = conductivity p / density p) :
    UpperPowerBound pc variance 2 := by
  obtain ⟨CA, hCA, hA⟩ := hA
  obtain ⟨cθ, hcθ, hθ⟩ := hθ
  refine ⟨2 * CA / cθ, by positivity, ?_⟩
  intro p hp hp1
  have hgap : 0 < p - pc := by linarith
  have hθlo : cθ * (p - pc) ≤ density p := by simpa using hθ p hp hp1
  have hu := einstein_upper hgap hcθ (hAnn p hp hp1) (hA p hp hp1) hθlo (hE p hp hp1)
  refine hu.trans (le_of_eq ?_)
  field_simp

/-- Diffusivity upper bound UP TO THE LOGARITHM, from the frozen homogenized
conductivity log bound (`κ ≤ D·(p-pc)³·|log(p-pc)|`), a linear density lower bound,
and the Einstein identity: `σ²(p) ≤ D'·(p-pc)²·|log(p-pc)|` on `(pc, 1]`. -/
theorem sigma_sq_upper_of_conductivity_log {pc : ℝ} {conductivity density variance : ℝ → ℝ}
    {cθ : ℝ} (hcθ : 0 < cθ)
    (hκbound : ∃ D : ℝ, 0 < D ∧ ∀ p : ℝ, pc < p → p ≤ 1 →
      conductivity p ≤ D * (p - pc) ^ 3 * |Real.log (p - pc)|)
    (hκ0 : ∀ p : ℝ, pc < p → p ≤ 1 → 0 ≤ conductivity p)
    (hθlo : ∀ p : ℝ, pc < p → p ≤ 1 → cθ * (p - pc) ≤ density p)
    (hE : ∀ p : ℝ, pc < p → p ≤ 1 → variance p / 2 = conductivity p / density p) :
    ∃ D' : ℝ, 0 < D' ∧ ∀ p : ℝ, pc < p → p ≤ 1 →
      variance p ≤ D' * (p - pc) ^ 2 * |Real.log (p - pc)| := by
  obtain ⟨D, hD, hκ⟩ := hκbound
  refine ⟨2 * D / cθ, by positivity, ?_⟩
  intro p hp hp1
  have hgap : 0 < p - pc := by linarith
  have hu := einstein_upper hgap hcθ (hκ0 p hp hp1) (hκ p hp hp1) (hθlo p hp hp1) (hE p hp hp1)
  refine hu.trans (le_of_eq ?_)
  field_simp

end NearCritical
