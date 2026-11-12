module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

@[expose] public section

namespace NearCritical

/-- Pointwise algebra in the homogenization reduction, with all probabilistic
inputs exposed. `variance` denotes σ², not σ. This is not Theorem 1.1. -/
theorem einstein_bounds {δ conductivity density variance cA CA cθ Cθ : ℝ}
    (hδ : 0 < δ) (hcA : 0 < cA) (hCθ : 0 < Cθ) (hcθ : 0 < cθ)
    (hAlo : cA * δ ^ 3 ≤ conductivity) (hAhi : conductivity ≤ CA * δ ^ 3)
    (hθlo : cθ * δ ≤ density) (hθhi : density ≤ Cθ * δ)
    (hEinstein : variance / 2 = conductivity / density) :
    (2 * cA / Cθ) * δ ^ 2 ≤ variance ∧
      variance ≤ (2 * CA / cθ) * δ ^ 2 := by
  have hθ : 0 < density := lt_of_lt_of_le (mul_pos hcθ hδ) hθlo
  have hA : 0 < conductivity := lt_of_lt_of_le (mul_pos hcA (pow_pos hδ 3)) hAlo
  have hσ : 0 < variance := by
    have := div_pos hA hθ
    rw [← hEinstein] at this
    linarith
  have hid : variance * density = 2 * conductivity := by
    have := (div_eq_iff (ne_of_gt hθ)).mp hEinstein.symm
    linarith
  have hlo : (2 * cA * δ ^ 2) * δ ≤ (variance * Cθ) * δ := by
    nlinarith [mul_le_mul_of_nonneg_left hθhi (le_of_lt hσ)]
  have hhi : (variance * cθ) * δ ≤ (2 * CA * δ ^ 2) * δ := by
    nlinarith [mul_le_mul_of_nonneg_left hθlo (le_of_lt hσ)]
  have hlo' := (mul_le_mul_iff_left₀ hδ).mp hlo
  have hhi' := (mul_le_mul_iff_left₀ hδ).mp hhi
  constructor
  · rw [div_mul_eq_mul_div]
    exact (div_le_iff₀ hCθ).2 hlo'
  · rw [div_mul_eq_mul_div]
    exact (le_div_iff₀ hcθ).2 hhi' 

/-- Uniform two-sided bounds on the entire supercritical parameter interval.
The constants are chosen before quantifying over the parameter. -/
def UniformPowerBounds (pc : ℝ) (f : ℝ → ℝ) (k : ℕ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧
    ∀ p : ℝ, pc < p → p ≤ 1 → c * (p - pc) ^ k ≤ f p ∧ f p ≤ C * (p - pc) ^ k

/-- The uniform algebraic reduction in the introduction. It assumes, rather
than asserts, the conductivity bounds, mean-field density bounds, and Einstein
identity. In particular it does not prove the paper's percolation estimates. -/
theorem uniform_einstein_bounds {pc : ℝ} {conductivity density variance : ℝ → ℝ}
    (hA : UniformPowerBounds pc conductivity 3)
    (hθ : UniformPowerBounds pc density 1)
    (hE : ∀ p : ℝ, pc < p → p ≤ 1 → variance p / 2 = conductivity p / density p) :
    UniformPowerBounds pc variance 2 := by
  obtain ⟨cA, hcA, CA, hCA, hA⟩ := hA
  obtain ⟨cθ, hcθ, Cθ, hCθ, hθ⟩ := hθ
  refine ⟨2 * cA / Cθ, div_pos (mul_pos (by norm_num) hcA) hCθ,
    2 * CA / cθ, div_pos (mul_pos (by norm_num) hCA) hcθ, ?_⟩
  intro p hp hp1
  obtain ⟨hAlo, hAhi⟩ := hA p hp hp1
  obtain ⟨hθlo, hθhi⟩ := hθ p hp hp1
  simp only [pow_one] at hθlo hθhi
  exact einstein_bounds (sub_pos.mpr hp) hcA hCθ hcθ hAlo hAhi hθlo hθhi (hE p hp hp1)

end NearCritical
