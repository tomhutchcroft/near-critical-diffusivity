module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.UnitInterval
public import Mathlib.Tactic

/-! Arithmetic for the satisfiability of the parameter relations of
`time_constant_sandwich_of_pregood`.

* `exit_bound_eventually`: for `0 < p_c`, every `c > 0` has a threshold `J₀`
  with `((1 - p_c)(1 - q))^j <= c` for all `q` in `[0,1]` and `j >= J₀`
  (the exit relation, with `c = 1 - 1/rho`).
* `diam_ratio_le`: if `1 + C <= 4 A eta` and `T >= 1` then
  `(1 + C T^2) / (A (2T)^2 + 1) <= eta` (the diameter relation with
  `K_diam = A (2t)^2`).
-/
@[expose] public section
namespace NearCritical.Section10

theorem exit_bound_eventually {pc : ℝ} (hpc0 : 0 < pc) (hpc1 : pc ≤ 1) {c : ℝ} (hc : 0 < c) :
    ∃ J₀ : ℕ, ∀ q : unitInterval, ∀ j : ℕ, J₀ ≤ j → ((1 - pc) * (1 - (q : ℝ))) ^ j ≤ c := by
  have hb0 : 0 ≤ 1 - pc := by linarith
  have hb1 : 1 - pc < 1 := by linarith
  obtain ⟨J₀, hJ⟩ := exists_pow_lt_of_lt_one hc hb1
  refine ⟨J₀, fun q j hj => ?_⟩
  have hq0 : 0 ≤ 1 - (q : ℝ) := by linarith [q.2.2]
  have hq1 : 1 - (q : ℝ) ≤ 1 := by linarith [q.2.1]
  have hle : (1 - pc) * (1 - (q : ℝ)) ≤ 1 - pc := mul_le_of_le_one_right hb0 hq1
  calc ((1 - pc) * (1 - (q : ℝ))) ^ j ≤ (1 - pc) ^ j :=
        pow_le_pow_left₀ (mul_nonneg hb0 hq0) hle j
    _ ≤ (1 - pc) ^ J₀ := pow_le_pow_of_le_one hb0 hb1.le hj
    _ ≤ c := hJ.le

theorem diam_ratio_le {C A η T : ℝ} (hC : 0 ≤ C) (hA : 0 ≤ A) (hη : 0 < η) (hT : 1 ≤ T)
    (hrel : 1 + C ≤ 4 * A * η) :
    (1 + C * T ^ 2) / (A * (2 * T) ^ 2 + 1) ≤ η := by
  have hT2 : 1 ≤ T ^ 2 := by nlinarith
  have hden : 0 < A * (2 * T) ^ 2 + 1 := by positivity
  rw [div_le_iff₀ hden]
  have h1 : 1 + C * T ^ 2 ≤ (1 + C) * T ^ 2 := by nlinarith
  have h2 : (1 + C) * T ^ 2 ≤ 4 * A * η * T ^ 2 :=
    mul_le_mul_of_nonneg_right hrel (by positivity)
  nlinarith

end NearCritical.Section10
