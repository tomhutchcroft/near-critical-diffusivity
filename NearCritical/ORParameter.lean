module

public import NearCritical.BK
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Tactic.FunProp

/-! Choose a low-density Bernoulli parameter whose finite OR aggregation has
any prescribed p<1. An intermediate-value proof avoids fractional powers. -/
@[expose] public section
noncomputable section
namespace NearCritical.BK
open Set

/-- Every p in [0,1) is the OR of finitely many independent Bernoulli-q bits
for some q in [0,1/2]. The product-law statement is proved separately. -/
theorem exists_or_parameter (p : unitInterval) (hp : (p : ℝ) < 1) :
    ∃ m : ℕ, 0 < m ∧ ∃ q : unitInterval, (q : ℝ) ≤ 1 / 2 ∧
      (p : ℝ) = 1 - (1 - (q : ℝ)) ^ m := by
  obtain ⟨m, hm⟩ : ∃ m : ℕ, (1 / 2 : ℝ) ^ m < 1 - (p : ℝ) :=
    exists_pow_lt_of_lt_one (sub_pos.mpr hp) (by norm_num)
  have hmpos : 0 < m := by
    by_contra h
    have hm0 : m = 0 := by omega
    rw [hm0, pow_zero] at hm
    linarith [p.property.1]
  let f : ℝ → ℝ := fun q ↦ 1 - (1 - q) ^ m
  have hf : Continuous f := by fun_prop
  have htarget : (p : ℝ) ∈ Icc (f 0) (f (1 / 2)) := by
    constructor
    · simpa [f] using p.property.1
    · change (p : ℝ) ≤ 1 - (1 - (1 / 2 : ℝ)) ^ m
      norm_num only [show (1 - (1 / 2 : ℝ)) = 1 / 2 by norm_num]
      linarith
  obtain ⟨q, hq, hfp⟩ := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1 / 2)
    hf.continuousOn htarget
  refine ⟨m, hmpos, ⟨q, hq.1, hq.2.trans (by norm_num)⟩, hq.2, ?_⟩
  exact hfp.symm

end NearCritical.BK
