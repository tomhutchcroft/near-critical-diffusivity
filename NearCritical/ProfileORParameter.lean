module

public import NearCritical.ORParameter

/-! A common rectangular OR block for a uniformly subunit profile.
This is only parameter selection; no product-law identity or BK conclusion
is assumed or proved here. -/
@[expose] public section
noncomputable section
namespace NearCritical.BK
open Set

/-- At a fixed positive block length, every rate below the half-density
OR capacity has a low-density preimage. -/
lemma exists_or_parameter_at_length (p : unitInterval) (m : ℕ) (hm : 0 < m)
    (hcapacity : (p : ℝ) ≤ 1 - (1 / 2 : ℝ) ^ m) :
    ∃ q : unitInterval, (q : ℝ) ≤ 1 / 2 ∧
      (p : ℝ) = 1 - (1 - (q : ℝ)) ^ m := by
  let f : ℝ → ℝ := fun q ↦ 1 - (1 - q) ^ m
  have hf : Continuous f := by fun_prop
  have htarget : (p : ℝ) ∈ Icc (f 0) (f (1 / 2)) := by
    constructor
    · simpa [f, Nat.ne_of_gt hm] using p.property.1
    · change (p : ℝ) ≤ 1 - (1 - (1 / 2 : ℝ)) ^ m
      rw [show (1 - (1 / 2 : ℝ)) = 1 / 2 by norm_num]
      exact hcapacity
  obtain ⟨q, hq, hfp⟩ := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1 / 2)
    hf.continuousOn htarget
  refine ⟨⟨q, hq.1, hq.2.trans (by norm_num)⟩, hq.2, ?_⟩
  exact hfp.symm

/-- A uniform bound below one gives a SINGLE positive block length before
all coordinates, including zero rates. No finiteness of the index is needed. -/
theorem exists_common_or_parameters {E : Type*} (r : E → unitInterval)
    (P : unitInterval) (hP : (P : ℝ) < 1) (hr : ∀ e, r e ≤ P) :
    ∃ m : ℕ, 0 < m ∧ ∃ q : E → unitInterval,
      ∀ e, (q e : ℝ) ≤ 1 / 2 ∧
        (r e : ℝ) = 1 - (1 - (q e : ℝ)) ^ m := by
  obtain ⟨m, hcap⟩ : ∃ m : ℕ, (1 / 2 : ℝ) ^ m < 1 - (P : ℝ) :=
    exists_pow_lt_of_lt_one (sub_pos.mpr hP) (by norm_num)
  have hm : 0 < m := by
    by_contra h
    have hm0 : m = 0 := by omega
    rw [hm0, pow_zero] at hcap
    linarith [P.property.1]
  have hcoordinate (e : E) : (r e : ℝ) ≤ 1 - (1 / 2 : ℝ) ^ m := by
    have he : (r e : ℝ) ≤ (P : ℝ) := hr e
    linarith
  choose q hq using fun e => exists_or_parameter_at_length (r e) m hm (hcoordinate e)
  exact ⟨m, hm, q, hq⟩

end NearCritical.BK
