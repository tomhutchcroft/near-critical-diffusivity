module

public import NearCritical.PioneerZeroLayer

/-! The positive-height pioneer estimate also controls height zero. -/
@[expose] public section
noncomputable section

namespace NearCritical

/-- A uniform positive-height bound gives an all-height bound after
enlarging the coefficient by the inverse edge parameter. -/
theorem halfSpace_pioneer_uniform_of_positive_heights {d : ℕ} (p : unitInterval)
    (i : Fin d) {K : ℝ} (hp : 0 < (p : ℝ)) (hK : 0 ≤ K)
    (h : ∀ n : ℕ, 1 ≤ n →
      halfSpacePioneerMass p i (n : ℤ) ≤ ENNReal.ofReal K) (n : ℕ) :
    halfSpacePioneerMass p i (n : ℤ) ≤ ENNReal.ofReal (K / (p : ℝ)) := by
  cases n with
  | zero =>
    rw [Nat.cast_zero, ENNReal.ofReal_div_of_pos hp]
    apply (ENNReal.le_div_iff_mul_le (.inl (ENNReal.ofReal_pos.mpr hp).ne')
      (.inl ENNReal.ofReal_ne_top)).mpr
    simpa only [mul_comm] using (halfSpace_pioneer_zero_mul_le_one p i).trans (h 1 le_rfl)
  | succ n =>
    apply (h (n + 1) (by omega)).trans (ENNReal.ofReal_le_ofReal ?_)
    apply (le_div_iff₀ hp).mpr
    exact mul_le_of_le_one_right hK p.property.2

end NearCritical
