module

public import NearCritical.SplitCrossSpineBoxes

/-! The macroscopic separation coefficient is fixed before choosing a
star length. At a large enough box scale it works for every edge. -/
@[expose] public section
noncomputable section

namespace NearCritical.SplitCrossDirect

theorem crossing_overlap_scales_eventually (d : ℕ) :
    ∃ q : ℝ, 0 < q ∧ ∀ R : ℕ, ∃ T : ℕ, ∀ t ≥ T,
      3 * ((R + 1 : ℕ) : ℝ) ≤ (spineRadius (4 * d - 1) t : ℝ) ∧
      q * (t : ℝ) + 2 * ((R + 1 : ℕ) : ℝ) ≤ (spineRadius (4 * d - 1) t : ℝ) := by
  let D : ℕ := 256 * (4 * d - 1 + 1)
  let q : ℝ := 1 / (4 * (D : ℝ))
  have hD : 0 < D := by dsimp [D]; positivity
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  have hq : 0 < q := by dsimp [q]; positivity
  refine ⟨q, hq, ?_⟩
  intro R
  let m : ℕ := R + 1
  refine ⟨4 * D * (3 * m + 1), ?_⟩
  intro t ht
  let s : ℝ := q * (t : ℝ)
  have hsD : 4 * (D : ℝ) * s = (t : ℝ) := by
    dsimp [s, q]
    field_simp
  have hs : 3 * (m : ℝ) + 1 ≤ s := by
    apply (mul_le_mul_iff_right₀ (by positivity : (0 : ℝ) < 4 * (D : ℝ))).mp
    rw [hsD]
    exact_mod_cast ht
  have hfloorN : t ≤ D * (spineRadius (4 * d - 1) t + 1) := by
    change t ≤ D * (t / D + 1)
    rw [Nat.mul_add, Nat.mul_one]
    have hmod := Nat.mod_lt t hD
    have hdiv := Nat.mod_add_div t D
    omega
  have hfloorR : (t : ℝ) ≤ (D : ℝ) * ((spineRadius (4 * d - 1) t : ℝ) + 1) := by
    exact_mod_cast hfloorN
  have hfloor : 4 * s ≤ (spineRadius (4 * d - 1) t : ℝ) + 1 := by
    apply (mul_le_mul_iff_right₀ hD').mp
    calc
      _ = (t : ℝ) := by linarith only [hsD]
      _ ≤ _ := hfloorR
  have hm : 0 ≤ (m : ℝ) := by positivity
  change 3 * (m : ℝ) ≤ (spineRadius (4 * d - 1) t : ℝ) ∧
    s + 2 * (m : ℝ) ≤ (spineRadius (4 * d - 1) t : ℝ)
  constructor <;> linarith

end NearCritical.SplitCrossDirect
