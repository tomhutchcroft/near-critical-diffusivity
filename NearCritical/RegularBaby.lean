module

public import NearCritical.NestRegularBoundary

/-! Source lem.regular.baby (main.tex 3087): for every `(r,δ)`-regular point
`x ∈ fC ∩ ∂Q`, `∑_{y ∈ (fC ∩ ∂Q) \ {x}} |x-y|^{4-d} ≤ δ r^{d-4}`.

Proof as in the source. For lattice points `x ≠ y`, `|x-y| ≥ 1`, hence
`|x-y| ≥ max(r,|x-y|)/r`. With exponent `4-d ≤ 0` this gives
`|x-y|^{4-d} ≤ r^{d-4} max(r,|x-y|)^{4-d}`, and the sum is `r^{d-4}·ERE₂ ≤ δ r^{d-4}`.
Deterministic. Imports `NestRegularBoundary` read-only. -/
@[expose] public section
noncomputable section
namespace NearCritical

/-- Distinct lattice points are at supremum distance at least `1`. -/
lemma one_le_latticeDistance {d : ℕ} {x y : Vertex d} (h : x ≠ y) :
    1 ≤ latticeDistance x y := by
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ y i := by
    by_contra hc
    push_neg at hc
    exact h (funext hc)
  have h1 : dist (vertexReal x i) (vertexReal y i) ≤ latticeDistance x y :=
    dist_le_pi_dist (vertexReal x) (vertexReal y) i
  have h2 : (1 : ℝ) ≤ dist (vertexReal x i) (vertexReal y i) := by
    change (1 : ℝ) ≤ dist ((x i : ℤ) : ℝ) ((y i : ℤ) : ℝ)
    rw [Real.dist_eq, ← Int.cast_sub, ← Int.cast_abs]
    exact_mod_cast Int.one_le_abs (sub_ne_zero.mpr hi)
  linarith

/-- Source lem.regular.baby. -/
theorem regular_baby {d : ℕ} (hd : 4 ≤ d) {F S boundary : Finset (Vertex d)} {r : ℕ}
    (hr : 1 ≤ r) {δ : ℝ} {x : Vertex d} (hx : sourceRegularPoint F S boundary r δ x) :
    ∑ y ∈ (F ∩ boundary).erase x, (latticeDistance x y) ^ ((4 : ℤ) - (d : ℤ))
      ≤ δ * (r : ℝ) ^ ((d : ℤ) - 4) := by
  obtain ⟨k, rfl⟩ : ∃ k, d = k + 4 := ⟨d - 4, by omega⟩
  have he1 : (4 : ℤ) - ((k + 4 : ℕ) : ℤ) = -(k : ℤ) := by push_cast; ring
  have he2 : ((k + 4 : ℕ) : ℤ) - 4 = (k : ℤ) := by push_cast; ring
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hrpos : (0 : ℝ) < r := by linarith
  obtain ⟨_, _, hE2⟩ := hx
  unfold regularityEnergyTwo at hE2
  rw [he1] at hE2 ⊢
  rw [he2, zpow_natCast]
  have hpt : ∀ y ∈ (F ∩ boundary).erase x,
      (latticeDistance x y) ^ (-(k : ℤ)) ≤
        (r : ℝ) ^ k * (max (r : ℝ) (latticeDistance x y)) ^ (-(k : ℤ)) := by
    intro y hy
    have hyx : y ≠ x := (Finset.mem_erase.mp hy).1
    have hL1 : 1 ≤ latticeDistance x y := one_le_latticeDistance (Ne.symm hyx)
    have hLpos : 0 < latticeDistance x y := by linarith
    have hM : max (r : ℝ) (latticeDistance x y) ≤ (r : ℝ) * latticeDistance x y :=
      max_le (by nlinarith) (by nlinarith)
    have hMpos : 0 < max (r : ℝ) (latticeDistance x y) := lt_of_lt_of_le hrpos (le_max_left _ _)
    rw [zpow_neg, zpow_neg, zpow_natCast, zpow_natCast]
    rw [← div_eq_mul_inv, ← one_div, div_le_div_iff₀ (by positivity) (by positivity), one_mul,
      ← mul_pow]
    exact pow_le_pow_left₀ hMpos.le hM k
  calc ∑ y ∈ (F ∩ boundary).erase x, (latticeDistance x y) ^ (-(k : ℤ))
      ≤ ∑ y ∈ (F ∩ boundary).erase x,
          (r : ℝ) ^ k * (max (r : ℝ) (latticeDistance x y)) ^ (-(k : ℤ)) :=
        Finset.sum_le_sum hpt
    _ = (r : ℝ) ^ k * ∑ y ∈ (F ∩ boundary).erase x,
          (max (r : ℝ) (latticeDistance x y)) ^ (-(k : ℤ)) := by rw [Finset.mul_sum]
    _ ≤ (r : ℝ) ^ k * ∑ y ∈ F ∩ boundary, (max (r : ℝ) (latticeDistance x y)) ^ (-(k : ℤ)) :=
        mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
            (fun y _ _ => zpow_nonneg (le_trans hrpos.le (le_max_left _ _)) _))
          (by positivity)
    _ ≤ (r : ℝ) ^ k * δ := mul_le_mul_of_nonneg_left hE2 (by positivity)
    _ = δ * (r : ℝ) ^ k := by ring

end NearCritical
