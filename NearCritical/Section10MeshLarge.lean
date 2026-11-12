module

public import NearCritical.Section10SprinkleWindow

/-! The mesh is large close to the critical point.

`mesh_large`: with `2t = n0 * l_*(p)`, `n0 >= 1` and
`p - p_c <= (n0 / (4 T₀))^2`, the half-mesh satisfies `T₀ <= t`. This supplies
`t >= 9`, `t >= N₀` and the largeness of `(2t)^(d-6)` in the parameter
relations of `time_constant_sandwich_of_pregood`, uniformly for `p` in
`(p_c, p₁]` with `p₁` close to `p_c`.
-/
@[expose] public section
noncomputable section
namespace NearCritical.Section10

theorem mesh_large (d : ℕ) (p : unitInterval) (hp : criticalPoint d < p) (n0 t : ℕ)
    (h : 2 * t = n0 * chemicalCorrelationScale d p) (hn0 : 1 ≤ n0) {T₀ : ℝ} (hT₀ : 0 < T₀)
    (hclose : (p : ℝ) - (criticalPoint d : ℝ) ≤ ((n0 : ℝ) / (4 * T₀)) ^ 2) :
    T₀ ≤ (t : ℝ) := by
  set δ : ℝ := (p : ℝ) - (criticalPoint d : ℝ) with hδdef
  have hδ : 0 < δ := sub_pos.mpr hp
  have hδ1 : δ ≤ 1 := by
    have h1 := p.2.2
    have h2 := (criticalPoint d).2.1
    linarith
  have hn0R : (1:ℝ) ≤ (n0 : ℝ) := by exact_mod_cast hn0
  set x : ℝ := (Real.sqrt δ)⁻¹ with hx
  have hsq : 0 < Real.sqrt δ := Real.sqrt_pos.mpr hδ
  have hsq1 : Real.sqrt δ ≤ 1 := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt hδ1
  have hx1 : 1 ≤ x := (one_le_inv₀ hsq).mpr hsq1
  set s : ℕ := chemicalCorrelationScale d p with hs
  have hxs : x < (s : ℝ) + 1 := by
    rw [hs]
    unfold chemicalCorrelationScale
    exact Nat.lt_floor_add_one _
  have hs1 : 1 ≤ s := by
    rw [hs]
    unfold chemicalCorrelationScale
    exact Nat.le_floor (by exact_mod_cast hx1)
  have hs1R : (1:ℝ) ≤ (s : ℝ) := by exact_mod_cast hs1
  have hx2s : x ≤ 2 * (s : ℝ) := by linarith
  have ht : (t : ℝ) = (n0 : ℝ) * (s : ℝ) / 2 := by
    have h' : (2 : ℝ) * (t : ℝ) = (n0 : ℝ) * (s : ℝ) := by exact_mod_cast h
    linarith
  have hratio : 0 < (n0 : ℝ) / (4 * T₀) := by positivity
  have hsqle : Real.sqrt δ ≤ (n0 : ℝ) / (4 * T₀) := by
    rw [← Real.sqrt_sq hratio.le]
    exact Real.sqrt_le_sqrt hclose
  have hxge : 4 * T₀ / (n0 : ℝ) ≤ x := by
    rw [hx, le_inv_comm₀ (by positivity) hsq]
    rw [inv_div]
    exact hsqle
  have hmul : 4 * T₀ ≤ (n0 : ℝ) * x := by
    have h1 := mul_le_mul_of_nonneg_left hxge (by positivity : (0:ℝ) ≤ (n0 : ℝ))
    rwa [mul_div_cancel₀ _ (by positivity : (n0 : ℝ) ≠ 0)] at h1
  rw [ht]
  nlinarith [mul_le_mul_of_nonneg_left hx2s (by positivity : (0:ℝ) ≤ (n0 : ℝ))]

end NearCritical.Section10
