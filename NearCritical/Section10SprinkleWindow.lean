module

public import NearCritical.ChemicalUpperBound
public import NearCritical.Section9SprinkleOrLaw

/-! The sprinkle parameter and its two-sided window.

For `p_c < p <= 1`, `p_c < 1`, mesh `2t = n0 * l_*(p)` with
`l_*(p) = floor((p - p_c)^{-1/2})`, the sprinkle parameter
`q = (p - p_c)/(1 - p_c)` satisfies `orParameter p_c q = p` and

  `n0^2 / (16 (1 - p_c)) <= q t^2 <= n0^2 / (4 (1 - p_c))`.

So the lower requirement `Lambda <= q t^2` of the Section 9 theorem holds once
`n0^2 >= 16 (1 - p_c) Lambda`, and the upper requirement `q <= q0 / t^2` of the
diameter bound holds with `q0 = n0^2 / (4 (1 - p_c))`. This is the first step
of the joint satisfiability of the parameter relations of
`time_constant_sandwich_of_pregood`.
-/
@[expose] public section
noncomputable section
namespace NearCritical.Section10

theorem sprinkle_window (d : ℕ) (p : unitInterval) (hp : criticalPoint d < p)
    (hpc1 : (criticalPoint d : ℝ) < 1) (n0 t : ℕ)
    (h : 2 * t = n0 * chemicalCorrelationScale d p) :
    ∃ q : unitInterval, orParameter (criticalPoint d) q = p ∧
      (n0 : ℝ) ^ 2 / (16 * (1 - (criticalPoint d : ℝ))) ≤ (q : ℝ) * (t : ℝ) ^ 2 ∧
      (q : ℝ) * (t : ℝ) ^ 2 ≤ (n0 : ℝ) ^ 2 / (4 * (1 - (criticalPoint d : ℝ))) := by
  set pc : ℝ := (criticalPoint d : ℝ) with hpc
  set δ : ℝ := (p : ℝ) - pc with hδdef
  have hδ : 0 < δ := sub_pos.mpr hp
  have h1pc : 0 < 1 - pc := by linarith
  have hδle : δ ≤ 1 - pc := by
    have := p.2.2
    linarith
  have hδ1 : δ ≤ 1 := by
    have := (criticalPoint d).2.1
    linarith
  set x : ℝ := (Real.sqrt δ)⁻¹ with hx
  have hsq : 0 < Real.sqrt δ := Real.sqrt_pos.mpr hδ
  have hsq1 : Real.sqrt δ ≤ 1 := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt hδ1
  have hx1 : 1 ≤ x := (one_le_inv₀ hsq).mpr hsq1
  have hδx : δ * x ^ 2 = 1 := by
    rw [hx, inv_pow, Real.sq_sqrt hδ.le]
    exact mul_inv_cancel₀ hδ.ne'
  set s : ℕ := chemicalCorrelationScale d p with hs
  have hsx : (s : ℝ) ≤ x := chemicalCorrelationScale_le d p
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
  have hq0 : 0 ≤ δ / (1 - pc) := div_nonneg hδ.le h1pc.le
  have hq1 : δ / (1 - pc) ≤ 1 := (div_le_one h1pc).mpr hδle
  refine ⟨⟨δ / (1 - pc), hq0, hq1⟩, ?_, ?_, ?_⟩
  · apply Subtype.ext
    show pc + (1 - pc) * (δ / (1 - pc)) = (p : ℝ)
    rw [mul_div_cancel₀ _ h1pc.ne']
    rw [hδdef]
    ring
  · show (n0 : ℝ) ^ 2 / (16 * (1 - pc)) ≤ δ / (1 - pc) * (t : ℝ) ^ 2
    rw [ht]
    have hlow : (1:ℝ) / 4 ≤ δ * (s : ℝ) ^ 2 := by
      have hxsq : x ^ 2 ≤ 4 * (s : ℝ) ^ 2 := by nlinarith
      nlinarith
    rw [div_le_iff₀ (by positivity)]
    have hid : δ / (1 - pc) * ((n0 : ℝ) * (s : ℝ) / 2) ^ 2 * (16 * (1 - pc)) =
        4 * (n0 : ℝ) ^ 2 * (δ * (s : ℝ) ^ 2) := by
      field_simp
      ring
    rw [hid]
    nlinarith [sq_nonneg (n0 : ℝ)]
  · show δ / (1 - pc) * (t : ℝ) ^ 2 ≤ (n0 : ℝ) ^ 2 / (4 * (1 - pc))
    rw [ht]
    have hup : δ * (s : ℝ) ^ 2 ≤ 1 := by
      have hssq : (s : ℝ) ^ 2 ≤ x ^ 2 := by nlinarith
      nlinarith
    rw [le_div_iff₀ (by positivity)]
    have hid : δ / (1 - pc) * ((n0 : ℝ) * (s : ℝ) / 2) ^ 2 * (4 * (1 - pc)) =
        (n0 : ℝ) ^ 2 * (δ * (s : ℝ) ^ 2) := by
      field_simp
      ring
    rw [hid]
    nlinarith [sq_nonneg (n0 : ℝ)]

end NearCritical.Section10
