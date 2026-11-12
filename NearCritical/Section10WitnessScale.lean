module

public import NearCritical.Section10MeshLarge

/-! A uniform threshold `p₁` for the scale relations.

`scale_witness`: for `p_c < 1`, an even mesh factor `n0 = 2a` (`a >= 1`) and a
target `T₀ > 0`, there is `p₁ > p_c` such that for every `p` in `(p_c, p₁]`
the half-mesh `t = a * l_*(p)` satisfies `2t = n0 * l_*(p)`, `T₀ <= t`, and the
sprinkle parameter `q` with `p = p_c + (1 - p_c) q` lies in the window
`n0^2/(16(1-p_c)) <= q t^2 <= n0^2/(4(1-p_c))`.
-/
@[expose] public section
noncomputable section
namespace NearCritical.Section10

theorem scale_witness (d : ℕ) (hpc1 : (criticalPoint d : ℝ) < 1) (a : ℕ) (ha : 1 ≤ a)
    {T₀ : ℝ} (hT₀ : 0 < T₀) :
    ∃ p₁ : unitInterval, criticalPoint d < p₁ ∧
      ∀ p : unitInterval, criticalPoint d < p → p ≤ p₁ →
        2 * (a * chemicalCorrelationScale d p) = (2 * a) * chemicalCorrelationScale d p ∧
        T₀ ≤ ((a * chemicalCorrelationScale d p : ℕ) : ℝ) ∧
        ∃ q : unitInterval, orParameter (criticalPoint d) q = p ∧
          ((2 * a : ℕ) : ℝ) ^ 2 / (16 * (1 - (criticalPoint d : ℝ))) ≤
            (q : ℝ) * ((a * chemicalCorrelationScale d p : ℕ) : ℝ) ^ 2 ∧
          (q : ℝ) * ((a * chemicalCorrelationScale d p : ℕ) : ℝ) ^ 2 ≤
            ((2 * a : ℕ) : ℝ) ^ 2 / (4 * (1 - (criticalPoint d : ℝ))) := by
  set pc : ℝ := (criticalPoint d : ℝ) with hpc
  have hpc0 : 0 ≤ pc := (criticalPoint d).2.1
  have haR : (1:ℝ) ≤ ((2 * a : ℕ) : ℝ) := by
    have : 1 ≤ 2 * a := by omega
    exact_mod_cast this
  set g : ℝ := min ((((2 * a : ℕ) : ℝ) / (4 * T₀)) ^ 2) (1 - pc) with hg
  have hgpos : 0 < g := lt_min (by positivity) (by linarith)
  have hg1 : g ≤ 1 - pc := min_le_right _ _
  have hg2 : g ≤ (((2 * a : ℕ) : ℝ) / (4 * T₀)) ^ 2 := min_le_left _ _
  refine ⟨⟨pc + g, by linarith, by linarith⟩, ?_, ?_⟩
  · show pc < pc + g
    linarith
  · intro p hp hpp
    have hpp' : (p : ℝ) ≤ pc + g := hpp
    have hmesh : 2 * (a * chemicalCorrelationScale d p) =
        (2 * a) * chemicalCorrelationScale d p := by ring
    refine ⟨hmesh, ?_, ?_⟩
    · exact mesh_large d p hp (2 * a) (a * chemicalCorrelationScale d p) hmesh (by omega) hT₀
        (by
          have : (p : ℝ) - pc ≤ g := by linarith
          exact this.trans hg2)
    · exact sprinkle_window d p hp hpc1 (2 * a) (a * chemicalCorrelationScale d p) hmesh

end NearCritical.Section10
