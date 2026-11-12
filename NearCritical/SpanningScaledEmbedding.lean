module

public import NearCritical.SpanningRoundedCuboid
public import NearCritical.SpanningCorridorMargins

/-! Exact link between normalized embedded vertices and the source lattice
cuboids. Positive scales are retained through denominator clearing. -/
@[expose] public section
noncomputable section
namespace NearCritical
open scoped Classical

def scaledSpanningVertex {d : ℕ} (n : ℕ) (z : Vertex d) : Fin d → ℝ :=
  fun i => (z i:ℝ)/(n:ℝ)

private lemma scaledSpanningHeight {d : ℕ} (n : ℕ) (f : Fin d × Bool) (z : Vertex d) :
    realSpanningHeight f (scaledSpanningVertex n z) = (spanningSignedHeight f z:ℝ)/(n:ℝ) := by
  rcases f with ⟨i,s⟩
  cases s <;> simp [realSpanningHeight,spanningSignedHeight,scaledSpanningVertex,neg_div]

/-- Normalized corridor bounds give EXACT source integer inequalities. -/
theorem scaledSpanningVertex_mem_cuboid {d n : ℕ} (hn : 1 ≤ n)
    (f : Fin d × Bool) (z : Vertex d)
    (hheight : -(3/8:ℝ) ≤ realSpanningHeight f (scaledSpanningVertex n z) ∧
      realSpanningHeight f (scaledSpanningVertex n z) ≤ 3)
    (htransverse : ∀ j, j ≠ f.1 → |scaledSpanningVertex n z j| ≤ (1/8:ℝ)) :
    z ∈ roundedSourceSpanningCuboid n f := by
  have hnpos : 0 < (n:ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  rw [scaledSpanningHeight] at hheight
  have hlo := (le_div_iff₀ hnpos).mp hheight.1
  have hhi := (div_le_iff₀ hnpos).mp hheight.2
  refine ⟨?_,?_,?_⟩
  · exact_mod_cast (show -3*(n:ℝ) ≤ 8*(spanningSignedHeight f z:ℝ) by linarith)
  · exact_mod_cast (show 8*(spanningSignedHeight f z:ℝ) ≤ 24*(n:ℝ) by linarith)
  · intro j hj
    have ht : |(z j:ℝ)|/(n:ℝ) ≤ (1/8:ℝ) := by
      simpa only [scaledSpanningVertex,abs_div,abs_of_pos hnpos] using htransverse j hj
    have hb := (div_le_iff₀ hnpos).mp ht
    exact_mod_cast (show 8*|(z j:ℝ)| ≤ (n:ℝ) by linarith)

/-- Normalized endpoint bounds give EXACT source target integer inequalities. -/
theorem scaledSpanningVertex_mem_target {d n : ℕ} (hn : 1 ≤ n)
    (f : Fin d × Bool) (z : Vertex d)
    (hheight : (15/8:ℝ) ≤ realSpanningHeight f (scaledSpanningVertex n z) ∧
      realSpanningHeight f (scaledSpanningVertex n z) ≤ 17/8)
    (htransverse : ∀ j, j ≠ f.1 → |scaledSpanningVertex n z j| ≤ (1/8:ℝ)) :
    z ∈ roundedSourceSpanningTarget n f := by
  have hnpos : 0 < (n:ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  rw [scaledSpanningHeight] at hheight
  have hlo := (le_div_iff₀ hnpos).mp hheight.1
  have hhi := (div_le_iff₀ hnpos).mp hheight.2
  refine ⟨?_,?_,?_⟩
  · exact_mod_cast (show 15*(n:ℝ) ≤ 8*(spanningSignedHeight f z:ℝ) by linarith)
  · exact_mod_cast (show 8*(spanningSignedHeight f z:ℝ) ≤ 17*(n:ℝ) by linarith)
  · intro j hj
    have ht : |(z j:ℝ)|/(n:ℝ) ≤ (1/8:ℝ) := by
      simpa only [scaledSpanningVertex,abs_div,abs_of_pos hnpos] using htransverse j hj
    have hb := (div_le_iff₀ hnpos).mp ht
    exact_mod_cast (show 8*|(z j:ℝ)| ≤ (n:ℝ) by linarith)

/-- Robust limiting corridor plus actual rescaled embedding agreement yields
membership of the ACTUAL integer vertex in the source corridor. -/
theorem spanning_limit_corridor_to_integer {d n : ℕ} (hn : 1 ≤ n)
    (f : Fin d × Bool) (z : Vertex d) (w : Fin d → ℝ)
    (herror : dist (scaledSpanningVertex n z) w ≤ (1/32:ℝ))
    (hheight : -(1/4:ℝ) ≤ realSpanningHeight f w ∧ realSpanningHeight f w ≤ 5/2)
    (htransverse : ∀ j, j ≠ f.1 → |w j| ≤ (1/32:ℝ)) :
    z ∈ roundedSourceSpanningCuboid n f := by
  obtain ⟨hlo,hhi,ht⟩ := spanning_corridor_margin f (scaledSpanningVertex n z) w
    herror hheight htransverse
  exact scaledSpanningVertex_mem_cuboid hn f z ⟨hlo,hhi⟩ ht

/-- Robust limiting target plus actual rescaled embedding agreement yields
membership of the ACTUAL integer vertex in the source target. -/
theorem spanning_limit_target_to_integer {d n : ℕ} (hn : 1 ≤ n)
    (f : Fin d × Bool) (z : Vertex d) (w : Fin d → ℝ)
    (herror : dist (scaledSpanningVertex n z) w ≤ (1/32:ℝ))
    (hheight : |realSpanningHeight f w-2| ≤ (1/32:ℝ))
    (htransverse : ∀ j, j ≠ f.1 → |w j| ≤ (1/32:ℝ)) :
    z ∈ roundedSourceSpanningTarget n f := by
  obtain ⟨hlo,hhi,ht⟩ := spanning_target_margin f (scaledSpanningVertex n z) w
    herror hheight htransverse
  exact scaledSpanningVertex_mem_target hn f z ⟨hlo,hhi⟩ ht

end NearCritical
