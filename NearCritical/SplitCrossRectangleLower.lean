module

public import NearCritical.Section8RectangleLowerInput
public import NearCritical.AppendixBoxFaceBudget

/-! Uniform two-point lower bounds for the fixed rectangle shapes used by
the interior edges of the exterior split legs. -/
@[expose] public section
noncomputable section

namespace NearCritical.SplitCrossDirect

open MeasureTheory
open scoped Classical

def splitLegExpandedRectangle {d : ℕ} (lo hi : Fin d → ℝ) (t : ℕ) (x : Vertex d) :
    Set (Vertex d) :=
  (fun z : Vertex d => x + z) '' section8Rectangle
    (fun j => (513 / 512 : ℝ) * lo j) (fun j => (513 / 512 : ℝ) * hi j) t

/-- The finitely many signed directions share a positive constant for the
cited two-point lower bound. -/
theorem splitLeg_rectangle_connection_lower {d : ℕ} (hd : 2 ≤ d)
    (lower : RestrictedRectangleLowerInput d) (lo hi : (Fin d × Bool) → Fin d → ℝ)
    (hlo : ∀ f j, 0 < lo f j ∧ lo f j ≤ 2) (hhi : ∀ f j, 0 < hi f j ∧ hi f j ≤ 2) :
    ∃ b : ℝ, 0 < b ∧ ∀ (t : ℕ), 1 ≤ t → ∀ (f : Fin d × Bool) (x y : Vertex d),
      y - x ∈ section8Rectangle (lo f) (hi f) t →
      b * (2 * (t : ℝ)) ^ ((2 : ℝ) - (d : ℝ)) ≤
        (percolation d (criticalPoint d)).real
          (connectionToSetEvent (splitLegExpandedRectangle (lo f) (hi f) t x) x {y}) := by
  classical
  letI : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  have hex (f : Fin d × Bool) := section8_translated_rectangle_lower lower
    (lo f) (hi f) (fun j => (hlo f j).1) (fun j => (hhi f j).1) (513 / 512) (by norm_num)
  let C (f : Fin d × Bool) := Classical.choose (hex f)
  have hC (f : Fin d × Bool) : 0 < C f := (Classical.choose_spec (hex f)).1
  let b := Finset.univ.inf' Finset.univ_nonempty C
  have hb : 0 < b := (Finset.lt_inf'_iff Finset.univ_nonempty).mpr (fun f _ => hC f)
  refine ⟨b, hb, ?_⟩
  intro t ht f x y hrel
  have hdist : latticeDistance 0 (y - x) ≤ 2 * (t : ℝ) := by
    refine latticeDistance_le_of_coord 0 (y - x) (by positivity) ?_
    intro j
    have hj := hrel j
    have h₁ := mul_le_mul_of_nonneg_right (hlo f j).2 (show 0 ≤ (t : ℝ) by positivity)
    have h₂ := mul_le_mul_of_nonneg_right (hhi f j).2 (show 0 ≤ (t : ℝ) by positivity)
    simp only [Pi.zero_apply, Int.cast_zero, zero_sub, abs_neg]
    rw [abs_le]
    constructor <;> linarith [hj.1, hj.2]
  have htR : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hk : (2 * (t : ℝ)) ^ ((2 : ℝ) - (d : ℝ)) ≤
      (max 1 (latticeDistance 0 (y - x))) ^ ((2 : ℝ) - (d : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
      (max_le (by linarith) hdist) (by linarith)
  have hc : b ≤ C f := Finset.inf'_le C (Finset.mem_univ f)
  have hh := (Classical.choose_spec (hex f)).2 t (by omega) x y hrel
  exact (mul_le_mul hc hk (Real.rpow_nonneg (by positivity) _) (hC f).le).trans hh


end NearCritical.SplitCrossDirect
