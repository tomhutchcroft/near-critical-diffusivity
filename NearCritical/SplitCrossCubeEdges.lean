module

public import NearCritical.Section10Section9Geometry
public import NearCritical.Section8ExtensionConnectionLower

/-! The uniform two-point lower bound for the tree edges contained entirely
in the typical cube. -/
@[expose] public section
noncomputable section

namespace NearCritical.SplitCrossDirect

open Section10 MeasureTheory

/-- The root, spine, entry branch and cube-side dummy terminal all use this
same cube connection estimate. -/
theorem splitCross_cube_connection_lower {d : ℕ} (hd : 2 ≤ d)
    (lower : RestrictedRectangleLowerInput d) :
    ∃ b : ℝ, 0 < b ∧ ∀ (t : ℕ), 1 ≤ t → ∀ x y : Vertex d,
      x ∈ centeredBox d (7 * t / 16) → y ∈ centeredBox d (7 * t / 16) →
      b * (t : ℝ) ^ ((2 : ℝ) - (d : ℝ)) ≤
        (percolation d (criticalPoint d)).real
          (connectionToSetEvent (typicalCube t (0 : Vertex d) : Set (Vertex d)) x {y}) := by
  obtain ⟨b, hb, h⟩ := section8_rectangle_interior_pair_lower hd lower
  refine ⟨b, hb, ?_⟩
  intro t ht x y hx hy
  let l : Fin d → ℝ := fun _ => -1 / 2
  let u : Fin d → ℝ := fun _ => 1 / 2
  have hwidth (j : Fin d) : u j - l j ≤ 1 := by norm_num [u, l]
  have hrad : ((7 * t / 16 : ℕ) : ℝ) ≤ 7 * (t : ℝ) / 16 := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using
      (Nat.cast_div_le (α := ℝ) (m := 7 * t) (n := 16))
  have hinterior (z : Vertex d) (hz : z ∈ centeredBox d (7 * t / 16)) (j : Fin d) :
      l j * (t : ℝ) + (t : ℝ) / 16 ≤ (z j : ℝ) ∧
        (z j : ℝ) ≤ u j * (t : ℝ) - (t : ℝ) / 16 := by
    have ⟨hlo, hhi⟩ := mem_centeredBox.mp hz j
    have hlo' : -((7 * t / 16 : ℕ) : ℝ) ≤ (z j : ℝ) := by
      simpa only [Int.cast_neg, Int.cast_natCast] using
        (Int.cast_le.mpr hlo : ((-((7 * t / 16 : ℕ) : ℤ) : ℤ) : ℝ) ≤ (z j : ℝ))
    have hhi' : (z j : ℝ) ≤ ((7 * t / 16 : ℕ) : ℝ) := by
      simpa only [Int.cast_natCast] using
        (Int.cast_le.mpr hhi : (z j : ℝ) ≤ (((7 * t / 16 : ℕ) : ℤ) : ℝ))
    dsimp [l, u]
    constructor <;> linarith
  have hsub : {z : Vertex d | ∀ j,
      l j * (t : ℝ) < (z j : ℝ) ∧ (z j : ℝ) < u j * (t : ℝ)} ⊆
      (typicalCube t (0 : Vertex d) : Set (Vertex d)) := by
    intro z hz
    refine (mem_typicalCube_iff_int (by omega) 0 z).mpr ?_
    intro j
    simp only [Pi.zero_apply, sub_zero]
    apply (halfSide_iff (by omega) (z j)).mpr
    have hj := hz j
    dsimp [l, u] at hj
    constructor <;> linarith [hj.1, hj.2]
  exact (h t ht x y l u hwidth (hinterior x hx) (hinterior y hy)).trans
    (measureReal_mono (connectionToSetEvent_mono hsub subset_rfl x) (measure_ne_top _ _))

end NearCritical.SplitCrossDirect
