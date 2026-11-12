module

public import NearCritical.SplitCrossTerminalBox

/-! Cube-side entry and terminal boxes for the split-crossing tree.
The entry box sits on the same transverse strip as the exterior leg boxes.
Both cube-side boxes leave a linear margin to the cube boundary. -/
@[expose] public section
noncomputable section

namespace NearCritical.SplitCrossDirect

open Section10
open scoped Classical

/-- Axial height of the branch box (`true`) or its dummy terminal box. -/
def entryBoxHeight (t : ℕ) (branch : Bool) : ℤ :=
  if branch then 3 * (t : ℤ) / 8 else (t : ℤ) / 4

def entryLegBox {d : ℕ} (t : ℕ) (f : Fin d × Bool) (pl branch : Bool) :
    Finset (Vertex d) :=
  translateSites (legBoxCenter t f pl (entryBoxHeight t branch))
    (centeredBox d (legBoxRadius t))

theorem entryLegBox_height_bounds {d t : ℕ} {f : Fin d × Bool} {pl branch : Bool}
    {y : Vertex d} (hy : y ∈ entryLegBox t f pl branch) :
    entryBoxHeight t branch - (legBoxRadius t : ℤ) ≤ faceHeight f y ∧
      faceHeight f y ≤ entryBoxHeight t branch + (legBoxRadius t : ℤ) :=
  legBox_height_bounds f pl _ hy

private theorem entryLegBox_transverse_bounds {d t : ℕ} {f : Fin d × Bool} {pl branch : Bool}
    {y : Vertex d} (hy : y ∈ entryLegBox t f pl branch) (i : Fin d) (hi : i ≠ f.1) :
    (if pl then 3 * (t : ℤ) / 16 else -(3 * (t : ℤ) / 16)) - (legBoxRadius t : ℤ) ≤ y i ∧
      y i ≤ (if pl then 3 * (t : ℤ) / 16 else -(3 * (t : ℤ) / 16)) + (legBoxRadius t : ℤ) := by
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
  have hzi := mem_centeredBox.mp hz i
  simp [legBoxCenter, Pi.add_apply, hi]
  omega

theorem entryLegBox_subset_inner_cube {d t : ℕ} (ht : 64 ≤ t) (f : Fin d × Bool) (pl branch : Bool) :
    entryLegBox t f pl branch ⊆ centeredBox d (7 * t / 16) := by
  intro y hy
  have hax := entryLegBox_height_bounds hy
  apply mem_centeredBox.mpr
  intro i
  by_cases hi : i = f.1
  · subst i
    obtain ⟨i, sign⟩ := f
    cases sign <;> cases branch <;>
      simp [faceHeight, entryBoxHeight, legBoxRadius] at hax ⊢ <;> omega
  · have htr := entryLegBox_transverse_bounds hy i hi
    cases pl <;> simp [legBoxRadius] at htr ⊢ <;> omega

theorem entryLegBox_subset_cube {d t : ℕ} (ht : 64 ≤ t)
    (f : Fin d × Bool) (pl branch : Bool) :
    entryLegBox t f pl branch ⊆ typicalCube t (0 : Vertex d) := by
  intro y hy
  have hinner := mem_centeredBox.mp (entryLegBox_subset_inner_cube ht f pl branch hy)
  apply (mem_typicalCube_iff_int (by omega) 0 y).mpr
  intro i
  have hb := hinner i
  simp only [Pi.zero_apply, sub_zero]
  omega

theorem entryLegBox_card {d : ℕ} (t : ℕ) (f : Fin d × Bool) (pl branch : Bool) :
    (entryLegBox t f pl branch).card = (2 * legBoxRadius t + 1) ^ d := by
  rw [entryLegBox, card_translateSites, card_centeredBox_exact]

/-- The entry and dummy boxes are separated from the allowable root region. -/
theorem entryLegBox_dist_root {d t : ℕ} (ht : 64 ≤ t)
    {f : Fin d × Bool} {pl branch : Bool} {x y : Vertex d}
    (hx : x ∈ centeredBox d ((t - 1) / 32)) (hy : y ∈ entryLegBox t f pl branch) :
    ((t / 8 : ℕ) : ℝ) ≤ dist x y := by
  have hax := (entryLegBox_height_bounds hy).1
  obtain ⟨i, sign⟩ := f
  have hr := mem_centeredBox.mp hx i
  have h₁ := le_abs_self (x i - y i)
  have h₂ := neg_le_abs (x i - y i)
  have hdist : ((t / 8 : ℕ) : ℤ) ≤ |x i - y i| := by
    cases sign <;> cases branch <;> simp [faceHeight, entryBoxHeight, legBoxRadius] at hax <;> omega
  refine le_trans ?_ (dist_le_pi_dist x y i)
  rw [Int.dist_eq]
  simpa only [Int.cast_natCast, Int.cast_abs, Int.cast_sub] using
    (Int.cast_le.mpr hdist : (((t / 8 : ℕ) : ℤ) : ℝ) ≤ ((|x i - y i| : ℤ) : ℝ))

end NearCritical.SplitCrossDirect
