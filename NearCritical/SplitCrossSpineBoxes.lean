module

public import NearCritical.SplitCrossEntryBoxes

/-! A finite line of separated branch boxes in the common cube of all legs. -/
@[expose] public section
noncomputable section

namespace NearCritical.SplitCrossDirect

open Section10
open scoped Classical

def spineRadius (K t : ℕ) : ℕ := t / (256 * (K + 1))

def spineBoxCenter {d K : ℕ} (t : ℕ) (axis : Fin d) (k : Fin K) : Vertex d :=
  fun j => if j = axis then ((t / 16 : ℕ) : ℤ) + 4 * (spineRadius K t : ℤ) * (k.val : ℤ)
    else 0

def spineBox {d K : ℕ} (t : ℕ) (axis : Fin d) (k : Fin K) : Finset (Vertex d) :=
  translateSites (spineBoxCenter t axis k) (centeredBox d (spineRadius K t))

private theorem spineRadius_budget (K t : ℕ) : 256 * spineRadius K t * (K + 1) ≤ t := by
  unfold spineRadius
  convert Nat.div_mul_le_self t (256 * (K + 1)) using 1
  ring

theorem spineBox_card {d K : ℕ} (t : ℕ) (axis : Fin d) (k : Fin K) :
    (spineBox t axis k).card = (2 * spineRadius K t + 1) ^ d := by
  rw [spineBox, card_translateSites, card_centeredBox_exact]

theorem spineBox_subset_inner_cube {d K t : ℕ} (ht : 64 ≤ t)
    (axis : Fin d) (k : Fin K) : spineBox t axis k ⊆ centeredBox d (t / 8) := by
  intro y hy
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
  have hb : 256 * spineRadius K t * (k.val + 1) ≤ t :=
    (Nat.mul_le_mul_left _ (by omega : k.val + 1 ≤ K + 1)).trans (spineRadius_budget K t)
  have hr : 256 * spineRadius K t ≤ t :=
    (Nat.le_mul_of_pos_right _ (Nat.succ_pos K)).trans (spineRadius_budget K t)
  have hbudget : 256 * (spineRadius K t : ℤ) * (k.val : ℤ) +
      256 * (spineRadius K t : ℤ) ≤ (t : ℤ) := by
    exact_mod_cast (by simpa only [Nat.mul_add, Nat.mul_one] using hb :
      256 * spineRadius K t * k.val + 256 * spineRadius K t ≤ t)
  have hscale : 256 * (spineRadius K t : ℤ) * (k.val : ℤ) =
      64 * (4 * (spineRadius K t : ℤ) * (k.val : ℤ)) := by ring
  rw [hscale] at hbudget
  have hpos : 0 ≤ 4 * (spineRadius K t : ℤ) * (k.val : ℤ) := by positivity
  have hr' : 256 * (spineRadius K t : ℤ) ≤ (t : ℤ) := by exact_mod_cast hr
  apply mem_centeredBox.mpr
  intro j
  have hz' := mem_centeredBox.mp hz j
  by_cases hj : j = axis
  · subst j
    simp [spineBoxCenter, Pi.add_apply]
    omega
  · simp [spineBoxCenter, Pi.add_apply, hj]
    omega

theorem spineBox_subset_cube {d K t : ℕ} (ht : 64 ≤ t)
    (axis : Fin d) (k : Fin K) : spineBox t axis k ⊆ typicalCube t (0 : Vertex d) := by
  intro y hy
  have hb := mem_centeredBox.mp (spineBox_subset_inner_cube ht axis k hy)
  apply (mem_typicalCube_iff_int (by omega) 0 y).mpr
  intro j
  have hj := hb j
  simp only [Pi.zero_apply, sub_zero]
  omega

private theorem spineBox_axis_bounds {d K t : ℕ} {axis : Fin d} {k : Fin K} {y : Vertex d}
    (hy : y ∈ spineBox t axis k) :
    ((t / 16 : ℕ) : ℤ) + 4 * (spineRadius K t : ℤ) * (k.val : ℤ) -
      (spineRadius K t : ℤ) ≤ y axis ∧
      y axis ≤ ((t / 16 : ℕ) : ℤ) + 4 * (spineRadius K t : ℤ) * (k.val : ℤ) +
      (spineRadius K t : ℤ) := by
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
  have hz' := mem_centeredBox.mp hz axis
  simp [spineBoxCenter, Pi.add_apply]
  omega

theorem spineBox_dist_root {d K t : ℕ} (ht : 64 ≤ t) (axis : Fin d) (k : Fin K)
    {x y : Vertex d} (hx : x ∈ centeredBox d ((t - 1) / 32)) (hy : y ∈ spineBox t axis k) :
    ((t / 64 : ℕ) : ℝ) ≤ dist x y := by
  have hx' := (mem_centeredBox.mp hx axis).2
  have hy' := (spineBox_axis_bounds hy).1
  have hr : 256 * spineRadius K t ≤ t :=
    (Nat.le_mul_of_pos_right _ (Nat.succ_pos K)).trans (spineRadius_budget K t)
  have hr' : 256 * (spineRadius K t : ℤ) ≤ (t : ℤ) := by exact_mod_cast hr
  have hn : 0 ≤ 4 * (spineRadius K t : ℤ) * (k.val : ℤ) := by positivity
  have habs := neg_le_abs (x axis - y axis)
  have hgap : ((t / 64 : ℕ) : ℤ) ≤ |x axis - y axis| := by omega
  refine le_trans ?_ (dist_le_pi_dist x y axis)
  rw [Int.dist_eq]
  simpa only [Int.cast_natCast, Int.cast_abs, Int.cast_sub] using
    (Int.cast_le.mpr hgap : (((t / 64 : ℕ) : ℤ) : ℝ) ≤ ((|x axis - y axis| : ℤ) : ℝ))

theorem spineBoxes_dist_of_lt {d K t : ℕ} (axis : Fin d) {k l : Fin K} (hkl : k < l)
    {x y : Vertex d} (hx : x ∈ spineBox t axis k) (hy : y ∈ spineBox t axis l) :
    2 * (spineRadius K t : ℝ) ≤ dist x y := by
  have hxy := (spineBox_axis_bounds hx).2
  have hyx := (spineBox_axis_bounds hy).1
  have hmul : 4 * spineRadius K t * (k.val + 1) ≤ 4 * spineRadius K t * l.val :=
    Nat.mul_le_mul_left _ (by omega)
  have hmul' : 4 * (spineRadius K t : ℤ) * (k.val : ℤ) + 4 * (spineRadius K t : ℤ) ≤
      4 * (spineRadius K t : ℤ) * (l.val : ℤ) := by
    exact_mod_cast (by simpa only [Nat.mul_add, Nat.mul_one] using hmul :
      4 * spineRadius K t * k.val + 4 * spineRadius K t ≤ 4 * spineRadius K t * l.val)
  have habs := neg_le_abs (x axis - y axis)
  have hgap : 2 * (spineRadius K t : ℤ) ≤ |x axis - y axis| := by omega
  refine le_trans ?_ (dist_le_pi_dist x y axis)
  rw [Int.dist_eq]
  simpa only [Int.cast_natCast, Int.cast_abs, Int.cast_sub, Int.cast_mul, Int.cast_ofNat] using
    (Int.cast_le.mpr hgap : ((2 * (spineRadius K t : ℤ) : ℤ) : ℝ) ≤
      ((|x axis - y axis| : ℤ) : ℝ))

theorem spineBox_dist_entryBox {d K t : ℕ} (ht : 64 ≤ t) (axis : Fin d) (k : Fin K)
    {f : Fin d × Bool} {pl branch : Bool} {x y : Vertex d}
    (hx : x ∈ spineBox t axis k) (hy : y ∈ entryLegBox t f pl branch) :
    ((t / 16 : ℕ) : ℝ) ≤ dist x y := by
  have hax := (entryLegBox_height_bounds hy).1
  obtain ⟨i, s⟩ := f
  have hxb := mem_centeredBox.mp (spineBox_subset_inner_cube ht axis k hx) i
  have hp := le_abs_self (x i - y i)
  have hn := neg_le_abs (x i - y i)
  have hgap : ((t / 16 : ℕ) : ℤ) ≤ |x i - y i| := by
    cases s <;> cases branch <;> simp [faceHeight, entryBoxHeight, legBoxRadius] at hax <;> omega
  refine le_trans ?_ (dist_le_pi_dist x y i)
  rw [Int.dist_eq]
  simpa only [Int.cast_natCast, Int.cast_abs, Int.cast_sub] using
    (Int.cast_le.mpr hgap : (((t / 16 : ℕ) : ℤ) : ℝ) ≤ ((|x i - y i| : ℤ) : ℝ))

end NearCritical.SplitCrossDirect
