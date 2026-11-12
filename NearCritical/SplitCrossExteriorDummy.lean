module

public import NearCritical.SplitCrossNeck

/-! The exterior branch-to-dummy edge, contained in a single rectangle
entirely beyond the cube face. -/
@[expose] public section
noncomputable section

namespace NearCritical.SplitCrossDirect

open Section10 MeasureTheory
open scoped Classical

private theorem dummyBox_axial {d t : ℕ} (ht : 4096 ≤ t)
    {f : Fin d × Bool} {pl : Bool} {y : Vertex d}
    (hy : y ∈ translateSites (interiorLegBoxCenter t f pl) (centeredBox d (legBoxRadius t))) :
    (t : ℝ) - (t : ℝ) / 32 ≤ (faceHeight f y : ℝ) ∧
      (faceHeight f y : ℝ) ≤ (t : ℝ) + (t : ℝ) / 32 := by
  let h : ℤ := (((t - 1) / 2 : ℕ) : ℤ) + ((t / 2 : ℕ) : ℤ)
  have hb := legBox_height_bounds f pl h hy
  have hl : ((h - (legBoxRadius t : ℤ) : ℤ) : ℝ) ≤ (faceHeight f y : ℝ) :=
    Int.cast_le.mpr hb.1
  have hu : (faceHeight f y : ℝ) ≤ ((h + (legBoxRadius t : ℤ) : ℤ) : ℝ) :=
    Int.cast_le.mpr hb.2
  simp only [h, legBoxRadius, Int.cast_add, Int.cast_sub, Int.cast_natCast] at hl hu
  have hN := cast_nat_halfSide_lower t (by omega)
  have hNhi : 2 * (((t - 1) / 2 : ℕ) : ℝ) ≤ t := by
    exact_mod_cast (show 2 * ((t - 1) / 2) ≤ t by omega)
  have hH : (t : ℝ) ≤ 2 * ((t / 2 : ℕ) : ℝ) + 1 := by
    exact_mod_cast (show t ≤ 2 * (t / 2) + 1 by omega)
  have hHhi : 2 * ((t / 2 : ℕ) : ℝ) ≤ t := by
    exact_mod_cast (show 2 * (t / 2) ≤ t by omega)
  have hr : ((t / 64 : ℕ) : ℝ) ≤ (t : ℝ) / 64 := by
    simpa only [Nat.cast_ofNat] using (Nat.cast_div_le (α := ℝ) (m := t) (n := 64))
  have htR : (4096 : ℝ) ≤ t := by exact_mod_cast ht
  constructor <;> linarith

private theorem dummyBox_transverse {d t : ℕ} (ht : 4096 ≤ t)
    {f : Fin d × Bool} {pl : Bool} {y : Vertex d}
    (hy : y ∈ translateSites (interiorLegBoxCenter t f pl) (centeredBox d (legBoxRadius t)))
    (j : Fin d) (hj : j ≠ f.1) :
    let c : ℝ := if pl then 3 / 16 else -(3 / 16)
    c * (t : ℝ) - (t : ℝ) / 32 ≤ (y j : ℝ) ∧
      (y j : ℝ) ≤ c * (t : ℝ) + (t : ℝ) / 32 := by
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
  have hz' := mem_centeredBox.mp hz j
  have hzlo : -(((legBoxRadius t : ℕ) : ℤ) : ℝ) ≤ (z j : ℝ) := by exact_mod_cast hz'.1
  have hzhi : (z j : ℝ) ≤ (((legBoxRadius t : ℕ) : ℤ) : ℝ) := Int.cast_le.mpr hz'.2
  simp only [legBoxRadius, Int.cast_natCast] at hzlo hzhi
  have hr : ((t / 64 : ℕ) : ℝ) ≤ (t : ℝ) / 64 := by
    simpa only [Nat.cast_ofNat] using (Nat.cast_div_le (α := ℝ) (m := t) (n := 64))
  have htR : (4096 : ℝ) ≤ t := by exact_mod_cast ht
  have hcL : 3 * (t : ℝ) - 15 ≤ 16 * (((3 * (t : ℤ)) / 16 : ℤ) : ℝ) := by
    exact_mod_cast (show 3 * (t : ℤ) - 15 ≤ 16 * ((3 * (t : ℤ)) / 16) by omega)
  have hcU : 16 * (((3 * (t : ℤ)) / 16 : ℤ) : ℝ) ≤ 3 * (t : ℝ) := by
    exact_mod_cast (show 16 * ((3 * (t : ℤ)) / 16) ≤ 3 * (t : ℤ) by omega)
  cases pl <;> simp [interiorLegBoxCenter, legBoxCenter, hj, Pi.add_apply, Int.cast_add,
    Int.cast_neg] <;> constructor <;> linarith

def exteriorDummyLower {d : ℕ} (f : Fin d × Bool) (j : Fin d) : ℝ :=
  if j = f.1 then (if f.2 then 17 / 32 else 1 / 128) else 5 / 128

def exteriorDummyUpper {d : ℕ} (f : Fin d × Bool) (j : Fin d) : ℝ :=
  if j = f.1 then (if f.2 then 1 / 128 else 17 / 32) else 5 / 128

def exteriorDummyRectangle {d : ℕ} (t : ℕ) (f : Fin d × Bool) (x : Vertex d) :
    Set (Vertex d) :=
  splitLegExpandedRectangle (exteriorDummyLower f) (exteriorDummyUpper f) t x

theorem exteriorDummy_endpoint_mem {d t : ℕ} (ht : 4096 ≤ t)
    (f : Fin d × Bool) (pl : Bool) {x y : Vertex d}
    (hx : x ∈ legBranchBox t f pl false)
    (hy : y ∈ translateSites (interiorLegBoxCenter t f pl) (centeredBox d (legBoxRadius t))) :
    y - x ∈ section8Rectangle (exteriorDummyLower f) (exteriorDummyUpper f) t := by
  have hxA := legBranchBox_axial ht hx
  have hyA := dummyBox_axial ht hy
  have htR : (4096 : ℝ) ≤ t := by exact_mod_cast ht
  intro j
  by_cases hj : j = f.1
  · subst j
    obtain ⟨i, s⟩ := f
    cases s <;> simp [exteriorDummyLower, exteriorDummyUpper, faceHeight, Pi.sub_apply,
      Int.cast_neg, Int.cast_sub] at hxA hyA ⊢ <;>
      constructor <;> linarith [hxA.1, hxA.2, hyA.1, hyA.2]
  · have hxT := legBranchBox_transverse ht hx j hj
    have hyT := dummyBox_transverse ht hy j hj
    cases pl <;> simp [exteriorDummyLower, exteriorDummyUpper, hj, Pi.sub_apply, Int.cast_sub]
      at hxT hyT ⊢ <;> constructor <;> linarith [hxT.1, hxT.2, hyT.1, hyT.2]

theorem exteriorDummyRectangle_subset_beyond {d t : ℕ} (ht : 4096 ≤ t)
    (f : Fin d × Bool) (pl : Bool) {x : Vertex d}
    (hx : x ∈ legBranchBox t f pl false) :
    exteriorDummyRectangle t f x ⊆ (splitBeyond t f pl t : Set (Vertex d)) := by
  rintro _ ⟨z, hz, rfl⟩
  have hxA := legBranchBox_axial ht hx
  have htR : (4096 : ℝ) ≤ t := by exact_mod_cast ht
  have hN := cast_nat_halfSide_lower t (by omega)
  have hNhi : 2 * (((t - 1) / 2 : ℕ) : ℝ) ≤ t := by
    exact_mod_cast (show 2 * ((t - 1) / 2) ≤ t by omega)
  have hax : (((t - 1) / 2 : ℕ) : ℝ) < (faceHeight f (x + z) : ℝ) ∧
      (faceHeight f (x + z) : ℝ) ≤ (((t - 1) / 2 : ℕ) : ℝ) + (t : ℝ) := by
    obtain ⟨i, s⟩ := f
    have hzA := hz i
    cases s <;> simp [exteriorDummyLower, exteriorDummyUpper, faceHeight, Pi.add_apply,
      Int.cast_neg, Int.cast_add] at hxA hzA ⊢ <;>
      constructor <;> linarith [hxA.1, hxA.2, hzA.1, hzA.2]
  have hbot : (((t - 1) / 2 : ℕ) : ℤ) < faceHeight f (x + z) := by
    have hcast : ((((t - 1) / 2 : ℕ) : ℤ) : ℝ) < (faceHeight f (x + z) : ℝ) := by
      simpa only [Int.cast_natCast] using hax.1
    exact Int.cast_lt.mp hcast
  let top : ℤ := (((t - 1) / 2 : ℕ) : ℤ) + (t : ℤ)
  have htop : faceHeight f (x + z) ≤ top := by
    have hcast : (faceHeight f (x + z) : ℝ) ≤ (top : ℝ) := by
      simpa only [top, Int.cast_add, Int.cast_natCast] using hax.2
    exact Int.cast_le.mp hcast
  have htr (j : Fin d) (hj : j ≠ f.1) : splitRange t pl ((x + z) j) := by
    have hxT := legBranchBox_transverse ht hx j hj
    have hzT := hz j
    cases pl <;> simp [exteriorDummyLower, exteriorDummyUpper, hj, splitRange, Pi.add_apply,
      Int.cast_add] at hxT hzT ⊢ <;> constructor <;> linarith [hxT.1, hxT.2, hzT.1, hzT.2]
  have hall := mem_splitCorridor_of_strip (by omega) f pl
    (show 0 ≤ faceHeight f (x + z) by omega) htop htr
  rcases Finset.mem_union.mp hall with hc | hb
  · have hcoord := (mem_typicalCube_iff_int (by omega) 0 (x + z)).mp hc f.1
    obtain ⟨i, s⟩ := f
    cases s <;> simp [faceHeight, Pi.zero_apply] at hbot hcoord <;> omega
  · exact hb

theorem exteriorDummy_connection_lower {d : ℕ} (hd : 2 ≤ d)
    (lower : RestrictedRectangleLowerInput d) :
    ∃ b : ℝ, 0 < b ∧ ∀ (t : ℕ), 4096 ≤ t → ∀ (f : Fin d × Bool) (pl : Bool)
      (x y : Vertex d), x ∈ legBranchBox t f pl false →
      y ∈ translateSites (interiorLegBoxCenter t f pl) (centeredBox d (legBoxRadius t)) →
      b * (2 * (t : ℝ)) ^ ((2 : ℝ) - (d : ℝ)) ≤ (percolation d (criticalPoint d)).real
        (connectionToSetEvent (exteriorDummyRectangle t f x) x {y}) := by
  have hlo (f : Fin d × Bool) (j : Fin d) : 0 < exteriorDummyLower f j ∧ exteriorDummyLower f j ≤ 2 := by
    unfold exteriorDummyLower
    split_ifs <;> norm_num
  have hhi (f : Fin d × Bool) (j : Fin d) : 0 < exteriorDummyUpper f j ∧ exteriorDummyUpper f j ≤ 2 := by
    unfold exteriorDummyUpper
    split_ifs <;> norm_num
  obtain ⟨b, hb, h⟩ := splitLeg_rectangle_connection_lower hd lower
    exteriorDummyLower exteriorDummyUpper hlo hhi
  refine ⟨b, hb, ?_⟩
  intro t ht f pl x y hx hy
  exact h t (by omega) f x y (exteriorDummy_endpoint_mem ht f pl hx hy)

end NearCritical.SplitCrossDirect
