module

public import NearCritical.SplitCrossEntryBoxes
public import NearCritical.SplitCrossRectangleLower

/-! A single translated rectangle joins the two branch boxes on each leg.
Its expanded rectangle stays inside the split corridor even as it passes
through the typical-cube face. -/
@[expose] public section
noncomputable section

namespace NearCritical.SplitCrossDirect

open Section10 MeasureTheory
open scoped Classical

theorem cast_nat_halfSide_lower (t : ℕ) (ht : 1 ≤ t) :
    (t : ℝ) / 2 - 1 ≤ (((t - 1) / 2 : ℕ) : ℝ) := by
  have h : (t : ℝ) ≤ 2 * (((t - 1) / 2 : ℕ) : ℝ) + 2 := by
    exact_mod_cast (show t ≤ 2 * ((t - 1) / 2) + 2 by omega)
  linarith

/-- The full transverse strip between heights zero and the target is in the
union of the cube and the corresponding beyond-cube region. -/
theorem mem_splitCorridor_of_strip {d t : ℕ} (ht : 64 ≤ t)
    (f : Fin d × Bool) (pl : Bool) {v : Vertex d}
    (hlo : 0 ≤ faceHeight f v)
    (hhi : faceHeight f v ≤ (((t - 1) / 2 : ℕ) : ℤ) + (t : ℤ))
    (htr : ∀ j, j ≠ f.1 → splitRange t pl (v j)) :
    v ∈ splitCorridor t f pl t := by
  have hN := cast_nat_halfSide_lower t (by omega)
  have htR : (64 : ℝ) ≤ t := by exact_mod_cast ht
  have htrans (j : Fin d) (hj : j ≠ f.1) :
      -(((t - 1) / 2 : ℕ) : ℤ) ≤ v j ∧ v j ≤ (((t - 1) / 2 : ℕ) : ℤ) := by
    have hr := htr j hj
    have hh : -(((t - 1) / 2 : ℕ) : ℝ) ≤ (v j : ℝ) ∧
        (v j : ℝ) ≤ (((t - 1) / 2 : ℕ) : ℝ) := by
      cases pl <;> simp [splitRange] at hr <;> constructor <;> linarith [hr.1, hr.2]
    have hcast : (v j : ℝ) ≤ ((((t - 1) / 2 : ℕ) : ℤ) : ℝ) := by
      simpa only [Int.cast_natCast] using hh.2
    exact ⟨by exact_mod_cast hh.1, Int.cast_le.mp hcast⟩
  by_cases h : faceHeight f v ≤ (((t - 1) / 2 : ℕ) : ℤ)
  · refine Finset.mem_union_left _ ((mem_typicalCube_iff_int (by omega) 0 v).mpr ?_)
    intro j
    simp only [Pi.zero_apply, sub_zero]
    by_cases hj : j = f.1
    · subst j
      obtain ⟨i, s⟩ := f
      cases s <;> simp [faceHeight] at h hlo ⊢ <;> omega
    · exact htrans j hj
  · refine Finset.mem_union_right _ (Finset.mem_filter.mpr
      ⟨mem_centeredBox.mpr ?_, lt_of_not_ge h, htr⟩)
    intro j
    by_cases hj : j = f.1
    · subst j
      obtain ⟨i, s⟩ := f
      cases s <;> simp [faceHeight] at hhi hlo ⊢ <;> omega
    · have hb := htrans j hj
      omega

/-- A branch window inside either the entry box or the exterior far box. -/
def legBranchBox {d : ℕ} (t : ℕ) (f : Fin d × Bool) (pl inside : Bool) :
    Finset (Vertex d) :=
  translateSites (if inside then legBoxCenter t f pl (entryBoxHeight t true)
    else farLegBoxCenter t f pl) (centeredBox d (t / 1024))

theorem legBranchBox_card {d : ℕ} (t : ℕ) (f : Fin d × Bool) (pl inside : Bool) :
    (legBranchBox t f pl inside).card = (2 * (t / 1024) + 1) ^ d := by
  rw [legBranchBox, card_translateSites, card_centeredBox_exact]

theorem legBranchBox_axial {d t : ℕ} (ht : 4096 ≤ t)
    {f : Fin d × Bool} {pl inside : Bool} {x : Vertex d}
    (hx : x ∈ legBranchBox t f pl inside) :
    let c : ℝ := if inside then 3 / 8 else 95 / 64
    c * (t : ℝ) - (t : ℝ) / 512 ≤ (faceHeight f x : ℝ) ∧
      (faceHeight f x : ℝ) ≤ c * (t : ℝ) + (t : ℝ) / 512 := by
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨i, s⟩ := f
  have hz' := mem_centeredBox.mp hz i
  have hrad : (((t / 1024 : ℕ) : ℤ) : ℝ) ≤ (t : ℝ) / 1024 := by
    simpa only [Int.cast_natCast, Nat.cast_ofNat] using
      (Nat.cast_div_le (α := ℝ) (m := t) (n := 1024))
  have hzl : -(((t / 1024 : ℕ) : ℤ) : ℝ) ≤ (z i : ℝ) := by exact_mod_cast hz'.1
  have hzu : (z i : ℝ) ≤ (((t / 1024 : ℕ) : ℤ) : ℝ) := by exact_mod_cast hz'.2
  have htR : (4096 : ℝ) ≤ t := by exact_mod_cast ht
  have hEntryLo : 3 * (t : ℝ) - 7 ≤ 8 * (((3 * (t : ℤ)) / 8 : ℤ) : ℝ) := by
    exact_mod_cast (show 3 * (t : ℤ) - 7 ≤ 8 * ((3 * (t : ℤ)) / 8) by omega)
  have hEntryHi : 8 * (((3 * (t : ℤ)) / 8 : ℤ) : ℝ) ≤ 3 * (t : ℝ) := by
    exact_mod_cast (show 8 * ((3 * (t : ℤ)) / 8) ≤ 3 * (t : ℤ) by omega)
  have hNlo := cast_nat_halfSide_lower t (by omega)
  have hNhi : 2 * (((t - 1) / 2 : ℕ) : ℝ) ≤ t := by
    exact_mod_cast (show 2 * ((t - 1) / 2) ≤ t by omega)
  have hrlo : (t : ℝ) - 63 ≤ 64 * ((t / 64 : ℕ) : ℝ) := by
    have h : (t : ℝ) ≤ 64 * ((t / 64 : ℕ) : ℝ) + 63 := by
      exact_mod_cast (show t ≤ 64 * (t / 64) + 63 by omega)
    linarith
  have hrhi : 64 * ((t / 64 : ℕ) : ℝ) ≤ t := by
    exact_mod_cast (show 64 * (t / 64) ≤ t by omega)
  cases inside <;> cases s <;>
    simp only [legBoxCenter, farLegBoxCenter, entryBoxHeight, legBoxRadius, faceHeight,
      Prod.fst, Prod.snd, Bool.false_eq_true, if_false, if_true, Pi.add_apply,
      Int.cast_add, Int.cast_sub, Int.cast_neg, Int.cast_natCast] <;>
    constructor <;> linarith

theorem legBranchBox_transverse {d t : ℕ} (ht : 4096 ≤ t)
    {f : Fin d × Bool} {pl inside : Bool} {x : Vertex d}
    (hx : x ∈ legBranchBox t f pl inside) (j : Fin d) (hj : j ≠ f.1) :
    let c : ℝ := if pl then 3 / 16 else -(3 / 16)
    c * (t : ℝ) - (t : ℝ) / 512 ≤ (x j : ℝ) ∧
      (x j : ℝ) ≤ c * (t : ℝ) + (t : ℝ) / 512 := by
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
  have hz' := mem_centeredBox.mp hz j
  have hrad : (((t / 1024 : ℕ) : ℤ) : ℝ) ≤ (t : ℝ) / 1024 := by
    simpa only [Int.cast_natCast, Nat.cast_ofNat] using
      (Nat.cast_div_le (α := ℝ) (m := t) (n := 1024))
  have hzl : -(((t / 1024 : ℕ) : ℤ) : ℝ) ≤ (z j : ℝ) := by exact_mod_cast hz'.1
  have hzu : (z j : ℝ) ≤ (((t / 1024 : ℕ) : ℤ) : ℝ) := by exact_mod_cast hz'.2
  have htR : (4096 : ℝ) ≤ t := by exact_mod_cast ht
  have hcl : 3 * (t : ℝ) - 15 ≤ 16 * (((3 * (t : ℤ)) / 16 : ℤ) : ℝ) := by
    exact_mod_cast (show 3 * (t : ℤ) - 15 ≤ 16 * ((3 * (t : ℤ)) / 16) by omega)
  have hcu : 16 * (((3 * (t : ℤ)) / 16 : ℤ) : ℝ) ≤ 3 * (t : ℝ) := by
    exact_mod_cast (show 16 * ((3 * (t : ℤ)) / 16) ≤ 3 * (t : ℤ) by omega)
  cases inside <;> cases pl <;>
    simp [legBoxCenter, farLegBoxCenter, hj, Pi.add_apply, Int.cast_add, Int.cast_neg] <;>
    constructor <;> linarith

/-- The short backward and long forward extents are exchanged on negative faces. -/
def legNeckLower {d : ℕ} (f : Fin d × Bool) (j : Fin d) : ℝ :=
  if j = f.1 then (if f.2 then 1 / 16 else 143 / 128) else 1 / 64

def legNeckUpper {d : ℕ} (f : Fin d × Bool) (j : Fin d) : ℝ :=
  if j = f.1 then (if f.2 then 143 / 128 else 1 / 16) else 1 / 64

/-- The enlarged rectangle in the translated CH20 lower estimate. -/
def legNeckRectangle {d : ℕ} (t : ℕ) (f : Fin d × Bool) (x : Vertex d) : Set (Vertex d) :=
  splitLegExpandedRectangle (legNeckLower f) (legNeckUpper f) t x

theorem legNeck_endpoint_mem {d t : ℕ} (ht : 4096 ≤ t)
    (f : Fin d × Bool) (pl : Bool) {x y : Vertex d}
    (hx : x ∈ legBranchBox t f pl true) (hy : y ∈ legBranchBox t f pl false) :
    y - x ∈ section8Rectangle (legNeckLower f) (legNeckUpper f) t := by
  have hxA := legBranchBox_axial ht hx
  have hyA := legBranchBox_axial ht hy
  have htR : (4096 : ℝ) ≤ t := by exact_mod_cast ht
  intro j
  by_cases hj : j = f.1
  · subst j
    obtain ⟨i, s⟩ := f
    cases s <;> simp [legNeckLower, legNeckUpper, faceHeight, Pi.sub_apply, Int.cast_neg,
      Int.cast_sub] at hxA hyA ⊢ <;> constructor <;> linarith [hxA.1, hxA.2, hyA.1, hyA.2]
  · have hxT := legBranchBox_transverse ht hx j hj
    have hyT := legBranchBox_transverse ht hy j hj
    cases pl <;> simp [legNeckLower, legNeckUpper, hj, Pi.sub_apply, Int.cast_sub] at hxT hyT ⊢ <;>
      constructor <;> linarith [hxT.1, hxT.2, hyT.1, hyT.2]

theorem legNeckRectangle_subset_corridor {d t : ℕ} (ht : 4096 ≤ t)
    (f : Fin d × Bool) (pl : Bool) {x : Vertex d}
    (hx : x ∈ legBranchBox t f pl true) :
    legNeckRectangle t f x ⊆ (splitCorridor t f pl t : Set (Vertex d)) := by
  rintro _ ⟨z, hz, rfl⟩
  have hxA := legBranchBox_axial ht hx
  have htR : (4096 : ℝ) ≤ t := by exact_mod_cast ht
  have hN := cast_nat_halfSide_lower t (by omega)
  have hax : (0 : ℝ) ≤ (faceHeight f (x + z) : ℝ) ∧
      (faceHeight f (x + z) : ℝ) ≤ (((t - 1) / 2 : ℕ) : ℝ) + (t : ℝ) := by
    obtain ⟨i, s⟩ := f
    have hzA := hz i
    cases s <;> simp [legNeckLower, legNeckUpper, faceHeight, Pi.add_apply, Int.cast_neg,
      Int.cast_add] at hxA hzA ⊢ <;>
      constructor <;> linarith [hxA.1, hxA.2, hzA.1, hzA.2]
  refine mem_splitCorridor_of_strip (by omega) f pl
    (by exact_mod_cast hax.1) ?_ ?_
  · let top : ℤ := (((t - 1) / 2 : ℕ) : ℤ) + (t : ℤ)
    change faceHeight f (x + z) ≤ top
    have hcast : (faceHeight f (x + z) : ℝ) ≤ (top : ℝ) := by
      simpa only [top, Int.cast_add, Int.cast_natCast] using hax.2
    exact Int.cast_le.mp hcast
  intro j hj
  have hxT := legBranchBox_transverse ht hx j hj
  have hzT := hz j
  cases pl <;> simp [legNeckLower, legNeckUpper, hj, splitRange, Pi.add_apply, Int.cast_add]
    at hxT hzT ⊢ <;> constructor <;> linarith [hxT.1, hxT.2, hzT.1, hzT.2]

/-- The entry-to-exterior edge has its full interior two-point power inside
one admissible rectangle. -/
theorem legNeck_connection_lower {d : ℕ} (hd : 2 ≤ d)
    (lower : RestrictedRectangleLowerInput d) :
    ∃ b : ℝ, 0 < b ∧ ∀ (t : ℕ), 4096 ≤ t → ∀ (f : Fin d × Bool) (pl : Bool)
      (x y : Vertex d), x ∈ legBranchBox t f pl true → y ∈ legBranchBox t f pl false →
      b * (2 * (t : ℝ)) ^ ((2 : ℝ) - (d : ℝ)) ≤
        (percolation d (criticalPoint d)).real (connectionToSetEvent (legNeckRectangle t f x) x {y}) := by
  have hL (f : Fin d × Bool) (j : Fin d) : 0 < legNeckLower f j ∧ legNeckLower f j ≤ 2 := by
    unfold legNeckLower
    split_ifs <;> norm_num
  have hU (f : Fin d × Bool) (j : Fin d) : 0 < legNeckUpper f j ∧ legNeckUpper f j ≤ 2 := by
    unfold legNeckUpper
    split_ifs <;> norm_num
  obtain ⟨b, hb, h⟩ := splitLeg_rectangle_connection_lower hd lower
    legNeckLower legNeckUpper hL hU
  refine ⟨b, hb, ?_⟩
  intro t ht f pl x y hx hy
  exact h t (by omega) f x y (legNeck_endpoint_mem ht f pl hx hy)

end NearCritical.SplitCrossDirect
