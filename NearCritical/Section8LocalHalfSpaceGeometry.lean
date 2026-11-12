module
public import NearCritical.Section8HeartAnnulus
public import NearCritical.HalfSpaceLastVisit

/-! Discrete local half-space geometry with the inner boundary retained.
The strict radius condition repairs source eq.local_halfspace_match. -/
@[expose] public section
noncomputable section
namespace NearCritical.Section8
open scoped Classical

/-- Exact vertex boundary of the inclusive integer cube, including radius zero. -/
theorem mem_centeredBox_boundary_iff {d c : ℕ} (z : Vertex d) :
    z ∈ boundarySites (centeredBox d c) ↔
      z ∈ centeredBox d c ∧ ∃ i : Fin d, z i = (c : ℤ) ∨ z i = -(c : ℤ) := by
  constructor
  · intro hz
    obtain ⟨hzC,y,hyC,hzy⟩ := Finset.mem_filter.mp hz
    refine ⟨hzC,?_⟩
    have hout : ∃ i : Fin d, ¬ (-(c : ℤ) ≤ y i ∧ y i ≤ (c : ℤ)) := by
      simpa only [mem_centeredBox,not_forall] using hyC
    obtain ⟨i,hi⟩ := hout
    have hzb := mem_centeredBox.mp hzC i
    have hstep := openGraph_adj_height_bounds hzy i
    exact ⟨i,by omega⟩
  · rintro ⟨hzC,i,hi | hi⟩
    · refine Finset.mem_filter.mpr ⟨hzC,bondTip (z,i),?_,?_⟩
      · intro hy
        have hb := (mem_centeredBox.mp hy i).2
        simp only [bondTip,Function.update_self] at hb
        omega
      · exact ⟨(z,i),rfl,Or.inl ⟨rfl,rfl⟩⟩
    · let y : Vertex d := Function.update z i (z i-1)
      have htip : bondTip (y,i) = z := by
        ext j
        by_cases hj : j = i
        · subst j
          simp [bondTip,y]
        · simp [bondTip,y,Function.update_of_ne hj]
      refine Finset.mem_filter.mpr ⟨hzC,y,?_,?_⟩
      · intro hy
        have hb := (mem_centeredBox.mp hy i).1
        dsimp [y] at hb
        simp only [Function.update_self] at hb
        omega
      · exact ⟨(y,i),rfl,Or.inr ⟨rfl,htip.symm⟩⟩

/-- A local cube of radius t STRICTLY below the transverse face gap s sees
only the chosen positive face of the inner cube. The annulus is the actual
Q\(H\boundarySites H), and Q membership is explicit. -/
theorem local_annulus_iff_halfSpace {d c : ℕ} (Q : Finset (Vertex d))
    (i : Fin d) (w z : Vertex d) (r s t : ℤ)
    (hr : 0 ≤ r) (ht : 0 ≤ t) (hts : t < s) (hsc : s ≤ (c : ℤ))
    (hface : w i = (c : ℤ)+r)
    (htransverse : ∀ j : Fin d, j ≠ i → |w j| ≤ (c : ℤ)-s)
    (hlocal : ∀ j : Fin d, |z j-w j| ≤ t) (hzQ : z ∈ Q) :
    z ∈ heartAnnulus Q (centeredBox d c) ↔ (c : ℤ) ≤ z i := by
  have hzi : -(c : ℤ) < z i := by
    have hh := abs_le.mp (hlocal i)
    omega
  have hother (j : Fin d) (hj : j ≠ i) : -(c : ℤ) < z j ∧ z j < (c : ℤ) := by
    have hw := abs_le.mp (htransverse j hj)
    have hz := abs_le.mp (hlocal j)
    constructor <;> omega
  constructor
  · intro hz
    by_contra hn
    have hzilt : z i < (c : ℤ) := lt_of_not_ge hn
    have hzC : z ∈ centeredBox d c := by
      apply mem_centeredBox.mpr
      intro j
      by_cases hj : j = i
      · subst j
        exact ⟨hzi.le,hzilt.le⟩
      · exact ⟨(hother j hj).1.le,(hother j hj).2.le⟩
    have hzB := heartAnnulus_mem_heart_boundary Q (centeredBox d c) hz hzC
    obtain ⟨_,j,hj | hj⟩ := (mem_centeredBox_boundary_iff z).mp hzB
    · by_cases he : j = i
      · subst j
        omega
      · have hh := (hother j he).2
        omega
    · by_cases he : j = i
      · subst j
        omega
      · have hh := (hother j he).1
        omega
  · intro hziC
    apply Finset.mem_sdiff.mpr
    refine ⟨hzQ,?_⟩
    intro hzinterior
    obtain ⟨hzC,hzB⟩ := Finset.mem_sdiff.mp hzinterior
    have hh := (mem_centeredBox.mp hzC i).2
    have he : z i = (c : ℤ) := le_antisymm hh hziC
    exact hzB ((mem_centeredBox_boundary_iff z).mpr ⟨hzC,i,Or.inl he⟩)

end NearCritical.Section8
