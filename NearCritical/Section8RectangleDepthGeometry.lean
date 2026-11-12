module
public import NearCritical.Section8RectangleLowerInput
public import NearCritical.Section8BoundaryKernels
public import Mathlib.Data.Int.Interval

/-! Exact lattice representation and nearest-wall comparison for real rectangles. -/
@[expose] public section
noncomputable section
namespace NearCritical.Section8
open Set
open scoped Classical

/-- Lattice points of the source's closed real-coordinate rectangle. -/
def sourceRectangleFinset {d : ℕ} (α β : Fin d → ℝ) (n : ℕ) : Finset (Vertex d) :=
  Fintype.piFinset fun i => Finset.Icc ⌈-α i*(n : ℝ)⌉ ⌊β i*(n : ℝ)⌋

theorem sourceRectangleFinset_coe {d : ℕ} (α β : Fin d → ℝ) (n : ℕ) :
    (sourceRectangleFinset α β n : Set (Vertex d)) = section8Rectangle α β n := by
  ext x
  simp only [Finset.mem_coe,sourceRectangleFinset,Fintype.mem_piFinset,
    Finset.mem_Icc,Int.ceil_le,Int.le_floor,section8Rectangle,Set.mem_setOf_eq]

/-- The literal minimum of the real upper/lower coordinate margins. -/
def sourceRectangleDepth {d : ℕ} (hd : 1 ≤ d) (α β : Fin d → ℝ)
    (n : ℕ) (x : Vertex d) : ℝ :=
  (Finset.univ : Finset (Fin d)).inf'
    ⟨⟨0,by omega⟩,Finset.mem_univ _⟩
    (fun i => min (β i*(n : ℝ)-(x i : ℝ)) ((x i : ℝ)+α i*(n : ℝ)))

/-- Rounding inward preserves every lattice point and can only reduce depth.
No integrality of the real rectangle's aspect ratios is assumed. -/
theorem sourceRectangle_nearest_halfSpace {d : ℕ} (hd : 1 ≤ d)
    (α β : Fin d → ℝ) (n : ℕ) (x : Vertex d)
    (hx : x ∈ section8Rectangle α β n) :
    ∃ (i : Fin d) (wall : ℤ) (positive : Bool),
      section8Rectangle α β n ⊆ coordinateHalfSpace i wall positive ∧
      coordinateDepth i wall positive x ≤ sourceRectangleDepth hd α β n x := by
  let f := fun i : Fin d => min (β i*(n : ℝ)-(x i : ℝ)) ((x i : ℝ)+α i*(n : ℝ))
  have hne : (Finset.univ : Finset (Fin d)).Nonempty :=
    ⟨⟨0,by omega⟩,Finset.mem_univ _⟩
  obtain ⟨i,hi,hmin⟩ := Finset.exists_min_image Finset.univ f hne
  have hdepth : f i ≤ sourceRectangleDepth hd α β n x := by
    exact Finset.le_inf' _ _ hmin
  by_cases hside : β i*(n : ℝ)-(x i : ℝ) ≤ (x i : ℝ)+α i*(n : ℝ)
  · refine ⟨i,⌊β i*(n : ℝ)⌋,false,?_,?_⟩
    · intro y hy
      have hwall : y i ≤ ⌊β i*(n : ℝ)⌋ := Int.le_floor.mpr (hy i).2
      have hwallR : (y i : ℝ) ≤ (⌊β i*(n : ℝ)⌋ : ℝ) := by exact_mod_cast hwall
      change 0 ≤ coordinateDepth i ⌊β i*(n : ℝ)⌋ false y
      simpa [coordinateDepth] using sub_nonneg.mpr hwallR
    · have hfloor := Int.floor_le (β i*(n : ℝ))
      have hf : f i = β i*(n : ℝ)-(x i : ℝ) := min_eq_left hside
      rw [hf] at hdepth
      simp only [coordinateDepth,Bool.false_eq_true,ite_false]
      linarith
  · refine ⟨i,⌈-α i*(n : ℝ)⌉,true,?_,?_⟩
    · intro y hy
      have hwall : ⌈-α i*(n : ℝ)⌉ ≤ y i := Int.ceil_le.mpr (hy i).1
      have hwallR : (⌈-α i*(n : ℝ)⌉ : ℝ) ≤ (y i : ℝ) := by exact_mod_cast hwall
      change 0 ≤ coordinateDepth i ⌈-α i*(n : ℝ)⌉ true y
      simpa [coordinateDepth] using sub_nonneg.mpr hwallR
    · have hceil := Int.le_ceil (-α i*(n : ℝ))
      have hf : f i = (x i : ℝ)+α i*(n : ℝ) := min_eq_right (le_of_not_ge hside)
      rw [hf] at hdepth
      simp only [coordinateDepth,ite_true]
      linarith

end NearCritical.Section8
