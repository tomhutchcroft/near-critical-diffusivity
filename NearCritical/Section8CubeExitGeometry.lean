module
public import NearCritical.Section8FiniteExitSplit

/-! The actual first-exit interface of a domain cut by a translated cube. -/
@[expose] public section
noncomputable section
namespace NearCritical.Section8
open Set MeasureTheory
open scoped Classical

/-- Intersect an arbitrary finite domain with a closed translated radius-n cube. -/
def cubeCut {d : ℕ} (Q : Finset (Vertex d)) (x : Vertex d) (n : ℕ) : Finset (Vertex d) :=
  Q.filter fun z => ∀ i, x i-(n : ℤ) ≤ z i ∧ z i ≤ x i+(n : ℤ)

/-- An interface edge inside Q can leave this cut only through a coordinate
cube face; holes in Q do not create spurious cube exits. -/
theorem innerEntryBoundary_cubeCut_subset_faces {d n : ℕ}
    (Q : Finset (Vertex d)) (x : Vertex d) :
    innerEntryBoundary Q (cubeCut Q x n) ⊆
      (cubeCut Q x n).filter (fun z => ∃ i : Fin d,
        z i = x i+(n : ℤ) ∨ z i = x i-(n : ℤ)) := by
  intro z hz
  obtain ⟨hzC,u,huQ,huC,hadj⟩ := Finset.mem_filter.mp hz
  have hzbox := (Finset.mem_filter.mp hzC).2
  apply Finset.mem_filter.mpr
  refine ⟨hzC,?_⟩
  by_contra hface
  apply huC
  apply Finset.mem_filter.mpr
  refine ⟨huQ,?_⟩
  intro i
  have hb := hzbox i
  have hs := openGraph_adj_height_bounds hadj i
  have hne : ¬ (z i = x i+(n : ℤ) ∨ z i = x i-(n : ℤ)) :=
    fun hi => hface ⟨i,hi⟩
  constructor <;> omega

/-- Actual connection probability split over cube faces, with its prefix
confined to the original domain intersected with the cube. -/
theorem finite_connection_cube_exit_bk {d n : ℕ} (p : unitInterval)
    (Q : Finset (Vertex d)) (x y : Vertex d) (hxQ : x ∈ Q)
    (hy : y ∉ cubeCut Q x n) :
    (percolation d p).real (connectionToSetEvent (Q : Set (Vertex d)) x {y}) ≤
      ∑ z ∈ (cubeCut Q x n).filter (fun z => ∃ i : Fin d,
          z i = x i+(n : ℤ) ∨ z i = x i-(n : ℤ)),
        (percolation d p).real
          (connectionToSetEvent (cubeCut Q x n : Set (Vertex d)) x {z}) *
        (percolation d p).real (connectionToSetEvent (Q : Set (Vertex d)) z {y}) := by
  have hx : x ∈ cubeCut Q x n := by
    apply Finset.mem_filter.mpr
    refine ⟨hxQ,?_⟩
    intro i
    constructor <;> omega
  calc
    _ ≤ ∑ z ∈ innerEntryBoundary Q (cubeCut Q x n),
        (percolation d p).real
          (connectionToSetEvent (cubeCut Q x n : Set (Vertex d)) x {z}) *
        (percolation d p).real (connectionToSetEvent (Q : Set (Vertex d)) z {y}) :=
      finite_connection_first_exit_bk p Q (cubeCut Q x n) x y hx hy
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg
      (innerEntryBoundary_cubeCut_subset_faces Q x)
      (fun z _ _ => mul_nonneg measureReal_nonneg measureReal_nonneg)

end NearCritical.Section8
