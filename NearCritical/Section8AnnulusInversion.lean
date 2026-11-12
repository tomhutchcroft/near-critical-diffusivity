module
public import NearCritical.Section8LocalHalfSpaceGeometry
public import NearCritical.LatticeInversion

/-! Full inversion of the actual retained-boundary annulus. -/
@[expose] public section
noncomputable section
namespace NearCritical.Section8
open Set MeasureTheory
open scoped Classical

private theorem neg_mem_cube {d c : ℕ} (x : Vertex d) :
    -x ∈ centeredBox d c ↔ x ∈ centeredBox d c := by
  simp only [mem_centeredBox,Pi.neg_apply]
  constructor <;> intro h i <;> have hi := h i <;> constructor <;> omega

private theorem neg_mem_boundary {d c : ℕ} (x : Vertex d) :
    -x ∈ boundarySites (centeredBox d c) ↔
      x ∈ boundarySites (centeredBox d c) := by
  rw [mem_centeredBox_boundary_iff,mem_centeredBox_boundary_iff,neg_mem_cube]
  simp only [Pi.neg_apply]
  constructor
  · rintro ⟨hx,i,hi⟩
    exact ⟨hx,i,by omega⟩
  · rintro ⟨hx,i,hi⟩
    exact ⟨hx,i,by omega⟩

/-- Full inversion preserves the annulus, including both boundary shells. -/
theorem neg_mem_heartAnnulus {d n c : ℕ} (x : Vertex d) :
    -x ∈ heartAnnulus (centeredBox d n) (centeredBox d c) ↔
      x ∈ heartAnnulus (centeredBox d n) (centeredBox d c) := by
  simp only [heartAnnulus,Finset.mem_sdiff,neg_mem_cube,neg_mem_boundary]

/-- The actual connection probability in this annulus is inversion invariant. -/
theorem annulus_connection_probability_inversion {d n c : ℕ}
    (p : unitInterval) (x y : Vertex d) :
    (percolation d p).real (connectionToSetEvent
      (heartAnnulus (centeredBox d n) (centeredBox d c) : Set (Vertex d)) (-x) {-y}) =
    (percolation d p).real (connectionToSetEvent
      (heartAnnulus (centeredBox d n) (centeredBox d c) : Set (Vertex d)) x {y}) := by
  let Q := heartAnnulus (centeredBox d n) (centeredBox d c)
  have hQ : Neg.neg '' (Q : Set (Vertex d)) = (Q : Set (Vertex d)) := by
    ext z
    constructor
    · rintro ⟨w,hw,rfl⟩
      exact (neg_mem_heartAnnulus w).mpr hw
    · intro hz
      refine ⟨-z,(neg_mem_heartAnnulus z).mpr hz,?_⟩
      simp
  have he := connectionToSet_probability_inversion p x (Q : Set (Vertex d)) {y}
  rw [hQ,Set.image_singleton] at he
  exact congrArg ENNReal.toReal he

end NearCritical.Section8
