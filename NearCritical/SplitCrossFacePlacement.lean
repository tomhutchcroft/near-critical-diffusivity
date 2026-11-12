module

public import NearCritical.SplitCrossUniformFaceMoment

/-! The tube choices vary only at the far-face terminals. Reindex the
realization sum by those terminals alone. -/
@[expose] public section
noncomputable section

namespace NearCritical.SplitCrossDirect

open SplitTreeNode MeasureTheory
open scoped Classical BigOperators

/-- Replace the face positions and retain all other positions. -/
def replaceFaceSites {d : ℕ} (b : SplitTreeNode (4 * d) → Vertex d)
    (g : Fin (4 * d) → Vertex d) : SplitTreeNode (4 * d) → Vertex d
  | face k => g k
  | v => b v

private def extendFaceChoices {d : ℕ} (z : CrossingEdgeIndex d → Vertex d)
    (f : Fin (4 * d) → Vertex d) (v : CrossingEdgeIndex d) : Vertex d :=
  match v.val with
  | face k => f k
  | _ => z v

/-- The non-face edges have a single possible endpoint, so they
introduce no multiplicity into the sum. -/
theorem sum_crossingEdgeChoices_eq_face {d t : ℕ} (x : Vertex d) (axis : Fin d)
    (z : CrossingEdgeIndex d → Vertex d) (b : SplitTreeNode (4 * d) → Vertex d)
    (H : (SplitTreeNode (4 * d) → Vertex d) → ℝ) :
    (∑ f ∈ Fintype.piFinset (fun v => crossingEdgeChoices t v.val (z v)), H (faceAssignedSites b f)) =
      ∑ g ∈ Fintype.piFinset (fun k => nodeSites t x axis (face k)),
        H (replaceFaceSites b g) := by
  let restrictFace := fun (f : CrossingEdgeIndex d → Vertex d) (k : Fin (4 * d)) =>
    f ⟨face k, by simp⟩
  apply Finset.sum_nbij' restrictFace (extendFaceChoices z)
  · intro f hf
    apply Fintype.mem_piFinset.mpr
    intro k
    exact Fintype.mem_piFinset.mp hf ⟨face k, by simp⟩
  · intro g hg
    apply Fintype.mem_piFinset.mpr
    intro v
    cases hv : v.val with
    | face k => simpa [extendFaceChoices, hv, crossingEdgeChoices, nodeSites] using
        Fintype.mem_piFinset.mp hg k
    | root | spine _ | entry _ | exterior _ | cubeDummy _ | exteriorDummy _ =>
      simp [extendFaceChoices, hv, crossingEdgeChoices]
  · intro f hf
    funext v
    have hm := Fintype.mem_piFinset.mp hf v
    cases hv : v.val with
    | face k =>
      have he : (⟨face k, by simp⟩ : CrossingEdgeIndex d) = v := Subtype.ext hv.symm
      simp [extendFaceChoices, hv, restrictFace, he]
    | root | spine _ | entry _ | exterior _ | cubeDummy _ | exteriorDummy _ =>
      have he : f v = z v := by simpa [hv, crossingEdgeChoices] using hm
      simp [extendFaceChoices, hv, he]
  · intro g _
    funext k
    rfl
  · intro f _
    congr 1

end NearCritical.SplitCrossDirect
