module

public import NearCritical.SplitCrossCorridorRoutes
public import NearCritical.SplitCrossNodeRays

/-! Every branch's star lies in the regions of all its incident edges.
These same margins also cover the outward segments used before deletion. -/
@[expose] public section
noncomputable section

namespace NearCritical.SplitCrossDirect

open Section10 SplitTreeNode
open scoped Classical

def isCrossingBranch {L : ℕ} : SplitTreeNode L → Bool
  | spine _ | entry _ | exterior _ => true
  | _ => false

def crossingBranches (L : ℕ) : Finset (SplitTreeNode L) :=
  Finset.univ.filter fun v => isCrossingBranch v = true

@[simp] theorem mem_crossingBranches {L : ℕ} (v : SplitTreeNode L) :
    v ∈ crossingBranches L ↔ isCrossingBranch v = true := by
  simp [crossingBranches]

/-- A branch box with enough room for all fixed lattice offsets. -/
def crossingBranchBox {d : ℕ} (t : ℕ) (axis : Fin d) :
    SplitTreeNode (4 * d) → Finset (Vertex d)
  | spine k => spineBox t axis k
  | entry k => legBranchBox t (splitLegEquiv d k).1 (splitLegEquiv d k).2 true
  | exterior k => translateSites
      (farLegBoxCenter t (splitLegEquiv d k).1 (splitLegEquiv d k).2)
      (centeredBox d (legBoxRadius t))
  | _ => ∅

theorem branchBox_offset_subset {d t n : ℕ} (hts : 512 * (4 * d - 1 + 1) * n ≤ t)
    (htl : 2048 * n ≤ t) (x : Vertex d) (axis : Fin d) (v : SplitTreeNode (4 * d))
    (hv : v ∈ crossingBranches (4 * d)) {z : Vertex d} (hz : z ∈ nodeSites t x axis v) :
    translateSites z (centeredBox d n) ⊆ crossingBranchBox t axis v := by
  intro y hy
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hy
  cases v with
  | spine k => exact spineBranchCore_add_mem hts hz hu
  | entry k => exact legBranchCore_add_mem htl hz hu
  | exterior k =>
    have hhalf := legBranchBox_exterior_subset_halfBox _ _ (legBranchCore_add_mem htl hz hu)
    have hzero : (0 : Vertex d) ∈ centeredBox d 0 := by simp [mem_centeredBox]
    simpa [crossingBranchBox] using translatedBox_add_mem (by omega : legBoxRadius t / 2 + 0 ≤ legBoxRadius t)
      hhalf hzero
  | root | cubeDummy _ | exteriorDummy _ | face _ =>
    simp [isCrossingBranch] at hv

theorem branchBox_subset_incoming_region {d t : ℕ} (ht : 64 ≤ t)
    (axis : Fin d) (v : SplitTreeNode (4 * d)) :
    crossingBranchBox t axis v ⊆ crossingEdgeRegion t v := by
  cases v with
  | spine k => exact spineBox_subset_cube ht axis k
  | entry k => exact (legBranchBox_inside_subset_entry _ _).trans (entryLegBox_subset_cube ht _ _ true)
  | exterior k => exact (farLegBox_subset_beyond ht _ _).trans Finset.subset_union_right
  | root | cubeDummy _ | exteriorDummy _ | face _ => exact Finset.empty_subset _

theorem branchBox_subset_outgoing_region {d t : ℕ} (ht : 64 ≤ t)
    (hL : 2 ≤ 4 * d) (axis : Fin d) (v : SplitTreeNode (4 * d)) :
    crossingBranchBox t axis (parent hL v) ⊆ crossingEdgeRegion t v := by
  cases v with
  | root => exact Finset.empty_subset _
  | spine k =>
    by_cases hk : k.val = 0
    · simp [parent, hk, crossingBranchBox, crossingEdgeRegion]
    · simpa [parent, hk, crossingBranchBox, crossingEdgeRegion] using
        (spineBox_subset_cube ht axis (⟨k.val - 1, by have := k.isLt; omega⟩ : Fin (4 * d - 1)))
  | entry k => exact spineBox_subset_cube ht axis _
  | cubeDummy k =>
    exact (legBranchBox_inside_subset_entry _ _).trans (entryLegBox_subset_cube ht _ _ true)
  | exterior k =>
    exact (legBranchBox_inside_subset_entry _ _).trans
      ((entryLegBox_subset_cube ht _ _ true).trans Finset.subset_union_left)
  | exteriorDummy k => exact farLegBox_subset_beyond ht _ _
  | face k => exact subset_rfl

end NearCritical.SplitCrossDirect
