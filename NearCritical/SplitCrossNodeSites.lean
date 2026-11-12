module

public import NearCritical.SplitCrossIndexChildren
public import NearCritical.SplitCrossBranchMargins
public import NearCritical.SplitCrossFarFaceCore

/-! The actual lattice site sets for the nodes of the split-crossing tree.
The spine and entry branches lie inside the common cube. Every exterior
node lies in its own split leg. -/
@[expose] public section
noncomputable section

namespace NearCritical.SplitCrossDirect

open Section10 SplitTreeNode
open scoped Classical

/-- Identify the tree's ordered legs with the two transverse halves of
each signed lattice face. -/
def splitLegEquiv (d : ℕ) : Fin (4 * d) ≃ (Fin d × Bool) × Bool :=
  (finCongr (by simp [Fintype.card_prod, Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm] :
    4 * d = Fintype.card ((Fin d × Bool) × Bool))).trans (Fintype.equivFin _).symm

def splitEnvelope (d t : ℕ) : Finset (Vertex d) := centeredBox d ((t - 1) / 2 + t)

def nodeSites {d : ℕ} (t : ℕ) (x : Vertex d) (axis : Fin d) :
    SplitTreeNode (4 * d) → Finset (Vertex d)
  | root => {x}
  | spine k => spineBranchCore t axis k
  | entry k => legBranchCore t (splitLegEquiv d k).1 (splitLegEquiv d k).2 true
  | exterior k => legBranchCore t (splitLegEquiv d k).1 (splitLegEquiv d k).2 false
  | cubeDummy k => entryLegBox t (splitLegEquiv d k).1 (splitLegEquiv d k).2 false
  | exteriorDummy k => translateSites
      (interiorLegBoxCenter t (splitLegEquiv d k).1 (splitLegEquiv d k).2)
      (centeredBox d (legBoxRadius t))
  | face k => farLegFaceCore t (splitLegEquiv d k).1 (splitLegEquiv d k).2

theorem spineBranchCore_subset_spine {d K : ℕ} (t : ℕ) (axis : Fin d) (k : Fin K) :
    spineBranchCore t axis k ⊆ spineBox t axis k := by
  intro y hy
  have hzero : (0 : Vertex d) ∈ centeredBox d 0 := by simp [mem_centeredBox]
  simpa using spineBranchCore_add_mem (R := 0) (by simp) hy hzero

theorem legBranchCore_subset_branch {d : ℕ} (t : ℕ) (f : Fin d × Bool) (pl inside : Bool) :
    legBranchCore t f pl inside ⊆ legBranchBox t f pl inside := by
  intro y hy
  have hzero : (0 : Vertex d) ∈ centeredBox d 0 := by simp [mem_centeredBox]
  simpa using legBranchCore_add_mem (R := 0) (by simp) hy hzero

theorem legBranchCore_inside_subset_entry {d : ℕ} (t : ℕ) (f : Fin d × Bool) (pl : Bool) :
    legBranchCore t f pl true ⊆ entryLegBox t f pl true :=
  (legBranchCore_subset_branch t f pl true).trans (legBranchBox_inside_subset_entry (t := t) f pl)

theorem legBranchCore_exterior_subset_farBox {d : ℕ} (t : ℕ) (f : Fin d × Bool) (pl : Bool) :
    legBranchCore t f pl false ⊆
      translateSites (farLegBoxCenter t f pl) (centeredBox d (legBoxRadius t)) := by
  intro y hy
  have hhalf := legBranchBox_exterior_subset_halfBox (t := t) f pl
    (legBranchCore_subset_branch t f pl false hy)
  have hzero : (0 : Vertex d) ∈ centeredBox d 0 := by simp [mem_centeredBox]
  simpa using translatedBox_add_mem (by omega : legBoxRadius t / 2 + 0 ≤ legBoxRadius t)
    hhalf hzero

theorem farLegFaceCore_subset_farBox {d : ℕ} (t : ℕ) (f : Fin d × Bool) (pl : Bool) :
    farLegFaceCore t f pl ⊆
      translateSites (farLegBoxCenter t f pl) (centeredBox d (legBoxRadius t)) := by
  intro y hy
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
  exact (mem_translateSites _ _ _).mpr (Finset.mem_filter.mp (signedCubeFaceCore_mem hz).1).1

theorem typicalCube_subset_splitEnvelope {d t : ℕ} (ht : 1 ≤ t) :
    typicalCube t (0 : Vertex d) ⊆ splitEnvelope d t := by
  intro y hy
  have hy' := (mem_typicalCube_iff_int (by omega) 0 y).mp hy
  apply mem_centeredBox.mpr
  intro j
  have hj := hy' j
  simp only [Pi.zero_apply, sub_zero] at hj
  omega

theorem splitBeyond_subset_splitEnvelope {d : ℕ} (t : ℕ) (f : Fin d × Bool) (pl : Bool) :
    splitBeyond t f pl t ⊆ splitEnvelope d t :=
  Finset.filter_subset _ _

theorem root_mem_innerCube {d t : ℕ} {x : Vertex d}
    (hx : x ∈ centeredBox d ((t - 1) / 32)) : x ∈ centeredBox d (7 * t / 16) := by
  apply mem_centeredBox.mpr
  intro i
  have hi := mem_centeredBox.mp hx i
  omega

theorem root_mem_typicalCube {d t : ℕ} (ht : 1 ≤ t) {x : Vertex d}
    (hx : x ∈ centeredBox d ((t - 1) / 32)) : x ∈ typicalCube t 0 := by
  apply (mem_typicalCube_iff_int (by omega) 0 x).mpr
  intro i
  have hi := mem_centeredBox.mp hx i
  simp only [Pi.zero_apply, sub_zero]
  omega

theorem nodeSites_subset_envelope {d t : ℕ} (ht : 64 ≤ t) {x : Vertex d}
    (hx : x ∈ centeredBox d ((t - 1) / 32)) (axis : Fin d) (v : SplitTreeNode (4 * d)) :
    nodeSites t x axis v ⊆ splitEnvelope d t := by
  have hc : typicalCube t (0 : Vertex d) ⊆ splitEnvelope d t :=
    typicalCube_subset_splitEnvelope (by omega)
  cases v with
  | root =>
    exact Finset.singleton_subset_iff.mpr (hc (root_mem_typicalCube (by omega) hx))
  | spine k =>
    exact (spineBranchCore_subset_spine t axis k).trans
      ((spineBox_subset_cube ht axis k).trans hc)
  | entry k =>
    exact (legBranchCore_inside_subset_entry t _ _).trans
      ((entryLegBox_subset_cube ht _ _ true).trans hc)
  | exterior k =>
    exact (legBranchCore_exterior_subset_farBox t _ _).trans
      ((farLegBox_subset_beyond ht _ _).trans (splitBeyond_subset_splitEnvelope t _ _))
  | cubeDummy k =>
    exact (entryLegBox_subset_cube ht _ _ false).trans hc
  | exteriorDummy k =>
    exact (interiorLegBox_subset_beyond ht _ _).trans (splitBeyond_subset_splitEnvelope t _ _)
  | face k =>
    exact (farLegFaceCore_subset_farBox t _ _).trans
      ((farLegBox_subset_beyond ht _ _).trans (splitBeyond_subset_splitEnvelope t _ _))

/-- Cardinal lower bounds used when summing over all placements. -/
def nodeSiteCount (d t : ℕ) : SplitTreeNode (4 * d) → ℕ
  | root => 1
  | spine _ => (2 * (spineRadius (4 * d - 1) t / 2) + 1)^d
  | entry _ | exterior _ => (2 * (t / 2048) + 1)^d
  | cubeDummy _ | exteriorDummy _ => (2 * legBoxRadius t + 1)^d
  | face _ => (2 * (legBoxRadius t / 2) + 1)^(d - 1)

theorem nodeSiteCount_le_card {d : ℕ} (t : ℕ) (x : Vertex d) (axis : Fin d)
    (v : SplitTreeNode (4 * d)) : nodeSiteCount d t v ≤ (nodeSites t x axis v).card := by
  cases v with
  | root => simp [nodeSiteCount, nodeSites]
  | spine k => exact (spineBranchCore_card t axis k).ge
  | entry k => exact (legBranchCore_card t _ _ true).ge
  | exterior k => exact (legBranchCore_card t _ _ false).ge
  | cubeDummy k => exact (entryLegBox_card t _ _ false).ge
  | exteriorDummy k => exact (interiorLegBox_card t _ _).ge
  | face k => exact farLegFaceCore_card_lower t _ _

theorem nodeSites_nonempty {d : ℕ} (t : ℕ) (x : Vertex d) (axis : Fin d)
    (v : SplitTreeNode (4 * d)) : (nodeSites t x axis v).Nonempty := by
  have h : 0 < nodeSiteCount d t v := by
    cases v <;> simp only [nodeSiteCount] <;> positivity
  exact Finset.card_pos.mp (h.trans_le (nodeSiteCount_le_card t x axis v))

end NearCritical.SplitCrossDirect
