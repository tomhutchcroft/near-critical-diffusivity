module

public import NearCritical.RectangleBoundary
public import Mathlib.Data.Int.DivMod

/-! Exact rectangular grid tilings and an owner map independent of the
distinguished coordinate. Translation to centered odd water cubes is separate. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Finset

def gridCell {d : ℕ} (w z : Vertex d) : Finset (Vertex d) :=
  latticeRectangle (fun k => z k * w k) (fun k => z k * w k + w k - 1)

def gridOwner {d : ℕ} (w x : Vertex d) : Vertex d := fun k => x k / w k

lemma mem_gridCell_iff_owner {d : ℕ} (w : Vertex d) (hw : ∀ k, 0 < w k)
    (z x : Vertex d) : x ∈ gridCell w z ↔ gridOwner w x = z := by
  rw [gridCell, mem_latticeRectangle]
  constructor
  · intro hx
    funext k
    apply (Int.ediv_eq_iff_of_pos (hw k)).mpr
    have hk := hx k
    exact ⟨hk.1, by omega⟩
  · intro he k
    have hk := (Int.ediv_eq_iff_of_pos (hw k)).mp (congrFun he k)
    exact ⟨hk.1, by omega⟩

lemma gridOwner_mem_index_iff {d : ℕ} (w : Vertex d) (hw : ∀ k, 0 < w k)
    (N x : Vertex d) :
    gridOwner w x ∈ latticeRectangle 0 (fun k => N k - 1) ↔
      x ∈ latticeRectangle 0 (fun k => N k * w k - 1) := by
  simp only [mem_latticeRectangle, Pi.zero_apply, gridOwner]
  constructor
  · intro hx k
    have hk := hx k
    have hl := (Int.ediv_nonneg_iff_of_pos (hw k)).mp hk.1
    have ht : x k / w k < N k := by omega
    have hh := (Int.ediv_lt_iff_lt_mul (hw k)).mp ht
    exact ⟨hl, by omega⟩
  · intro hx k
    have hk := hx k
    have hl := (Int.ediv_nonneg_iff_of_pos (hw k)).mpr hk.1
    have ht : x k < N k * w k := by omega
    have hh := (Int.ediv_lt_iff_lt_mul (hw k)).mpr ht
    exact ⟨hl, by omega⟩

theorem gridCell_pairwiseDisjoint {d : ℕ} (w : Vertex d) (hw : ∀ k, 0 < w k)
    (s : Finset (Vertex d)) : (s : Set (Vertex d)).PairwiseDisjoint (gridCell w) := by
  intro z _ t _ hzt
  apply disjoint_left.mpr
  intro x hx hz
  exact hzt (((mem_gridCell_iff_owner w hw z x).mp hx).symm.trans
    ((mem_gridCell_iff_owner w hw t x).mp hz))

theorem biUnion_gridCell {d : ℕ} (w : Vertex d) (hw : ∀ k, 0 < w k)
    (N : Vertex d) :
    (latticeRectangle 0 (fun k => N k - 1)).biUnion (gridCell w) =
      latticeRectangle 0 (fun k => N k * w k - 1) := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨z, hz, hx⟩ := mem_biUnion.mp hx
    apply (gridOwner_mem_index_iff w hw N x).mp
    simpa only [(mem_gridCell_iff_owner w hw z x).mp hx] using hz
  · intro hx
    exact mem_biUnion.mpr ⟨gridOwner w x, (gridOwner_mem_index_iff w hw N x).mpr hx,
      (mem_gridCell_iff_owner w hw _ _).mpr rfl⟩

def transverseGridOwner {d : ℕ} (i : Fin d) (w x : Vertex d) : Vertex d :=
  Function.update (gridOwner w x) i 0

lemma transverseGridOwner_bondTip {d : ℕ} (i : Fin d) (w x : Vertex d) :
    transverseGridOwner i w (bondTip (x,i)) = transverseGridOwner i w x := by
  ext k
  by_cases hki : k = i
  · subst k
    simp [transverseGridOwner]
  · simp [transverseGridOwner, gridOwner, bondTip, hki]

lemma transverseGridOwner_eq_on_cell {d : ℕ} (i : Fin d)
    (w : Vertex d) (hw : ∀ k, 0 < w k) (z x : Vertex d) (hz : z i = 0)
    (hx : x ∈ gridCell w z) : transverseGridOwner i w x = z := by
  rw [transverseGridOwner, (mem_gridCell_iff_owner w hw z x).mp hx]
  exact Function.update_eq_self_iff.mpr hz.symm

end NearCritical
