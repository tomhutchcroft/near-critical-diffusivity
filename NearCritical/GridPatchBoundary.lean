module

public import NearCritical.LatticeRectangularTiling
public import NearCritical.PatchBoundaryGeometry
public import NearCritical.MixedDirichletPatch
public import Mathlib.Tactic.Linarith

/-! Boundary tile indices and actual transverse interior bounds. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Finset

def gridBoundaryIndex {d : ℕ} (i : Fin d) (N z : Vertex d) : Prop :=
  ∃ k, k ≠ i ∧ (z k = 0 ∨ z k = N k - 1)

lemma gridCell_subset_total {d : ℕ} (w : Vertex d) (hw : ∀ k, 0 < w k)
    (N z : Vertex d) (hz : z ∈ latticeRectangle 0 (fun k => N k - 1)) :
    gridCell w z ⊆ latticeRectangle 0 (fun k => N k * w k - 1) := by
  rw [← biUnion_gridCell w hw N]
  exact subset_biUnion_of_mem (gridCell w) hz

/-- The entire enlarged support of a nonboundary tile lies strictly above all
global transverse lower faces, and below the global upper base faces. -/
theorem grid_good_tile_transverse_bounds {d : ℕ} (i : Fin d)
    (w : Vertex d) (hw : ∀ k, 0 < w k) (N z : Vertex d)
    (hz : z ∈ latticeRectangle 0 (fun k => N k - 1))
    (hgood : ¬ gridBoundaryIndex i N z) (x : DomainVertex (gridCell w z)) :
    ∀ k, k ≠ i → 0 < x.val k ∧ x.val k ≤ N k * w k - 1 := by
  intro k hki
  have hzk := mem_latticeRectangle.mp hz k
  have hzn : z k ≠ 0 := fun h => hgood ⟨k,hki,Or.inl h⟩
  have hzt : z k ≠ N k - 1 := fun h => hgood ⟨k,hki,Or.inr h⟩
  have hzpos : 0 < z k := by simpa only [Pi.zero_apply] using
    (lt_of_le_of_ne hzk.1 (Ne.symm hzn))
  have hzupper : z k + 1 < N k := by omega
  have hx := sitesPlus_coordinate_bounds (gridCell w z) k
    (fun y hy => (mem_latticeRectangle.mp hy) k) x.val x.property
  have hl : 0 < z k * w k := mul_pos hzpos (hw k)
  have hu : (z k + 1) * w k < N k * w k :=
    mul_lt_mul_of_pos_right hzupper (hw k)
  constructor
  · exact lt_of_lt_of_le hl hx.1
  · nlinarith [hx.2]

def gridBoundaryFlag {d : ℕ} (i : Fin d) (N z : Vertex d) : Bool := by
  classical
  exact decide (gridBoundaryIndex i N z)

/-- Actual grid cells discharge the mixed patch's local boundary membership:
boundary-index tiles use full data, and every other tile uses its two faces. -/
theorem grid_patch_boundary_membership {d : ℕ} (i : Fin d)
    (w : Vertex d) (hw : ∀ k, 0 < w k) (N z : Vertex d) (hNi : N i = 1)
    (hz : z ∈ latticeRectangle 0 (fun k => N k - 1))
    (x : Vertex d) (hx : x ∈ sitesPlus (gridCell w z))
    (hb : x ∈ boundarySites (sitesPlus (latticeRectangle 0 (fun k => N k * w k - 1)))) :
    (⟨x,hx⟩ : DomainVertex (gridCell w z)) ∈
      mixedBoundary (gridCell w z) i (gridBoundaryFlag i N z) := by
  classical
  have hzi : z i = 0 := by
    have h := mem_latticeRectangle.mp hz i
    simp only [Pi.zero_apply, hNi, sub_self] at h
    omega
  by_cases hbad : gridBoundaryIndex i N z
  · simp only [gridBoundaryFlag, hbad, decide_true, mixedBoundary, ↓reduceIte]
    exact boundarySites_of_subset (sitesPlus_mono (gridCell_subset_total w hw N z hz)) hx hb
  · simp only [gridBoundaryFlag, hbad, decide_false, mixedBoundary, Bool.false_eq_true,
      ↓reduceIte]
    apply rectangle_global_boundary_mem_local_twoFace_of_subset
      0 (fun k => N k * w k - 1) (fun k => z k * w k)
      (fun k => z k * w k + w k - 1) i
      (by simp [hzi]) (by simp [hzi,hNi]) (gridCell_subset_total w hw N z hz) x hx hb
    exact grid_good_tile_transverse_bounds i w hw N z hz hbad ⟨x,hx⟩

end NearCritical
