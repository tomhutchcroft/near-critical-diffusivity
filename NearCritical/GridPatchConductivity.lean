module

public import NearCritical.GridPatchBoundary
public import Mathlib.Tactic.Positivity

/-! Concrete finite rectangular mixed-minimizer comparison. No tiling, owner,
potential-range or outer boundary membership is assumed in the conclusion. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Finset

theorem fullConductivity_grid_patch_le {d : ℕ} (i : Fin d)
    (w N : Vertex d) (hw : ∀ k, 0 < w k) (hN : ∀ k, 0 < N k)
    (hNi : N i = 1) (L : ℕ) (hL : 0 < L)
    (hwidth : ∀ k, k ≠ i → w k = (L : ℤ)) (ω : Configuration d) :
    fullConductivity (latticeRectangle 0 (fun k => N k * w k - 1)) i ω ≤
      (∑ z ∈ latticeRectangle 0 (fun k => N k - 1), ((gridCell w z).card : ℝ) *
        (if gridBoundaryFlag i N z then fullConductivity (gridCell w z) i ω
          else relaxedConductivity (gridCell w z) i ω)) /
        (latticeRectangle 0 (fun k => N k * w k - 1)).card +
          (w i : ℝ)^2 * (d-1 : ℕ) / L := by
  classical
  let s := latticeRectangle 0 (fun k => N k - 1)
  let lo := fun z : Vertex d => fun k => z k * w k
  let hi := fun z : Vertex d => fun k => z k * w k + w k - 1
  let T := s.biUnion (gridCell w)
  have hTeq : T = latticeRectangle 0 (fun k => N k * w k - 1) := biUnion_gridCell w hw N
  have hv : ∀ z ∈ s, ∀ k, lo z k ≤ hi z k := by
    intro z _ k
    dsimp only [lo,hi]
    have hk := hw k
    omega
  have hz0 : ∀ z ∈ s, z i = 0 := by
    intro z hz
    have h := mem_latticeRectangle.mp hz i
    simp only [Pi.zero_apply,hNi,sub_self] at h
    omega
  have hnon : T.Nonempty := by
    rw [hTeq]
    refine ⟨0,mem_latticeRectangle.mpr ?_⟩
    intro k
    have hk := mul_pos (hN k) (hw k)
    constructor <;> simp only [Pi.zero_apply] <;> omega
  have hcoord : ∀ x ∈ sitesPlus T, (x i : ℝ) ∈ Set.Icc 0 (w i : ℝ) := by
    intro x hx
    rw [hTeq] at hx
    have h := sitesPlus_coordinate_bounds
      (latticeRectangle 0 (fun k => N k * w k - 1)) i
      (fun y hy => mem_latticeRectangle.mp hy i) x hx
    simp only [Pi.zero_apply,hNi,one_mul,sub_add_cancel] at h
    constructor
    · exact_mod_cast h.1
    · exact_mod_cast h.2
  have hp := fullConductivity_mixed_rectangular_patch_le s lo hi hv
    (gridCell_pairwiseDisjoint w hw s) (transverseGridOwner i w)
    (gridBoundaryFlag i N) ω i L hL
    (fun z hz k hki => by
      dsimp only [lo,hi]
      rw [Int.card_Icc]
      have hk := hwidth k hki
      omega)
    0 (w i : ℝ) (by exact_mod_cast (hw i).le)
    (fun z hz x hx => transverseGridOwner_eq_on_cell i w hw z x (hz0 z hz) hx)
    (fun _ _ x _ => transverseGridOwner_bondTip i w x) hnon hcoord
    (fun x hx hj hlocal => by
      have hb : x.val ∈ boundarySites
          (sitesPlus (latticeRectangle 0 (fun k => N k * w k - 1))) := by
        change x.val ∈ boundarySites (sitesPlus T) at hx
        simpa only [hTeq] using hx
      exact grid_patch_boundary_membership i w hw N _ hNi hj x.val hlocal hb)
  change fullConductivity T i ω ≤
    (∑ z ∈ s, ((gridCell w z).card : ℝ) *
      (if gridBoundaryFlag i N z then fullConductivity (gridCell w z) i ω
        else relaxedConductivity (gridCell w z) i ω)) / T.card +
      ((w i : ℝ)-0)^2 * (d-1 : ℕ) / L at hp
  simpa only [hTeq,sub_zero] using hp

end NearCritical
