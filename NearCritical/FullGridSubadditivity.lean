module

public import NearCritical.AnnealedSubadditivity
public import NearCritical.GridPatchMeanComparison

/-! Exact full-Dirichlet mean comparison under rectangular replication.
This is the finite tiling step of the cube-to-water chain, without a limit. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Finset

theorem annealedFull_grid_subadditivity {d : ℕ} (i : Fin d)
    (w N : Vertex d) (hw : ∀ k, 0 < w k) (hN : ∀ k, 0 < N k)
    (p : unitInterval) :
    annealedFull (latticeRectangle 0 (fun k => N k * w k - 1)) i (p : ℝ) ≤
      annealedFull (gridCell w 0) i (p : ℝ) := by
  classical
  let s := latticeRectangle 0 (fun k => N k - 1)
  let lo := fun z : Vertex d => fun k => z k * w k
  let hi := fun z : Vertex d => fun k => z k * w k + w k - 1
  let T := latticeRectangle 0 (fun k => N k * w k - 1)
  have hv : ∀ z ∈ s, ∀ k, lo z k ≤ hi z k := by
    intro z _ k
    have hk := hw k
    dsimp only [lo,hi]
    omega
  have hs : s.Nonempty := by
    refine ⟨0,mem_latticeRectangle.mpr ?_⟩
    intro k
    have hk := hN k
    simp only [Pi.zero_apply]
    omega
  have hb : (gridCell w 0).Nonempty := by
    refine ⟨0,mem_latticeRectangle.mpr ?_⟩
    intro k
    have hk := hw k
    simp only [Pi.zero_apply,zero_mul]
    omega
  have hs0 : (s.card : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt (card_pos.mpr hs)
  have hb0 : ((gridCell w 0).card : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt (card_pos.mpr hb)
  have hvol : (T.card : ℝ) = (s.card : ℝ) * ((gridCell w 0).card : ℝ) := by
    exact_mod_cast card_grid_total_eq w hw N
  have hsum : (∑ z ∈ s, ((gridCell w z).card : ℝ) / T.card *
      annealedFull (gridCell w z) i (p : ℝ)) = annealedFull (gridCell w 0) i (p : ℝ) := by
    simp_rw [card_gridCell_eq,annealedFull_gridCell]
    rw [sum_const,nsmul_eq_mul,hvol]
    field_simp [hs0,hb0]
  have hp := annealedFull_rectangle_subadditivity s lo hi hv
    (gridCell_pairwiseDisjoint w hw s) p i
  change annealedFull (s.biUnion (gridCell w)) i (p : ℝ) ≤
    ∑ z ∈ s, ((gridCell w z).card : ℝ) / (s.biUnion (gridCell w)).card *
      annealedFull (gridCell w z) i (p : ℝ) at hp
  have hT : s.biUnion (gridCell w) = T := biUnion_gridCell w hw N
  rw [hT,hsum] at hp
  exact hp

end NearCritical
