module
public import NearCritical.ThreePointDiagram
public import NearCritical.WaterCube

/-! Exact surface-order counting and clipped midpoint separation for cube faces. -/
@[expose] public section
noncomputable section
namespace NearCritical.Section8
open scoped Classical

/-- Every fixed-coordinate slice of a finite subset of a translated cube has
surface-order cardinality, even when the selected plane misses the cube. -/
theorem translated_cube_plane_card_le {d n : ℕ} (Q : Finset (Vertex d))
    (x : Vertex d) (i : Fin d) (cut : ℤ)
    (hQ : ∀ y ∈ Q, ∀ j, x j - (n : ℤ) ≤ y j ∧ y j ≤ x j + (n : ℤ)) :
    (Q.filter (fun y => y i = cut)).card ≤ (2*n+1)^(d-1) := by
  let I := fun j : Fin d => Finset.Icc (x j - (n : ℤ)) (x j + (n : ℤ))
  let T := Fintype.piFinset I
  have hQT : Q ⊆ T := by
    intro y hy
    apply Fintype.mem_piFinset.mpr
    intro j
    exact Finset.mem_Icc.mpr (hQ y hy j)
  have hcard (j : Fin d) : (I j).card = 2*n+1 := by
    dsimp only [I]
    rw [Int.card_Icc]
    omega
  have hle := Finset.card_le_card (Finset.filter_subset_filter
    (fun y : Vertex d => y i = cut) hQT)
  apply hle.trans
  dsimp only [T]
  rw [Fintype.card_filter_piFinset_eq (α := fun _ : Fin d => ℤ) I i cut]
  split_ifs
  · simp only [hcard, Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ i),
      Finset.card_univ, Fintype.card_fin, le_refl]
  · exact Nat.zero_le _

/-- Clipping handles n=1 and a zero midpoint offset. The same separation
constant works for either orientation of every coordinate midpoint plane. -/
theorem cube_midpoint_clipped_distance_lower {d n : ℕ} (hn : 1 ≤ n)
    (x y : Vertex d) (i : Fin d)
    (hmid : |(x i : ℝ)-(y i : ℝ)| = ((n/2 : ℕ) : ℝ)) :
    (n : ℝ)/3 ≤ max 1 (latticeDistance x y) := by
  have hcoord : ((n/2 : ℕ) : ℝ) ≤ latticeDistance x y := by
    rw [← hmid]
    simpa only [latticeDistance, vertexReal, Real.dist_eq] using
      dist_le_pi_dist (vertexReal x) (vertexReal y) i
  have hscale : n ≤ 3 * max 1 (n/2) := by omega
  have hscaleR : (n : ℝ) ≤ 3 * max 1 ((n/2 : ℕ) : ℝ) := by
    exact_mod_cast hscale
  have hmax : max 1 ((n/2 : ℕ) : ℝ) ≤ max 1 (latticeDistance x y) :=
    max_le_max_left 1 hcoord
  linarith

end NearCritical.Section8
