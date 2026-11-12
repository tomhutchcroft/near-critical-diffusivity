module

public import NearCritical.AnnealedGridPatch
public import NearCritical.GridPatchStationarity
public import NearCritical.SqrtDifferentialIntegration

/-! The mixed grid mean reduces to one relaxed template and its actual
boundary-index fraction times the full template. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Finset

lemma card_grid_total_eq {d : ℕ} (w : Vertex d) (hw : ∀ k, 0 < w k) (N : Vertex d) :
    (latticeRectangle 0 (fun k => N k * w k - 1)).card =
      (latticeRectangle 0 (fun k => N k - 1)).card * (gridCell w 0).card := by
  classical
  rw [← biUnion_gridCell w hw N,card_biUnion (gridCell_pairwiseDisjoint w hw _)]
  simp_rw [card_gridCell_eq]
  simp

theorem annealedFull_grid_template_le {d : ℕ} (i : Fin d)
    (w N : Vertex d) (hw : ∀ k, 0 < w k) (hN : ∀ k, 0 < N k)
    (hNi : N i = 1) (L : ℕ) (hL : 0 < L)
    (hwidth : ∀ k, k ≠ i → w k = (L : ℤ)) (p : unitInterval) :
    annealedFull (latticeRectangle 0 (fun k => N k * w k - 1)) i (p : ℝ) ≤
      annealedRelaxed (gridCell w 0) i (p : ℝ) +
        (((latticeRectangle 0 (fun k => N k - 1)).filter
          (fun z => gridBoundaryFlag i N z)).card : ℝ) /
          (latticeRectangle 0 (fun k => N k - 1)).card *
            annealedFull (gridCell w 0) i (p : ℝ) +
        (w i : ℝ)^2 * (d-1 : ℕ) / L := by
  classical
  let s := latticeRectangle 0 (fun k => N k - 1)
  let U := fun z => gridCell w z
  let T := latticeRectangle 0 (fun k => N k * w k - 1)
  let bad := s.filter (fun z => gridBoundaryFlag i N z)
  let A := annealedRelaxed (U 0) i (p : ℝ)
  let F := annealedFull (U 0) i (p : ℝ)
  let K : ℝ := (w i : ℝ)^2 * (d-1 : ℕ) / L
  have hA : 0 ≤ A := annealedRelaxed_nonneg _ _ p.2.1 p.2.2
  have hs : s.Nonempty := by
    refine ⟨0,mem_latticeRectangle.mpr ?_⟩
    intro k
    have hk := hN k
    simp only [Pi.zero_apply]
    omega
  have hb : (U 0).Nonempty := by
    refine ⟨0,mem_latticeRectangle.mpr ?_⟩
    intro k
    have hk := hw k
    simp only [Pi.zero_apply,zero_mul]
    omega
  have hs0 : (s.card : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt (card_pos.mpr hs)
  have hb0 : ((U 0).card : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt (card_pos.mpr hb)
  have hvol : (T.card : ℝ) = (s.card : ℝ) * ((U 0).card : ℝ) := by
    exact_mod_cast card_grid_total_eq w hw N
  have hz0 : ∀ z ∈ s, z i = 0 := by
    intro z hz
    have h := mem_latticeRectangle.mp hz i
    simp only [Pi.zero_apply,hNi,sub_self] at h
    omega
  have hsumEq : (∑ z ∈ s, ((U z).card : ℝ) *
      (if gridBoundaryFlag i N z then annealedFull (U z) i (p : ℝ)
        else annealedRelaxed (U z) i (p : ℝ))) =
      ((U 0).card : ℝ) * ∑ z ∈ s, (if gridBoundaryFlag i N z then F else A) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro z hz
    rw [card_gridCell_eq,annealedFull_gridCell,annealedRelaxed_gridCell w z i (hz0 z hz) p]
  have hsumIndicator : (∑ z ∈ s, if gridBoundaryFlag i N z then F else 0) =
      (bad.card : ℝ) * F := by
    rw [← sum_filter]
    simp [bad]
  have hsumBound : (∑ z ∈ s, if gridBoundaryFlag i N z then F else A) ≤
      (s.card : ℝ) * A + (bad.card : ℝ) * F := by
    calc
      _ ≤ ∑ z ∈ s, (A + if gridBoundaryFlag i N z then F else 0) := by
        apply sum_le_sum
        intro z _
        split_ifs <;> linarith
      _ = _ := by rw [sum_add_distrib,sum_const,nsmul_eq_mul,hsumIndicator]
  have hcompare : (((U 0).card : ℝ) *
      ∑ z ∈ s, (if gridBoundaryFlag i N z then F else A)) / T.card ≤
      A + (bad.card : ℝ) / s.card * F := by
    calc
      _ ≤ (((U 0).card : ℝ) * ((s.card : ℝ)*A + (bad.card : ℝ)*F)) / T.card :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hsumBound (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
      _ = _ := by rw [hvol]; field_simp [hs0,hb0]
  have hp := annealedFull_grid_patch_le i w N hw hN hNi L hL hwidth p
  change annealedFull T i (p : ℝ) ≤
    (∑ z ∈ s, ((U z).card : ℝ) *
      (if gridBoundaryFlag i N z then annealedFull (U z) i (p : ℝ)
        else annealedRelaxed (U z) i (p : ℝ))) / T.card + K at hp
  rw [hsumEq] at hp
  exact hp.trans (add_le_add hcompare le_rfl)

end NearCritical
