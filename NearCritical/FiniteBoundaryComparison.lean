module

public import NearCritical.GridPatchMeanComparison
public import NearCritical.GridBoundaryCount
public import NearCritical.ConductivityUpperBound

/-! Actual finite annealed full-versus-relaxed boundary comparison on grids. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Finset

theorem annealedFull_grid_boundary_comparison {d : ℕ} (i : Fin d)
    (w N : Vertex d) (hw : ∀ k, 0 < w k) (hN : ∀ k, 0 < N k)
    (hNi : N i = 1) (L n : ℕ) (hL : 0 < L) (hn : 0 < n)
    (hwidth : ∀ k, k ≠ i → w k = (L : ℤ))
    (hcount : ∀ k, k ≠ i → N k = (n : ℤ)) (p : unitInterval) :
    annealedFull (latticeRectangle 0 (fun k => N k * w k - 1)) i (p : ℝ) ≤
      annealedRelaxed (gridCell w 0) i (p : ℝ) + 2 * (d-1 : ℕ) / n +
        (w i : ℝ)^2 * (d-1 : ℕ) / L := by
  classical
  let s := latticeRectangle 0 (fun k => N k - 1)
  let frac : ℝ := ((s.filter (fun z => gridBoundaryFlag i N z)).card : ℝ) / s.card
  have hb : (gridCell w 0).Nonempty := by
    refine ⟨0,mem_latticeRectangle.mpr ?_⟩
    intro k
    have hk := hw k
    simp only [Pi.zero_apply,zero_mul]
    omega
  have hF : annealedFull (gridCell w 0) i (p : ℝ) ≤ 1 :=
    (annealedFull_le_parameter _ hb i p).trans p.2.2
  have hfrac : 0 ≤ frac := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hbound : frac ≤ 2 * (d-1 : ℕ) / n := by
    simpa only [frac,s,gridBoundaryFlag,decide_eq_true_eq] using
      gridBoundaryIndex_fraction_le i N n hn hNi hcount
  have hproduct : frac * annealedFull (gridCell w 0) i (p : ℝ) ≤
      2 * (d-1 : ℕ) / n := by
    calc
      _ ≤ frac * 1 := mul_le_mul_of_nonneg_left hF hfrac
      _ = frac := mul_one frac
      _ ≤ _ := hbound
  have hp := annealedFull_grid_template_le i w N hw hN hNi L hL hwidth p
  exact hp.trans (add_le_add (add_le_add le_rfl hproduct) le_rfl)

end NearCritical
