module

public import NearCritical.GridPatchConductivity
public import NearCritical.TransverseConductivityTranslation

/-! Actual Bernoulli averaging of the concrete mixed grid comparison. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Finset MeasureTheory

theorem annealedFull_grid_patch_le {d : ℕ} (i : Fin d)
    (w N : Vertex d) (hw : ∀ k, 0 < w k) (hN : ∀ k, 0 < N k)
    (hNi : N i = 1) (L : ℕ) (hL : 0 < L)
    (hwidth : ∀ k, k ≠ i → w k = (L : ℤ)) (p : unitInterval) :
    annealedFull (latticeRectangle 0 (fun k => N k * w k - 1)) i (p : ℝ) ≤
      (∑ z ∈ latticeRectangle 0 (fun k => N k - 1), ((gridCell w z).card : ℝ) *
        (if gridBoundaryFlag i N z then annealedFull (gridCell w z) i (p : ℝ)
          else annealedRelaxed (gridCell w z) i (p : ℝ))) /
        (latticeRectangle 0 (fun k => N k * w k - 1)).card +
          (w i : ℝ)^2 * (d-1 : ℕ) / L := by
  classical
  let s := latticeRectangle 0 (fun k => N k - 1)
  let U := fun z => gridCell w z
  let T := latticeRectangle 0 (fun k => N k * w k - 1)
  let K : ℝ := (w i : ℝ)^2 * (d-1 : ℕ) / L
  let g := fun z ω => if gridBoundaryFlag i N z then fullConductivity (U z) i ω
    else relaxedConductivity (U z) i ω
  have hg : ∀ z, Integrable (g z) (percolation d p) := by
    intro z
    cases h : gridBoundaryFlag i N z
    · simpa only [g,h,Bool.false_eq_true,↓reduceIte] using integrable_relaxedConductivity (U z) i p
    · simpa only [g,h,↓reduceIte] using integrable_fullConductivity (U z) i p
  have hmean : ∀ z, (∫ ω, g z ω ∂percolation d p) =
      if gridBoundaryFlag i N z then annealedFull (U z) i (p : ℝ)
        else annealedRelaxed (U z) i (p : ℝ) := by
    intro z
    cases h : gridBoundaryFlag i N z
    · simpa only [g,h,Bool.false_eq_true,↓reduceIte] using (annealedRelaxed_eq_integral (U z) i p).symm
    · simpa only [g,h,↓reduceIte] using (annealedFull_eq_integral (U z) i p).symm
  have hint : ∀ z ∈ s, Integrable (fun ω => ((U z).card : ℝ) * g z ω) (percolation d p) :=
    fun z _ => (hg z).const_mul _
  have hdiv := (integrable_finsetSum s hint).div_const (T.card : ℝ)
  have hsum : (∫ ω, ∑ z ∈ s, ((U z).card : ℝ) * g z ω ∂percolation d p) =
      ∑ z ∈ s, ((U z).card : ℝ) *
        (if gridBoundaryFlag i N z then annealedFull (U z) i (p : ℝ)
          else annealedRelaxed (U z) i (p : ℝ)) := by
    rw [integral_finsetSum s hint]
    apply sum_congr rfl
    intro z _
    rw [integral_const_mul,hmean]
  calc
    _ = ∫ ω, fullConductivity T i ω ∂percolation d p := annealedFull_eq_integral T i p
    _ ≤ ∫ ω, ((∑ z ∈ s, ((U z).card : ℝ) * g z ω) / T.card + K) ∂percolation d p :=
      integral_mono (integrable_fullConductivity T i p) (hdiv.add (integrable_const K))
        (fun ω => fullConductivity_grid_patch_le i w N hw hN hNi L hL hwidth ω)
    _ = _ := by
      rw [integral_add hdiv (integrable_const K),integral_div,hsum]
      simp only [integral_const,smul_eq_mul,probReal_univ,one_mul]
      rfl

end NearCritical
