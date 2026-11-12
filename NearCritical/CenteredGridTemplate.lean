module
public import NearCritical.RelaxedConductivityTranslation
public import NearCritical.LatticeRectangularTiling
public import NearCritical.WaterCube

/-! Exact centering of actual odd grid templates. The distinguished-coordinate
shift is allowed by proved relaxed affine-boundary translation invariance. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Finset

def oddGridWidths {d : ℕ} (radii : Fin d → ℕ) : Vertex d := fun j => 2*(radii j:ℤ)+1

/-- Actual supports agree after translation, not merely in cardinality. -/
theorem gridCell_odd_eq_translate {d : ℕ} (radii : Fin d → ℕ) :
    gridCell (oddGridWidths radii) 0 =
      translateSites (fun j => (radii j:ℤ)) (rectangularBox radii) := by
  classical
  ext x
  constructor
  · intro hx
    refine mem_image.mpr ⟨x-(fun j => (radii j:ℤ)),?_,by simp⟩
    apply mem_rectangularBox.mpr
    intro j
    have hk := mem_latticeRectangle.mp hx j
    simp only [Pi.zero_apply,zero_mul,zero_add,oddGridWidths] at hk
    change -(radii j:ℤ) ≤ x j-(radii j:ℤ) ∧ x j-(radii j:ℤ) ≤ (radii j:ℤ)
    omega
  · rintro hx
    obtain ⟨y,hy,rfl⟩ := mem_image.mp hx
    apply mem_latticeRectangle.mpr
    intro j
    have hk := mem_rectangularBox.mp hy j
    simp only [Pi.zero_apply,zero_mul,zero_add,oddGridWidths,Pi.add_apply]
    omega

theorem annealedFull_odd_grid_centered {d : ℕ} (radii : Fin d → ℕ) (i : Fin d)
    (p : unitInterval) :
    annealedFull (gridCell (oddGridWidths radii) 0) i (p:ℝ) =
      annealedFull (rectangularBox radii) i (p:ℝ) := by
  rw [gridCell_odd_eq_translate,annealedFull_translation]

theorem annealedRelaxed_odd_grid_centered {d : ℕ} (radii : Fin d → ℕ) (i : Fin d)
    (p : unitInterval) :
    annealedRelaxed (gridCell (oddGridWidths radii) 0) i (p:ℝ) =
      annealedRelaxed (rectangularBox radii) i (p:ℝ) := by
  rw [gridCell_odd_eq_translate,annealedRelaxed_translation]

/-- Literal water-cube template in an uncentered rectangular grid. -/
theorem annealedRelaxed_waterCube_grid {d : ℕ} (i : Fin d) (r R : ℕ)
    (p : unitInterval) :
    annealedRelaxed (gridCell (oddGridWidths (fun j => if j=i then r else R)) 0) i (p:ℝ) =
      annealedRelaxed (waterCube d i r R) i (p:ℝ) :=
  annealedRelaxed_odd_grid_centered _ i p

theorem annealedFull_waterCube_grid {d : ℕ} (i : Fin d) (r R : ℕ)
    (p : unitInterval) :
    annealedFull (gridCell (oddGridWidths (fun j => if j=i then r else R)) 0) i (p:ℝ) =
      annealedFull (waterCube d i r R) i (p:ℝ) :=
  annealedFull_odd_grid_centered _ i p

end NearCritical
