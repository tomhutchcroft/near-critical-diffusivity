module

public import NearCritical.FullGridSubadditivity
public import NearCritical.CenteredGridTemplate
public import Mathlib.Tactic.Positivity

/-! The finite cube-to-water comparison at exactly divisible odd side lengths.
No infinite-volume conductivity is introduced or identified here. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Finset

theorem annealedFull_cube_le_water_of_odd_multiple {d : ℕ} (i : Fin d)
    (r R k : ℕ) (hside : 2*R+1 = (2*k+1)*(2*r+1)) (p : unitInterval) :
    annealedFull (centeredBox d R) i (p : ℝ) ≤
      annealedFull (waterCube d i r R) i (p : ℝ) := by
  classical
  let w := oddGridWidths (fun j => if j=i then r else R)
  let N : Vertex d := fun j => if j=i then ((2*k+1 : ℕ) : ℤ) else 1
  have hw : ∀ j, 0 < w j := by
    intro j
    dsimp only [w,oddGridWidths]
    positivity
  have hN : ∀ j, 0 < N j := by
    intro j
    dsimp only [N]
    split_ifs <;> positivity
  have htotal : latticeRectangle 0 (fun j => N j * w j - 1) =
      gridCell (oddGridWidths (fun _ : Fin d => R)) 0 := by
    simp only [gridCell,Pi.zero_apply,zero_mul,zero_add]
    apply congrArg (latticeRectangle (0 : Vertex d))
    funext j
    by_cases hji : j=i
    · simp only [N,w,oddGridWidths,hji,↓reduceIte]
      have hcast : ((2*k+1 : ℕ) : ℤ) * (2*(r : ℤ)+1) = 2*(R : ℤ)+1 := by
        exact_mod_cast hside.symm
      omega
    · simp [N,w,oddGridWidths,hji]
  have hp := annealedFull_grid_subadditivity i w N hw hN p
  rw [htotal,annealedFull_odd_grid_centered,annealedFull_waterCube_grid] at hp
  exact hp

end NearCritical
