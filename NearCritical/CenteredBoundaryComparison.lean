module
public import NearCritical.FiniteBoundaryComparison
public import NearCritical.CenteredGridTemplate

/-! Literal centered odd-watercube finite boundary comparison in lem.chain.2.
Actual support/centering and Bernoulli means are derived, not premises. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Finset
open scoped Classical

/-- Replicating an odd interval 2R+1 an odd number 2m+1 of times preserves
oddness, with this EXACT radius. -/
def replicatedRadius (R m : ℕ) : ℕ := (2*m+1)*R+m

lemma replicatedRadius_side (R m : ℕ) :
    2*replicatedRadius R m+1 = (2*m+1)*(2*R+1) := by
  unfold replicatedRadius
  ring

lemma replicatedRadius_ge (R m : ℕ) : m ≤ replicatedRadius R m := by
  unfold replicatedRadius
  omega

/-- Exact zero-based support of the replicated rectangle. -/
theorem replicated_waterCube_grid_support {d : ℕ} (i : Fin d) (r R m : ℕ) :
    latticeRectangle 0 (fun j =>
      (if j=i then 1 else (2*m+1:ℕ) : ℤ)*
        oddGridWidths (fun k => if k=i then r else R) j-1) =
      gridCell (oddGridWidths (fun j => if j=i then r else replicatedRadius R m)) 0 := by
  simp only [gridCell,Pi.zero_apply,zero_mul,zero_add]
  apply congrArg (latticeRectangle (0:Vertex d))
  funext j
  by_cases hj : j=i
  · simp [oddGridWidths,hj]
  · simp [oddGridWidths,hj,replicatedRadius]
    ring

/-- Actual centered form of the finite full-versus-relaxed comparison. It
holds for ALL radii, all odd replication counts, and every p in[0,1]. -/
theorem annealedFull_centered_boundary_comparison {d : ℕ} (i : Fin d)
    (r R m : ℕ) (p : unitInterval) :
    annealedFull (waterCube d i r (replicatedRadius R m)) i (p:ℝ) ≤
      annealedRelaxed (waterCube d i r R) i (p:ℝ)+
        2*(d-1:ℕ)/(2*m+1:ℕ)+(2*(r:ℝ)+1)^2*(d-1:ℕ)/(2*R+1:ℕ) := by
  let w := oddGridWidths (fun j => if j=i then r else R)
  let N : Vertex d := fun j => if j=i then 1 else (2*m+1:ℕ)
  have hw : ∀ j, 0 < w j := by intro j; dsimp [w,oddGridWidths]; split <;> omega
  have hN : ∀ j, 0 < N j := by intro j; dsimp [N]; split <;> omega
  have H := annealedFull_grid_boundary_comparison i w N hw hN
    (by simp [N]) (2*R+1) (2*m+1) (by omega) (by omega)
    (by intro j hj; simp [w,oddGridWidths,hj])
    (by intro j hj; simp [N,hj]) p
  have hs : latticeRectangle 0 (fun j => N j*w j-1) =
      gridCell (oddGridWidths (fun j => if j=i then r else replicatedRadius R m)) 0 :=
    replicated_waterCube_grid_support i r R m
  rw [hs,annealedFull_waterCube_grid,annealedRelaxed_waterCube_grid] at H
  simpa only [w,oddGridWidths,ite_true,Int.cast_add,Int.cast_mul,Int.cast_ofNat,Int.cast_natCast,Int.cast_one] using H

end NearCritical
