module

public import NearCritical.CubeWaterChain
public import NearCritical.CenteredBoundaryComparison
public import Mathlib.Algebra.Order.Archimedean.Basic

/-! The water comparison for an arbitrary common lower bound of full cube
means. This does not define or identify the infinite-volume conductivity. -/
@[expose] public section
noncomputable section
namespace NearCritical

theorem cube_lower_bound_le_relaxed_water {d : ℕ} (i : Fin d)
    (p : unitInterval) (α : ℝ)
    (hα : ∀ S : ℕ, α ≤ annealedFull (centeredBox d S) i (p : ℝ)) (r R : ℕ) :
    α ≤ annealedRelaxed (waterCube d i r R) i (p : ℝ) +
      (2*(r : ℝ)+1)^2 * (d-1 : ℕ) / (2*R+1 : ℕ) := by
  let A := annealedRelaxed (waterCube d i r R) i (p : ℝ)
  let K : ℝ := (2*(r : ℝ)+1)^2 * (d-1 : ℕ) / (2*R+1 : ℕ)
  have hfinite : ∀ m : ℕ, α ≤ A + 2*(d-1 : ℕ) /
      (2*replicatedRadius r m+1 : ℕ) + K := by
    intro m
    let q := replicatedRadius r m
    let S := replicatedRadius R q
    let k := replicatedRadius R m
    have hside : 2*S+1 = (2*k+1)*(2*r+1) := by
      dsimp [S,q,k,replicatedRadius]
      ring
    exact (hα S).trans
      ((annealedFull_cube_le_water_of_odd_multiple i r S k hside p).trans
        (annealedFull_centered_boundary_comparison i r R q p))
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨m,hm⟩ := exists_nat_gt ((2*(d-1 : ℕ) : ℝ)/ε)
  have hden : (m : ℝ) ≤ ((2*replicatedRadius r m+1 : ℕ) : ℝ) := by
    exact_mod_cast (show m ≤ 2*replicatedRadius r m+1 from by
      have := replicatedRadius_ge r m
      omega)
  have hpos : (0 : ℝ) < (2*replicatedRadius r m+1 : ℕ) := by positivity
  have hmul : (2*(d-1 : ℕ) : ℝ) < (m : ℝ)*ε := (div_lt_iff₀ hε).mp hm
  have herr : (2*(d-1 : ℕ) : ℝ)/(2*replicatedRadius r m+1 : ℕ) ≤ ε := by
    apply (div_le_iff₀ hpos).mpr
    calc
      _ ≤ (m : ℝ)*ε := hmul.le
      _ ≤ ((2*replicatedRadius r m+1 : ℕ) : ℝ)*ε :=
        mul_le_mul_of_nonneg_right hden hε.le
      _ = ε*((2*replicatedRadius r m+1 : ℕ) : ℝ) := mul_comm _ _
  have h := hfinite m
  linarith

end NearCritical
