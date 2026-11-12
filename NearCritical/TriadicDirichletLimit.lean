module
public import NearCritical.FullGridSubadditivity
public import NearCritical.CenteredGridTemplate

/-! Literal source lem.basic triadic convergence interface and its finite-cube
order consequence. Convergence/identification is a named STANDARD input, not
proved here. No infinite conductivity is defined by this module. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Filter
open scoped Topology

/-- Side length is multiplied by three at every step. -/
def triadicCubeRadius (r : ℕ) : ℕ → ℕ
  | 0 => r
  | m+1 => 3*triadicCubeRadius r m+1

lemma triadicCubeRadius_side (r m : ℕ) :
    2*triadicCubeRadius r m+1 = 3^m*(2*r+1) := by
  induction m with
  | zero => simp [triadicCubeRadius]
  | succ m hm =>
    change 2*(3*triadicCubeRadius r m+1)+1 = _
    calc
      _ = 3*(2*triadicCubeRadius r m+1) := by ring
      _ = 3*(3^m*(2*r+1)) := by rw [hm]
      _ = _ := by rw [pow_succ]; ring

/-- Actual full Dirichlet mean decreases under exact threefold tiling. -/
lemma annealedFull_cube_triple_le {d : ℕ} (i : Fin d) (r : ℕ) (p : unitInterval) :
    annealedFull (centeredBox d (3*r+1)) i (p:ℝ) ≤
      annealedFull (centeredBox d r) i (p:ℝ) := by
  let w := oddGridWidths (fun _ : Fin d => r)
  let N : Vertex d := fun _ => 3
  have hw : ∀ j, 0 < w j := by intro j; dsimp [w,oddGridWidths]; omega
  have hN : ∀ j, 0 < N j := by intro j; norm_num [N]
  have hs : latticeRectangle 0 (fun j => N j*w j-1) =
      gridCell (oddGridWidths (fun _ : Fin d => 3*r+1)) 0 := by
    simp only [gridCell,Pi.zero_apply,zero_mul,zero_add]
    apply congrArg (latticeRectangle (0:Vertex d))
    funext j
    dsimp [N,w,oddGridWidths]
    ring
  have H := annealedFull_grid_subadditivity i w N hw hN p
  rw [hs,annealedFull_odd_grid_centered,annealedFull_odd_grid_centered] at H
  exact H

lemma annealedFull_triadic_le_initial {d : ℕ} (i : Fin d) (r m : ℕ) (p : unitInterval) :
    annealedFull (centeredBox d (triadicCubeRadius r m)) i (p:ℝ) ≤
      annealedFull (centeredBox d r) i (p:ℝ) := by
  induction m with
  | zero => exact le_rfl
  | succ m hm => exact (annealedFull_cube_triple_le i (triadicCubeRadius r m) p).trans hm

/-- Named STANDARD source lem.basic/eq.def_sigma convergence specialization:
Armstrong2018 Section5, Dario2021 eq181. The SAME supplied coefficient is the
actual full-cube mean limit for EVERY initial odd side. No rate is assumed.
This does not supply its existence or identify a random-walk diffusivity. -/
def TriadicDirichletLimitInput (d : ℕ) (i : Fin d) (κ : ℝ → ℝ) : Prop :=
  ∀ (p : unitInterval), criticalPoint d < p → ∀ r : ℕ,
    Tendsto (fun m : ℕ => annealedFull (centeredBox d (triadicCubeRadius r m)) i (p:ℝ))
      atTop (𝓝 (κ (p:ℝ)))

/-- Finite-cube domination is DERIVED, rather than inserted as the standard
input. Only the literal triadic limit and actual finite tiling are used. -/
theorem triadic_limit_le_full_cube {d : ℕ} (i : Fin d) {κ : ℝ → ℝ}
    (limitInput : TriadicDirichletLimitInput d i κ) (p : unitInterval)
    (hp : criticalPoint d < p) (r : ℕ) :
    κ (p:ℝ) ≤ annealedFull (centeredBox d r) i (p:ℝ) := by
  exact le_of_tendsto (limitInput p hp r)
    (Filter.Eventually.of_forall (fun m => annealedFull_triadic_le_initial i r m p))

end NearCritical
