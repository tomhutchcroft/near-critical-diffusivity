module
public import NearCritical.Section9MiddleGeometry
public import NearCritical.ThreePointDiagram
import Mathlib.Tactic.Linarith

/-! Sup-distance geometry for the shared-target tripod estimate. -/
@[expose] public section
noncomputable section
namespace NearCritical
open scoped Classical

/-- Separation in the actual sup metric used by the clipped Green kernel. -/
theorem section9_middle_third_sup_separation {d : ℕ} (i : Fin d) (n : ℕ)
    {x y : Vertex d} (hx : x ∈ section9FiniteMiddle i n)
    (hy : y ∈ section9FiniteEndCube i n (2*(n : ℝ))) :
    (n : ℝ)/8 ≤ latticeDistance x y := by
  have hm := (Finset.mem_filter.mp hx).2
  have hc := (Finset.mem_filter.mp hy).2
  have hu := hm.2.1
  have hl := (hc i).1
  simp only [ite_true] at hl
  have hgap : (n : ℝ)/8 ≤ (y i : ℝ)-(x i : ℝ) := by linarith
  have habs : (y i : ℝ)-(x i : ℝ) ≤ |(x i : ℝ)-(y i : ℝ)| := by
    rw [abs_sub_comm]
    exact le_abs_self _
  have hcoord : |(x i : ℝ)-(y i : ℝ)| ≤ latticeDistance x y := by
    simpa only [latticeDistance,Real.dist_eq,vertexReal] using
      dist_le_pi_dist (vertexReal x) (vertexReal y) i
  exact hgap.trans (habs.trans hcoord)

/-- Any two vertices of one open end cube are at sup distance at most n. -/
theorem section9_end_cube_sup_diameter {d : ℕ} (i : Fin d) (n : ℕ) (center : ℝ)
    {x y : Vertex d} (hx : x ∈ section9FiniteEndCube i n center)
    (hy : y ∈ section9FiniteEndCube i n center) : latticeDistance x y ≤ (n : ℝ) := by
  have hxc := (Finset.mem_filter.mp hx).2
  have hyc := (Finset.mem_filter.mp hy).2
  apply (dist_pi_le_iff (Nat.cast_nonneg n : (0 : ℝ) ≤ n)).mpr
  intro j
  have hxj := hxc j
  have hyj := hyc j
  simp only [Real.dist_eq,vertexReal]
  apply abs_le.mpr
  constructor <;> linarith [hxj.1,hxj.2,hyj.1,hyj.2]

end NearCritical
