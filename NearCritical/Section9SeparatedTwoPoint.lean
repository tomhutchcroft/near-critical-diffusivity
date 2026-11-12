module

public import NearCritical.Section9MiddleGeometry
public import NearCritical.ThreePointDiagram
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! Actual source middle/end-cube separation and quantitative two-point decay.
Only the paper's existing TwoPointAsymptotics assumption is used. -/
@[expose] public section
noncomputable section
namespace NearCritical
open scoped Classical

lemma section9_coordinate_gap_le_norm {d : ℕ} (i : Fin d) (x y : Vertex d) :
    |(x i : ℝ) - (y i : ℝ)| ≤ euclideanNorm (x-y) := by
  have h := dist_le_pi_dist (vertexReal x) (vertexReal y) i
  have hc : |(x i : ℝ) - (y i : ℝ)| ≤ latticeDistance x y := by
    simpa only [latticeDistance, Real.dist_eq, vertexReal] using h
  exact hc.trans (latticeDistance_le_euclidean x y)

theorem section9Middle_first_separation {d : ℕ} (i : Fin d) (n : ℕ)
    {x y : Vertex d} (hx : x ∈ section9FiniteMiddle i n)
    (hy : y ∈ section9FiniteEndCube i n 0) :
    (n:ℝ)/8 ≤ euclideanNorm (x-y) := by
  have hm := (Finset.mem_filter.mp hx).2
  have hc := (Finset.mem_filter.mp hy).2
  have hl := hm.1
  have hu := (hc i).2
  simp only [ite_true, sub_zero] at hu
  have hgap : (n:ℝ)/8 ≤ (x i : ℝ) - (y i : ℝ) := by linarith
  exact hgap.trans ((le_abs_self _).trans (section9_coordinate_gap_le_norm i x y))

theorem section9Middle_third_separation {d : ℕ} (i : Fin d) (n : ℕ)
    {x y : Vertex d} (hx : x ∈ section9FiniteMiddle i n)
    (hy : y ∈ section9FiniteEndCube i n (2*(n:ℝ))) :
    (n:ℝ)/8 ≤ euclideanNorm (x-y) := by
  have hm := (Finset.mem_filter.mp hx).2
  have hc := (Finset.mem_filter.mp hy).2
  have hu := hm.2.1
  have hl := (hc i).1
  simp only [ite_true] at hl
  have hgap : (n:ℝ)/8 ≤ (y i : ℝ) - (x i : ℝ) := by linarith
  have ha : (y i : ℝ) - (x i : ℝ) ≤ |(x i : ℝ) - (y i : ℝ)| := by
    rw [abs_sub_comm]
    exact le_abs_self _
  exact hgap.trans (ha.trans (section9_coordinate_gap_le_norm i x y))

/-- The source asymptotics already supply a constant uniform in scale and
endpoints separated by n/8. Dimension two is allowed; Section9 uses d>=9. -/
theorem section9TwoPoint_separated_bound {d : ℕ} (hd : 2 ≤ d)
    (h : TwoPointAsymptotics d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℝ), 0 < n → ∀ x y : Vertex d,
      n/8 ≤ euclideanNorm (x-y) →
      twoPoint d (criticalPoint d) x y ≤ C * (n/8) ^ ((2:ℝ)-(d:ℝ)) := by
  obtain ⟨C,hC,hb⟩ := critical_twoPoint_global_upper hd h
  refine ⟨C,hC,?_⟩
  intro n hn x y hsep
  have hd' : (2:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
  have hp := Real.rpow_le_rpow_of_nonpos (div_pos hn (by norm_num : (0:ℝ)<8))
    (hsep.trans (le_max_right 1 _)) (sub_nonpos.mpr hd')
  exact (hb x y).trans (mul_le_mul_of_nonneg_left hp hC.le)

/-- Uniform quantitative decay for actual finite middle-to-end-cube pairs.
The same constant works for either end cube and every positive integer scale. -/
theorem section9TwoPoint_middle_end_bounds {d : ℕ} (hd : 2 ≤ d)
    (h : TwoPointAsymptotics d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (i : Fin d) (n : ℕ), 0 < n →
      ∀ x ∈ section9FiniteMiddle i n, ∀ y : Vertex d,
      y ∈ section9FiniteEndCube i n 0 ∨ y ∈ section9FiniteEndCube i n (2*(n:ℝ)) →
      twoPoint d (criticalPoint d) x y ≤ C * ((n:ℝ)/8) ^ ((2:ℝ)-(d:ℝ)) := by
  obtain ⟨C,hC,hb⟩ := section9TwoPoint_separated_bound hd h
  refine ⟨C,hC,?_⟩
  intro i n hn x hx y hy
  apply hb (n:ℝ) (by exact_mod_cast hn) x y
  rcases hy with hy | hy
  · exact section9Middle_first_separation i n hx hy
  · exact section9Middle_third_separation i n hx hy

end NearCritical
