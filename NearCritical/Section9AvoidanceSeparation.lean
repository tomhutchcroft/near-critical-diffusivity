module
public import NearCritical.Section8ReflectionGeometry
public import NearCritical.Section9ExitFace

/-! Actual source separations for the avoidance bad-hit error. -/
@[expose] public section
noncomputable section
namespace NearCritical
open scoped Classical

private theorem avoidance_coordinate_gap_le {d : ℕ} (i : Fin d) (a b : Vertex d) :
    (b i : ℝ)-(a i : ℝ) ≤ latticeDistance a b := by
  have hcoord : |(a i : ℝ)-(b i : ℝ)| ≤ latticeDistance a b := by
    simpa only [latticeDistance,vertexReal,Real.dist_eq] using
      dist_le_pi_dist (vertexReal a) (vertexReal b) i
  have hgap : (b i : ℝ)-(a i : ℝ) ≤ |(a i : ℝ)-(b i : ℝ)| := by
    rw [abs_sub_comm]
    exact le_abs_self _
  exact hgap.trans hcoord

private theorem avoidance_exit_axial_bounds {d : ℕ} (i : Fin d) (n : ℕ)
    {v : Vertex d} (hv : v ∈ section9ExitFace i n) :
    11*(n : ℝ)/8-1 ≤ (v i : ℝ) ∧ (v i : ℝ) < 11*(n : ℝ)/8 := by
  obtain ⟨hvT,hvTip⟩ := Finset.mem_filter.mp hv
  have hshape := (Finset.mem_filter.mp hvT).2
  have hlower : (n : ℝ)+(3/8)*(n : ℝ) ≤ (v i : ℝ)+1 := by
    apply le_of_not_gt
    intro hupper
    apply hvTip
    apply (mem_section9FiniteTube i n (-(5 : ℝ)/8) (3/8)
      (by norm_num) (by norm_num) (bondTip (v,i))).mpr
    refine ⟨?_,?_,?_⟩
    · simp only [bondTip,Function.update_self,Int.cast_add,Int.cast_one]
      linarith [hshape.1]
    · simpa only [bondTip,Function.update_self,Int.cast_add,Int.cast_one] using hupper
    · intro j hji
      simpa only [bondTip,Function.update_of_ne hji] using hshape.2.2 j hji
  constructor <;> linarith [hshape.2.1]

/-- All three pairs in the source bad-hit tripod are separated by n/16.
The actual discrete exit face has coordinate at least11n/8-1; no exact face
coordinate or parity convention is assumed. -/
theorem section9_source_avoidance_pair_separation {d : ℕ} (i : Fin d) (n : ℕ)
    (hn : 16 ≤ n) (z y v : Vertex d)
    (hz : z ∈ section8ExtensionMiddleCore i n)
    (hy : y ∈ section8ExtensionNegativeFaceCore i n)
    (hv : v ∈ section9ExitFace i n) :
    (n : ℝ)/16 ≤ latticeDistance z y ∧
      (n : ℝ)/16 ≤ latticeDistance z v ∧
      (n : ℝ)/16 ≤ latticeDistance y v := by
  have hnR : (16 : ℝ) ≤ n := by exact_mod_cast hn
  have hzShape := ((section8_mem_extension_middle_core i n z).mp hz) i
  simp only [ite_true] at hzShape
  have hyQ := (Finset.mem_filter.mp hy).1
  have hyShape := (Finset.mem_filter.mp hyQ).2 i
  simp only [ite_true] at hyShape
  have hvAxial := avoidance_exit_axial_bounds i n hv
  have hzy := avoidance_coordinate_gap_le i z y
  have hzv := avoidance_coordinate_gap_le i z v
  have hyv := avoidance_coordinate_gap_le i v y
  rw [latticeDistance_comm v y] at hyv
  refine ⟨?_,?_,?_⟩
  · linarith [hzShape.2,hyShape.1]
  · linarith [hzShape.2,hvAxial.1]
  · linarith [hyShape.1,hvAxial.2]

end NearCritical
