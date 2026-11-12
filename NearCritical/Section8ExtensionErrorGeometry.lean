module
public import NearCritical.Section8ExtensionSourceGeometry
public import NearCritical.ThreePointDiagram

/-! Actual small-cube and source separation geometry for extension errors. -/
@[expose] public section
noncomputable section
namespace NearCritical
open scoped Classical

/-- Literal S=Λ_(3n/4): an OPEN cube of side length 3n/4 centered at zero. -/
def section8ExtensionSmallCube {d : ℕ} (i : Fin d) (n : ℕ) : Finset (Vertex d) :=
  (centeredBox d (3*n)).filter fun y =>
    y ∈ sprinklingEndCube i (3*(n : ℝ)/4) 0

/-- T12 lies strictly beyond the small cube's positive axial face. -/
theorem section8_extension_tube_disjoint_small_cube {d : ℕ} (i : Fin d) (n : ℕ) :
    Disjoint (section9FiniteTube i n (-(5 : ℝ)/8) (3/8))
      (section8ExtensionSmallCube i n) := by
  apply Finset.disjoint_left.mpr
  intro y hyTube hySmall
  have hTube := (Finset.mem_filter.mp hyTube).2.1
  have hSmall := ((Finset.mem_filter.mp hySmall).2 i).2
  simp only [ite_true,sub_zero] at hSmall
  linarith

private theorem extension_coordinate_gap_le_distance {d : ℕ}
    (a b : Vertex d) (i : Fin d) : (b i : ℝ)-(a i : ℝ) ≤ latticeDistance a b := by
  have hcoord : |(a i : ℝ)-(b i : ℝ)| ≤ latticeDistance a b := by
    simpa only [latticeDistance,vertexReal,Real.dist_eq] using
      dist_le_pi_dist (vertexReal a) (vertexReal b) i
  have hab : (b i : ℝ)-(a i : ℝ) ≤ |(a i : ℝ)-(b i : ℝ)| := by
    rw [abs_sub_comm]
    exact le_abs_self _
  exact hab.trans hcoord

/-- Actual source geometry supplies the ERE2 separation assumptions. The
shifted a-z separation is n/8, while the unshifted y-z separation is n/4;
the near-pair kernel remains bounded only above by 2n. -/
theorem section8_extension_error_source_distances {d : ℕ}
    (i : Fin d) (n r : ℕ) (hn : 16*(r+1) ≤ n) {x z : Vertex d}
    (hx : x ∈ section8ExtensionPositiveFaceCore i n)
    (hz : z ∈ section8ExtensionMiddleCore i n) :
    let a := Function.update x i (x i+(r : ℤ))
    (n : ℝ)/8 ≤ latticeDistance a z ∧
      ∀ y ∈ section9FiniteEndCube i n 0,
        (n : ℝ)/4 ≤ latticeDistance y z ∧ max 1 (latticeDistance a y) ≤ 2*(n : ℝ) := by
  intro a
  have hnR : 16*((r : ℝ)+1) ≤ n := by exact_mod_cast hn
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hn16 : (16 : ℝ) ≤ n := by linarith
  have hxQ := (Finset.mem_filter.mp hx).1
  have hxShape := (Finset.mem_filter.mp hxQ).2
  have hxAxial := hxShape i
  simp only [ite_true,sub_zero] at hxAxial
  have hzShape := ((section8_mem_extension_middle_core i n z).mp hz) i
  simp only [ite_true] at hzShape
  have hai : (a i : ℝ) = (x i : ℝ)+(r : ℝ) := by
    simp only [a,Function.update_self,Int.cast_add,Int.cast_natCast]
  constructor
  · have hgap := extension_coordinate_gap_le_distance a z i
    rw [hai] at hgap
    linarith [hzShape.1,hxAxial.2]
  · intro y hy
    have hyShape := (Finset.mem_filter.mp hy).2
    have hyAxial := hyShape i
    simp only [ite_true,sub_zero] at hyAxial
    constructor
    · have hgap := extension_coordinate_gap_le_distance y z i
      linarith [hzShape.1,hyAxial.2]
    · apply max_le (by linarith : (1 : ℝ) ≤ 2*(n : ℝ))
      change dist (vertexReal a) (vertexReal y) ≤ 2*(n : ℝ)
      apply (dist_pi_le_iff (by linarith : (0 : ℝ) ≤ 2*(n : ℝ))).mpr
      intro j
      have hxj := hxShape j
      have hyj := hyShape j
      simp only [ite_self,sub_zero] at hxj hyj
      change dist (a j : ℝ) (y j : ℝ) ≤ 2*(n : ℝ)
      rw [Real.dist_eq]
      apply abs_le.mpr
      by_cases hji : j = i
      · subst j
        rw [hai]
        constructor <;> linarith [hxj.1,hxj.2,hyj.1,hyj.2]
      · have haj : a j = x j := by simp only [a,Function.update_of_ne hji]
        rw [haj]
        constructor <;> linarith [hxj.1,hxj.2,hyj.1,hyj.2]

end NearCritical
