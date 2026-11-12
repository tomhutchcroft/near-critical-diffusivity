module

public import NearCritical.ThreePointDiagram
public import NearCritical.ConnectionToSet
public import NearCritical.Section9MiddleGeometry
import Mathlib.Tactic.Linarith

@[expose] public section
namespace NearCritical
open MeasureTheory
open scoped Classical

/-- A uniform lower bound on the three pairwise separations gives the
Case 2 power for the joint connection, under the explicit tree-graph inputs. -/
theorem section9_separated_three_point_le {d : ℕ} (hd : 4 < d)
    (asymptotics : TwoPointAsymptotics d) {B : ℝ} (hB : 0 < B)
    (bubble : CriticalSpatialBubbleInput d B) (tree : ThreePointTreeGraphInput d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (D : Set (Vertex d)) (a b z : Vertex d) (r : ℝ), 0 < r →
      r ≤ latticeDistance a b → r ≤ latticeDistance b z → r ≤ latticeDistance a z →
      (percolation d (criticalPoint d)).real
        (connectionToSetEvent D a {b} ∩ connectionToSetEvent D a {z}) ≤
          C * r ^ (6 - 2 * (d : ℝ)) := by
  obtain ⟨C, hC, h⟩ :=
    threePoint_probability_upper_of_asymptotics_and_standard_inputs hd asymptotics hB bubble tree
  refine ⟨C, hC, ?_⟩
  intro D a b z r hr hab hbz haz
  have ne_of_bound (u v : Vertex d) (huv : r ≤ latticeDistance u v) : u ≠ v := by
    rintro rfl
    exact (not_le_of_gt hr) (by simpa [latticeDistance] using huv)
  have hMin : r ≤ tripleMinSeparation a b z := le_min hab (le_min hbz haz)
  have hMax : r ≤ tripleMaxSeparation a b z := hab.trans (le_max_left _ _)
  have hd' : (4 : ℝ) ≤ d := by exact_mod_cast hd.le
  have hsub : connectionToSetEvent D a {b} ∩ connectionToSetEvent D a {z} ⊆
      connectionEvent a b ∩ connectionEvent a z := by
    rintro ω ⟨⟨_, u, hu, _, hau⟩, ⟨_, v, hv, _, hav⟩⟩
    have hu' : u = b := hu
    have hv' : v = z := hv
    subst u
    subst v
    have hle : restrictedGraph ω D ≤ openGraph ω := fun _ _ h => h.1
    exact ⟨hau.mono hle, hav.mono hle⟩
  calc
    _ ≤ _ := measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ _ := h a b z (ne_of_bound a b hab) (ne_of_bound b z hbz) (ne_of_bound a z haz)
    _ ≤ C * r ^ ((4 : ℝ) - (d : ℝ)) * r ^ ((2 : ℝ) - (d : ℝ)) := by
      have hmin := Real.rpow_le_rpow_of_nonpos hr hMin (sub_nonpos.mpr hd')
      have hmax := Real.rpow_le_rpow_of_nonpos hr hMax
        (sub_nonpos.mpr ((by norm_num : (2 : ℝ) ≤ 4).trans hd'))
      exact mul_le_mul (mul_le_mul_of_nonneg_left hmin hC.le) hmax
        (Real.rpow_nonneg (hr.le.trans hMax) _) (mul_nonneg hC.le (Real.rpow_nonneg hr.le _))
    _ = _ := by
      rw [mul_assoc, ← Real.rpow_add hr]
      congr 1
      ring

/-- The actual first, middle and third regions give all three
separations in the supremum metric used by the diagram. -/
theorem section9_cross_terminal_separations {d : ℕ} (i : Fin d) (n : ℕ)
    {a b z : Vertex d} (ha : a ∈ section9FiniteMiddle i n)
    (hb : b ∈ section9FiniteEndCube i n 0)
    (hz : z ∈ section9FiniteEndCube i n (2*(n:ℝ))) :
    (n:ℝ)/8 ≤ latticeDistance a b ∧ (n:ℝ)/8 ≤ latticeDistance b z ∧
      (n:ℝ)/8 ≤ latticeDistance a z := by
  have hm := (Finset.mem_filter.mp ha).2
  have hLo := hm.1
  have hHi := hm.2.1
  have hFirst := ((Finset.mem_filter.mp hb).2 i).2
  have hThird := ((Finset.mem_filter.mp hz).2 i).1
  simp only [ite_true, sub_zero] at hFirst
  simp only [ite_true] at hThird
  have hCoord (u v : Vertex d) : |(u i : ℝ) - (v i : ℝ)| ≤ latticeDistance u v := by
    simpa only [latticeDistance, vertexReal, Real.dist_eq] using
      dist_le_pi_dist (vertexReal u) (vertexReal v) i
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  refine ⟨?_, ?_, ?_⟩
  · exact (show (n:ℝ)/8 ≤ (a i : ℝ) - (b i : ℝ) by linarith).trans
      ((le_abs_self _).trans (hCoord a b))
  · have hAbs : (z i : ℝ) - (b i : ℝ) ≤ |(b i : ℝ) - (z i : ℝ)| := by
      rw [abs_sub_comm]
      exact le_abs_self _
    exact (show (n:ℝ)/8 ≤ (z i : ℝ) - (b i : ℝ) by linarith).trans
      (hAbs.trans (hCoord b z))
  · have hAbs : (z i : ℝ) - (a i : ℝ) ≤ |(a i : ℝ) - (z i : ℝ)| := by
      rw [abs_sub_comm]
      exact le_abs_self _
    exact (show (n:ℝ)/8 ≤ (z i : ℝ) - (a i : ℝ) by linarith).trans
      (hAbs.trans (hCoord a z))

/-- The joint Case 2 connection to the other root and a target is
bounded by the separated three-point estimate summed over targets. -/
theorem section9_cross_joint_arm_le {d : ℕ} (hd : 4 < d)
    (asymptotics : TwoPointAsymptotics d) {B₀ : ℝ} (hB₀ : 0 < B₀)
    (bubble : CriticalSpatialBubbleInput d B₀) (tree : ThreePointTreeGraphInput d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (i : Fin d) (n : ℕ), 0 < n →
      ∀ (D : Set (Vertex d)) (B : Finset (Vertex d)) (a b : Vertex d),
      a ∈ section9FiniteMiddle i n → b ∈ section9FiniteEndCube i n 0 →
      B ⊆ section9FiniteEndCube i n (2*(n:ℝ)) →
      (percolation d (criticalPoint d)).real
        (connectionToSetEvent D a {b} ∩ connectionToSetEvent D a (B : Set (Vertex d))) ≤
          (B.card : ℝ) * (C * ((n:ℝ)/8) ^ (6 - 2 * (d : ℝ))) := by
  obtain ⟨C, hC, h⟩ := section9_separated_three_point_le hd asymptotics hB₀ bubble tree
  refine ⟨C, hC, ?_⟩
  intro i n hn D B a b ha hb hB
  let E := fun z => connectionToSetEvent D a {b} ∩ connectionToSetEvent D a {z}
  have hsub : connectionToSetEvent D a {b} ∩ connectionToSetEvent D a (B : Set (Vertex d)) ⊆
      ⋃ z ∈ B, E z := by
    rintro ω ⟨hab, ⟨haD, z, hz, hzD, haz⟩⟩
    exact Set.mem_iUnion.mpr ⟨z, Set.mem_iUnion.mpr ⟨hz, hab, ⟨haD, z, rfl, hzD, haz⟩⟩⟩
  refine (measureReal_mono hsub (measure_ne_top _ _)).trans ((measureReal_biUnion_finset_le B E).trans ?_)
  calc
    _ ≤ ∑ _z ∈ B, C * ((n:ℝ)/8) ^ (6 - 2 * (d : ℝ)) := by
      apply Finset.sum_le_sum
      intro z hz
      obtain ⟨hab, hbz, haz⟩ := section9_cross_terminal_separations i n ha hb (hB hz)
      exact h D a b z ((n:ℝ)/8) (div_pos (by exact_mod_cast hn) (by norm_num)) hab hbz haz
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]

end NearCritical
