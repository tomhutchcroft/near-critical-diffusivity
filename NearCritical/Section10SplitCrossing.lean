module

public import NearCritical.Section10SplitCorridor

/-! The `delta n^2` bound for a split face of the origin typical cube.

* `splitTarget t f pl R`: the points of the corridor beyond the split face at
  signed height exactly `N + R` (`N = (t-1)/2`).
* `splitTarget_not_mem_cube`, `splitFace_far_from_target`: the target is
  outside the cube and at distance at least `R` from the split face.
* `splitCrossing_small_count_le`: for a root `x` of the cube,

  `P[ x crosses to the target inside the corridor, |C(x) ∩ splitFace| <= m ]
      <= m * alpha * P[ C(x) ∩ splitFace nonempty ]`

  whenever `alpha` bounds the one-arm probability to distance `r < R`.
-/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open MeasureTheory
open scoped Classical

/-- Far end of the split corridor. -/
def splitTarget {d : ℕ} (t : ℕ) (f : Fin d × Bool) (pl : Bool) (R : ℕ) : Finset (Vertex d) :=
  (splitBeyond t f pl R).filter fun u =>
    faceHeight f u = (((t - 1) / 2 : ℕ) : ℤ) + (R : ℤ)

lemma splitTarget_not_mem_cube {d : ℕ} (t : ℕ) (ht : 1 ≤ t) (f : Fin d × Bool) (pl : Bool)
    (R : ℕ) : ∀ y₀ ∈ splitTarget t f pl R, y₀ ∉ typicalCube t (0 : Vertex d) := by
  intro y₀ hy₀ hcube
  obtain ⟨i, s⟩ := f
  obtain ⟨hB, _⟩ := Finset.mem_filter.mp hy₀
  obtain ⟨_, hheight, _⟩ := Finset.mem_filter.mp hB
  have hc := (mem_typicalCube_iff_int (by omega) 0 y₀).mp hcube i
  simp only [Pi.zero_apply, sub_zero] at hc
  cases s <;> simp only [faceHeight] at hheight <;> simp at hheight <;> omega

lemma splitFace_far_from_target {d : ℕ} (t : ℕ) (f : Fin d × Bool) (pl : Bool) (R : ℕ)
    {r : ℝ} (hr : r < (R : ℝ)) :
    ∀ y ∈ typicalSplitFace t (0 : Vertex d) f pl, ∀ y₀ ∈ splitTarget t f pl R,
      r < dist y y₀ := by
  intro y hy y₀ hy₀
  obtain ⟨i, s⟩ := f
  obtain ⟨_, hh⟩ := Finset.mem_filter.mp hy₀
  obtain ⟨hface, _⟩ := Finset.mem_filter.mp hy
  obtain ⟨_, hyi⟩ := Finset.mem_filter.mp hface
  have hyi' : y i = if s then (((t - 1) / 2 : ℕ) : ℤ) else -(((t - 1) / 2 : ℕ) : ℤ) := by
    simpa using hyi
  have hcoord : dist (y i) (y₀ i) ≤ dist y y₀ := dist_le_pi_dist y y₀ i
  have hR : (R : ℝ) ≤ dist (y i) (y₀ i) := by
    rw [Int.dist_eq]
    have hdiff : |y i - y₀ i| = (R : ℤ) := by
      cases s <;> simp only [faceHeight] at hh <;> simp at hh hyi' <;>
        rw [abs_eq (by positivity)] <;> omega
    have : ((|y i - y₀ i| : ℤ) : ℝ) = (R : ℝ) := by
      rw [hdiff]
      norm_cast
    rw [← this]
    push_cast
    exact le_refl _
  linarith

/-- **Crossing through a split face with few exit points is unlikely.** -/
theorem splitCrossing_small_count_le {d : ℕ} (p : unitInterval) (t : ℕ) (ht : 1 ≤ t)
    (f : Fin d × Bool) (pl : Bool) (R : ℕ) {x : Vertex d}
    (hx : x ∈ typicalCube t (0 : Vertex d)) {r : ℝ} (hr : r < (R : ℝ)) (m : ℕ) {α : ℝ}
    (hα : ∀ y : Vertex d, (percolation d p).real (extrinsicRadiusArmEvent y r) ≤ α) :
    (percolation d p).real
      ({ω | ∃ y₀ ∈ splitTarget t f pl R, ∃ w : (openGraph ω).Walk x y₀,
          ∀ z ∈ w.support, z ∈ splitCorridor t f pl R} ∩
        {ω | (finiteBoxCluster ω (typicalCube t (0 : Vertex d)) x ∩
          typicalSplitFace t (0 : Vertex d) f pl).card ≤ m}) ≤
      (m : ℝ) * α * (percolation d p).real
        {ω | (finiteBoxCluster ω (typicalCube t (0 : Vertex d)) x ∩
          typicalSplitFace t (0 : Vertex d) f pl).Nonempty} :=
  crossing_small_count_le p (splitCorridor t f pl R) (typicalCube t (0 : Vertex d))
    (typicalSplitFace t (0 : Vertex d) f pl) (splitTarget t f pl R) hx
    (splitTarget_not_mem_cube t ht f pl R) (splitCorridor_exit t ht f pl R) r
    (splitFace_far_from_target t f pl R hr) m hα

end NearCritical.Section10
