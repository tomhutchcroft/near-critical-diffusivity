module

public import NearCritical.Section10SplitLowerCount
public import NearCritical.WaterCubeOrdinaryArms
public import NearCritical.PreGoodUpperCount

/-! The all-faces crossing event implies spanning; the one-arm constant.

* `crossSplit_meets_splitFace`: a crossing of a split corridor from a root of
  the cube forces the root's cluster to meet that split face.
* `crossAll_subset_spanning`: hence `crossAll` is contained in the spanning
  event of the origin typical cube (all faces `typicalFace t 0 f`).
* `ordinaryArm_alpha`: from the cited ordinary one-arm window input, the
  one-arm probability at `p_c` to distance `t/2` is at most `C/t^2`, for every
  vertex. This is the constant `alpha` of `crossAll_lower_failure` with
  `r = t/2 < R = t`.
-/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open MeasureTheory
open scoped Classical

theorem crossSplit_meets_splitFace {d : ℕ} (t : ℕ) (ht : 1 ≤ t) (f : Fin d × Bool) (pl : Bool)
    (R : ℕ) {x : Vertex d} (hx : x ∈ typicalCube t (0 : Vertex d)) {ω : Configuration d}
    (hω : ω ∈ crossSplit t f pl R x) :
    (finiteBoxCluster ω (typicalCube t (0 : Vertex d)) x ∩
      typicalSplitFace t (0 : Vertex d) f pl).Nonempty := by
  obtain ⟨y₀, hy₀, w, hW⟩ := hω
  obtain ⟨y, hy, _⟩ := exists_avoidArm_on_face (splitCorridor t f pl R)
    (typicalCube t (0 : Vertex d)) (typicalSplitFace t (0 : Vertex d) f pl) hx w hW
    (splitTarget_not_mem_cube t ht f pl R y₀ hy₀) (splitCorridor_exit t ht f pl R) (-1)
    (fun y _ => lt_of_lt_of_le (by norm_num) dist_nonneg)
  exact ⟨y, hy⟩

theorem crossAll_subset_spanning {d : ℕ} (t : ℕ) (ht : 1 ≤ t) (R : ℕ) {x : Vertex d}
    (hx : x ∈ typicalCube t (0 : Vertex d)) :
    crossAll t R x ⊆
      finiteRootSpanningEvent (typicalCube t (0 : Vertex d)) (typicalFace t (0 : Vertex d)) x := by
  intro ω hω f
  obtain ⟨y, hy⟩ := crossSplit_meets_splitFace t ht f true R hx (hω (f, true))
  obtain ⟨hyC, hyS⟩ := Finset.mem_inter.mp hy
  exact ⟨y, Finset.mem_inter.mpr ⟨hyC, (Finset.mem_filter.mp hyS).1⟩⟩

theorem ordinaryArm_alpha {d : ℕ} {C : ℝ} (ordinary : OrdinaryArmWindowInput d C) (t : ℕ)
    (ht : 1 ≤ t) (y : Vertex d) :
    (percolation d (criticalPoint d)).real (extrinsicRadiusArmEvent y ((t : ℝ) / 2)) ≤
      C / (t : ℝ) ^ 2 := by
  refine ordinary (criticalPoint d) y t ht ?_
  have : (0:ℝ) ≤ ((t : ℝ) ^ 2)⁻¹ := by positivity
  linarith

end NearCritical.Section10
