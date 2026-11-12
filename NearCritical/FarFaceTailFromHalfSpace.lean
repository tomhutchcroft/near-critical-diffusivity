module

public import NearCritical.Section7FaceDiameter
public import Mathlib.Combinatorics.SimpleGraph.Metric

/-! The far-face tail from the half-space longest-path tail.

Source (main.tex 1512-1542): CHS23 (105) bounds
`sup_x E_{p_c}[L(x) 1{x <-> ∂H}]` for the longest self-avoiding open path `L(x)`
from `x` to `∂H` in a half-space `H`; the paper then uses that a geodesic of the
box from `x` to a face is such a path, and Markov's inequality.

* `HalfSpaceLongPathTail d K`: the Markov consequence of (105), stated for every
  axis half-space (the lattice symmetries carry the paper's `H` to each of
  them): the probability that some self-avoiding open path of length at least
  `T` joins `x` to the boundary hyperplane inside the half-space is at most `K/T`.
  This is the CITED-level input.
* `farFaceEvent_subset_halfSpacePath`: the deterministic step. On the far-face
  event, a geodesic of the box-restricted graph from `x` to the far face point
  is a self-avoiding open path in the half-space bounded by that face.
* `faceReachTail_of_halfSpaceLongPath`: hence the far-face tail
  `P_{p_c}[farFaceEvent N x f T] <= K/T`, the hypothesis `htail` of the pre-good,
  time-constant and slab theorems.

Not formalized: the moment statement (105) itself (it needs the random variable
`L(x)`), and its Markov step; they are replaced by the tail input above.
-/

@[expose] public section
noncomputable section

namespace NearCritical.Section7

open MeasureTheory
open scoped Classical

variable {d : ℕ}

/-- Axis half-space: `z i <= b` (`s = true`) or `b <= z i` (`s = false`). -/
def axisHalfSpace (i : Fin d) (b : ℤ) (s : Bool) : Set (Vertex d) :=
  {z | if s then z i ≤ b else b ≤ z i}

/-- Some self-avoiding open path of length at least `T` joins `x` to the boundary
hyperplane inside the half-space. -/
def halfSpaceLongPathEvent (i : Fin d) (b : ℤ) (s : Bool) (x : Vertex d) (T : ℝ) :
    Set (Configuration d) :=
  {ω | ∃ u : Vertex d, u i = b ∧
    ∃ p : (restrictedGraph ω (axisHalfSpace i b s)).Walk x u, p.IsPath ∧ T ≤ (p.length : ℝ)}

/-- Markov consequence of CHS23 (105), for every axis half-space. -/
def HalfSpaceLongPathTail (d : ℕ) (K : ℝ) : Prop :=
  ∀ (i : Fin d) (b : ℤ) (s : Bool) (x : Vertex d) (T : ℝ), 0 < T →
    (percolation d (criticalPoint d)).real (halfSpaceLongPathEvent i b s x T) ≤ K / T

lemma centeredBox_subset_axisHalfSpace (N : ℕ) (f : Fin d × Bool) :
    (centeredBox d N : Set (Vertex d)) ⊆
      axisHalfSpace f.1 (if f.2 then (N : ℤ) else -(N : ℤ)) f.2 := by
  intro z hz
  have h := mem_centeredBox.mp (Finset.mem_coe.mp hz) f.1
  unfold axisHalfSpace
  cases hs : f.2
  · simp only [Set.mem_setOf_eq, Bool.false_eq_true, if_false]
    exact h.1
  · simp only [Set.mem_setOf_eq, if_true]
    exact h.2

theorem farFaceEvent_subset_halfSpacePath (N : ℕ) (x : Vertex d) (f : Fin d × Bool) (T : ℝ) :
    farFaceEvent N x f T ⊆
      halfSpaceLongPathEvent f.1 (if f.2 then (N : ℤ) else -(N : ℤ)) f.2 x T := by
  rintro ω ⟨u, huC, huF, hT⟩
  have hreach := ((mem_finiteBoxCluster ω _ x u).mp huC).2
  obtain ⟨p, hp, hlen⟩ := hreach.exists_path_of_dist
  have hle := restrictedGraph_mono ω (centeredBox_subset_axisHalfSpace (d := d) N f)
  have hface : u f.1 = if f.2 then (N : ℤ) else -(N : ℤ) := by
    unfold signedCubeFace at huF
    exact (Finset.mem_filter.mp huF).2
  refine ⟨u, hface, p.mapLe hle, (SimpleGraph.Walk.mapLe_isPath hle).mpr hp, ?_⟩
  rw [SimpleGraph.Walk.length_mapLe, hlen]
  exact hT

theorem faceReachTail_of_halfSpaceLongPath {K : ℝ} (h : HalfSpaceLongPathTail d K) :
    ∀ (N : ℕ) (x : Vertex d), x ∈ centeredBox d N →
      ∀ (f : Fin d × Bool) (T : ℝ), 0 < T →
        (percolation d (criticalPoint d)).real (farFaceEvent N x f T) ≤ K / T := by
  intro N x _ f T hT
  exact (measureReal_mono (farFaceEvent_subset_halfSpacePath N x f T) (measure_ne_top _ _)).trans
    (h f.1 _ f.2 x T hT)

end NearCritical.Section7
