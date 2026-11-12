module

public import NearCritical.Section10TypicalClusters
public import NearCritical.Section9MiddleGeometry

/-! Coordinates of the Section 10 step regions.

For a cube centre `c`, a direction `i` and mesh parameter `t` (`l0 = 2t`), the
left and right half tubes are the Section 9 tubes translated to `c`:
`stepL t c i`, `stepR t c i`, with overlap `stepMid t c i`.

* `mem_stepTube`: membership in coordinates relative to `c`.
* `stepL_disjoint_far_cube`, `stepR_disjoint_near_cube`: each half tube avoids
  the cube at the other end.
* `splitFace_subset_stepL` (for `t >= 9`): the `+` half of the face of the cube
  in direction `i` lies in the left half tube.
-/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open scoped Classical

/-- Left half tube of the step from the cube at `c` in direction `i`. -/
def stepL {d : ℕ} (t : ℕ) (c : Vertex d) (i : Fin d) : Finset (Vertex d) :=
  translateSites c (section9FiniteTube i t (-(5:ℝ)/8) (3/8))

/-- Right half tube. -/
def stepR {d : ℕ} (t : ℕ) (c : Vertex d) (i : Fin d) : Finset (Vertex d) :=
  translateSites c (section9FiniteTube i t (-(3:ℝ)/8) (5/8))

/-- Middle region. -/
def stepMid {d : ℕ} (t : ℕ) (c : Vertex d) (i : Fin d) : Finset (Vertex d) :=
  translateSites c (section9FiniteMiddle i t)

theorem mem_stepTube {d : ℕ} (t : ℕ) (c x : Vertex d) (i : Fin d) (lo hi : ℝ)
    (hlo : -1 ≤ lo) (hhi : hi ≤ 1) :
    x ∈ translateSites c (section9FiniteTube i t lo hi) ↔
      ((t:ℝ) + lo * t < ((x i - c i : ℤ) : ℝ) ∧ ((x i - c i : ℤ) : ℝ) < (t:ℝ) + hi * t ∧
        ∀ j, j ≠ i → -3 * (t:ℝ) / 8 < ((x j - c j : ℤ) : ℝ) ∧
          ((x j - c j : ℤ) : ℝ) < 3 * (t:ℝ) / 8) := by
  have h := mem_translateSites c (section9FiniteTube i t lo hi) (x - c)
  rw [add_sub_cancel] at h
  rw [h, mem_section9FiniteTube i t lo hi hlo hhi]
  rfl

lemma typicalCube_coord {d : ℕ} {t : ℕ} {c x : Vertex d} (hx : x ∈ typicalCube t c)
    (j : Fin d) : 2 * |((x j - c j : ℤ) : ℝ)| < (t : ℝ) :=
  (Finset.mem_filter.mp hx).2 j

/-- The cube at the far end of the step. -/
def farCenter {d : ℕ} (t : ℕ) (c : Vertex d) (i : Fin d) : Vertex d :=
  c + Pi.single i (2 * (t : ℤ))

lemma farCenter_apply_self {d : ℕ} (t : ℕ) (c : Vertex d) (i : Fin d) :
    farCenter t c i i = c i + 2 * (t : ℤ) := by
  simp [farCenter]

lemma farCenter_apply_ne {d : ℕ} (t : ℕ) (c : Vertex d) (i : Fin d) {j : Fin d} (h : j ≠ i) :
    farCenter t c i j = c j := by
  simp [farCenter, h]

theorem stepL_disjoint_far_cube {d : ℕ} (t : ℕ) (c : Vertex d) (i : Fin d) :
    Disjoint (stepL t c i) (typicalCube t (farCenter t c i)) := by
  rw [Finset.disjoint_left]
  intro x hxL hxQ
  have h1 := ((mem_stepTube t c x i _ _ (by norm_num) (by norm_num)).mp hxL).2.1
  have h2 := typicalCube_coord hxQ i
  rw [farCenter_apply_self] at h2
  have h3 : ((x i - (c i + 2 * (t:ℤ)) : ℤ) : ℝ) = ((x i - c i : ℤ) : ℝ) - 2 * (t:ℝ) := by
    push_cast
    ring
  rw [h3] at h2
  have h4 := (abs_lt.mp (by linarith : |((x i - c i : ℤ) : ℝ) - 2 * (t:ℝ)| < (t:ℝ) / 2)).1
  have ht0 : (0:ℝ) ≤ (t:ℝ) := Nat.cast_nonneg t
  linarith

theorem stepR_disjoint_near_cube {d : ℕ} (t : ℕ) (c : Vertex d) (i : Fin d) :
    Disjoint (stepR t c i) (typicalCube t c) := by
  rw [Finset.disjoint_left]
  intro x hxR hxQ
  have h1 := ((mem_stepTube t c x i _ _ (by norm_num) (by norm_num)).mp hxR).1
  have h2 := typicalCube_coord hxQ i
  have h4 := (abs_lt.mp (by linarith : |((x i - c i : ℤ) : ℝ)| < (t:ℝ) / 2)).2
  have ht0 : (0:ℝ) ≤ (t:ℝ) := Nat.cast_nonneg t
  linarith

theorem splitFace_subset_stepL {d : ℕ} {t : ℕ} (ht : 9 ≤ t) (c : Vertex d) (i : Fin d)
    (pl : Bool) : typicalSplitFace t c (i, true) pl ⊆ stepL t c i := by
  intro x hx
  unfold typicalSplitFace at hx
  obtain ⟨hface, hsplit⟩ := Finset.mem_filter.mp hx
  unfold typicalFace at hface
  have hcoord := (Finset.mem_filter.mp hface).2
  simp only [if_true] at hcoord
  have htR : (9:ℝ) ≤ (t:ℝ) := by exact_mod_cast ht
  have hh1 : (t:ℝ) - 2 ≤ 2 * (((t - 1) / 2 : ℕ) : ℝ) := by
    have : t - 2 ≤ 2 * ((t - 1) / 2) := by omega
    have h' : ((t - 2 : ℕ) : ℝ) ≤ ((2 * ((t - 1) / 2) : ℕ) : ℝ) := Nat.cast_le.mpr this
    rw [Nat.cast_sub (by omega)] at h'
    push_cast at h'
    linarith
  have hh2 : 2 * (((t - 1) / 2 : ℕ) : ℝ) ≤ (t:ℝ) := by
    have : 2 * ((t - 1) / 2) ≤ t := by omega
    exact_mod_cast this
  have hxi : ((x i - c i : ℤ) : ℝ) = (((t - 1) / 2 : ℕ) : ℝ) := by
    rw [hcoord]
    push_cast
    rfl
  refine (mem_stepTube t c x i _ _ (by norm_num) (by norm_num)).mpr ⟨?_, ?_, ?_⟩
  · rw [hxi]
    linarith
  · rw [hxi]
    linarith
  · intro j hj
    have h := hsplit j hj
    cases pl
    · simp only [Bool.false_eq_true, if_false] at h
      constructor <;> linarith [h.1, h.2]
    · simp only [if_true] at h
      constructor <;> linarith [h.1, h.2]

end NearCritical.Section10
