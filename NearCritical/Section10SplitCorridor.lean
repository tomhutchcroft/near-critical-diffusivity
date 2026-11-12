module

public import NearCritical.Section10CrossingCount
public import NearCritical.Section10Section9Geometry

/-! The split-face corridor of the origin typical cube.

For a face `f = (i, s)` and a half `pl`, `splitBeyond t f pl R` is the region
outside the cube beyond that face (signed height in `(N, N + R]`,
`N = (t-1)/2`) whose transverse coordinates lie in the split range, and
`splitCorridor = cube ∪ splitBeyond`.

`splitCorridor_exit`: a point of the cube with a lattice neighbour in the
corridor outside the cube lies on `typicalSplitFace t 0 f pl`. This is the
geometric hypothesis `hWF` of `crossing_small_count_le` for the 4d split
faces.
-/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open scoped Classical

/-- Signed height of a vertex relative to a face. -/
def faceHeight {d : ℕ} (f : Fin d × Bool) (u : Vertex d) : ℤ := if f.2 then u f.1 else -u f.1

/-- Transverse split condition (as in `typicalSplitFace`, centre `0`). -/
def splitRange (t : ℕ) (pl : Bool) (v : ℤ) : Prop :=
  if pl then (t : ℝ) < 8 * (v : ℝ) ∧ 4 * (v : ℝ) < (t : ℝ)
  else -(t : ℝ) < 4 * (v : ℝ) ∧ 8 * (v : ℝ) < -(t : ℝ)

/-- Region beyond the split face. -/
def splitBeyond {d : ℕ} (t : ℕ) (f : Fin d × Bool) (pl : Bool) (R : ℕ) : Finset (Vertex d) :=
  (centeredBox d ((t - 1) / 2 + R)).filter fun u =>
    (((t - 1) / 2 : ℕ) : ℤ) < faceHeight f u ∧ ∀ j, j ≠ f.1 → splitRange t pl (u j)

/-- Cube plus the region beyond the split face. -/
def splitCorridor {d : ℕ} (t : ℕ) (f : Fin d × Bool) (pl : Bool) (R : ℕ) : Finset (Vertex d) :=
  typicalCube t (0 : Vertex d) ∪ splitBeyond t f pl R

lemma latticeAdj_coords {d : ℕ} {y u : Vertex d}
    (h : (openGraph (fun _ : Bond d => true)).Adj y u) :
    ∃ j : Fin d, (u j = y j + 1 ∨ y j = u j + 1) ∧ ∀ k, k ≠ j → u k = y k := by
  obtain ⟨e, _, hends | hends⟩ := h
  · obtain ⟨h1, h2⟩ := hends
    refine ⟨e.2, Or.inl ?_, fun k hk => ?_⟩
    · rw [h2, h1]
      simp [bondTip]
    · rw [h2, h1]
      simp [bondTip, Function.update_of_ne hk]
  · obtain ⟨h1, h2⟩ := hends
    refine ⟨e.2, Or.inr ?_, fun k hk => ?_⟩
    · rw [h2, h1]
      simp [bondTip]
    · rw [h2, h1]
      simp [bondTip, Function.update_of_ne hk]

theorem splitCorridor_exit {d : ℕ} (t : ℕ) (ht : 1 ≤ t) (f : Fin d × Bool) (pl : Bool) (R : ℕ) :
    ∀ y ∈ typicalCube t (0 : Vertex d), ∀ u ∈ splitCorridor t f pl R,
      u ∉ typicalCube t (0 : Vertex d) →
      (openGraph (fun _ : Bond d => true)).Adj y u → y ∈ typicalSplitFace t (0 : Vertex d) f pl := by
  intro y hy u hu huQ hadj
  obtain ⟨i, s⟩ := f
  have huB : u ∈ splitBeyond t (i, s) pl R := by
    rcases Finset.mem_union.mp hu with h | h
    · exact absurd h huQ
    · exact h
  obtain ⟨_, hheight, htrans⟩ := Finset.mem_filter.mp huB
  have hyc := (mem_typicalCube_iff_int (by omega) 0 y).mp hy
  obtain ⟨j, hj, hrest⟩ := latticeAdj_coords hadj
  have hyi := hyc i
  simp only [Pi.zero_apply, sub_zero] at hyi
  -- the differing coordinate is `i`
  have hji : j = i := by
    by_contra hne
    have hui : u i = y i := hrest i (fun h => hne h.symm)
    cases s <;> simp only [faceHeight] at hheight <;> simp at hheight <;> omega
  subst hji
  have htr : ∀ k, k ≠ j → u k = y k := hrest
  have hface : y j - (0 : Vertex d) j =
      if s then (((t - 1) / 2 : ℕ) : ℤ) else -(((t - 1) / 2 : ℕ) : ℤ) := by
    rw [Pi.zero_apply, sub_zero]
    cases s <;> simp only [faceHeight] at hheight <;> simp at hheight ⊢ <;>
      rcases hj with h | h <;> omega
  unfold typicalSplitFace typicalFace
  refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hy, hface⟩, ?_⟩
  intro k hk
  have hsr := htrans k hk
  rw [htr k hk] at hsr
  simp only [Pi.zero_apply, sub_zero]
  exact hsr

end NearCritical.Section10
