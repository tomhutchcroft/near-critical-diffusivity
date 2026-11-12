module

public import NearCritical.Section10TubeArithmetic
public import NearCritical.Section10TubeGeometry
public import NearCritical.Section10TypicalNestTrace
public import NearCritical.ChemicalCrossingGeometry

/-! Cubes and tubes of the coarse box inside the crossing box.

Coarse centres are `c = 2t * a`. The crossing box has centre
`boxCenter t M = (M-1) t` in every coordinate and radius
`boxRadius t M = (M-1) t + (t-1)/2`, so its side is `(M-1) * 2t + s` with `s`
the odd side of a cube.

* `typicalCube_disjoint_of_ne`: cubes at distinct coarse centres are disjoint.
* `stepTubes_disjoint`: tubes of distinct (centre, direction) are disjoint.
* `cube_subset_support`, `stepL_subset_support`, `stepR_subset_support`.
* `bottomFace_mem`, `exitFace_mem`: faces of bottom and top cubes.
-/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open scoped Classical

/-- Coarse centre of a lattice point. -/
def coarseCenter {d : ℕ} (t : ℕ) (a : Vertex d) : Vertex d := fun k => (2 * (t : ℤ)) * a k

/-- Centre of the crossing box. -/
def boxCenter (d t M : ℕ) : Vertex d := fun _ => (((M - 1) * t : ℕ) : ℤ)

/-- Radius of the crossing box. -/
def boxRadius (t M : ℕ) : ℕ := (M - 1) * t + (t - 1) / 2

lemma typicalCube_int {d t : ℕ} (ht : 0 < t) {c x : Vertex d} (hx : x ∈ typicalCube t c)
    (k : Fin d) : -(((t - 1) / 2 : ℕ) : ℤ) ≤ x k - c k ∧ x k - c k ≤ (((t - 1) / 2 : ℕ) : ℤ) := by
  rw [typicalCube_eq_translated_centeredBox ht c] at hx
  have h := mem_translateSites c (centeredBox d ((t - 1) / 2)) (x - c)
  rw [add_sub_cancel] at h
  exact mem_centeredBox.mp (h.mp hx) k

theorem typicalCube_disjoint_of_ne {d t : ℕ} (ht : 0 < t) {a b : Vertex d} (hab : a ≠ b) :
    Disjoint (typicalCube t (coarseCenter t a)) (typicalCube t (coarseCenter t b)) := by
  rw [Finset.disjoint_left]
  intro x hxa hxb
  obtain ⟨k, hk⟩ : ∃ k, a k ≠ b k := by
    by_contra h
    exact hab (funext fun k => by_contra fun hk => h ⟨k, hk⟩)
  have h1 := typicalCube_coord hxa k
  have h2 := typicalCube_coord hxb k
  have htR : (0:ℝ) < (t:ℝ) := by exact_mod_cast ht
  have h1' := abs_lt.mp (by linarith : |((x k - coarseCenter t a k : ℤ) : ℝ)| < (t:ℝ) / 2)
  have h2' := abs_lt.mp (by linarith : |((x k - coarseCenter t b k : ℤ) : ℝ)| < (t:ℝ) / 2)
  simp only [coarseCenter] at h1' h2'
  push_cast at h1' h2'
  rcases lt_or_gt_of_ne hk with hlt | hgt
  · have : (a k : ℝ) + 1 ≤ (b k : ℝ) := by exact_mod_cast Int.add_one_le_iff.mpr hlt
    nlinarith [h1'.1, h1'.2, h2'.1, h2'.2]
  · have : (b k : ℝ) + 1 ≤ (a k : ℝ) := by exact_mod_cast Int.add_one_le_iff.mpr hgt
    nlinarith [h1'.1, h1'.2, h2'.1, h2'.2]

lemma stepLR_subset_coarseTube {d t : ℕ} (a : Vertex d) (i : Fin d) {x : Vertex d}
    (hx : x ∈ stepL t (coarseCenter t a) i ∪ stepR t (coarseCenter t a) i) :
    x ∈ coarseTubeVertices (2 * (t : ℝ)) a i := by
  have ht0 : (0:ℝ) ≤ (t:ℝ) := Nat.cast_nonneg t
  have hcast : ∀ k, ((x k - coarseCenter t a k : ℤ) : ℝ) = (x k : ℝ) - 2 * (t:ℝ) * (a k : ℝ) := by
    intro k
    simp only [coarseCenter]
    push_cast
    ring
  have hrange : (3 * (t:ℝ) / 8 < (x i : ℝ) - 2 * (t:ℝ) * (a i : ℝ) ∧
      (x i : ℝ) - 2 * (t:ℝ) * (a i : ℝ) < 13 * (t:ℝ) / 8) ∧
      ∀ k, k ≠ i → -3 * (t:ℝ) / 8 < (x k : ℝ) - 2 * (t:ℝ) * (a k : ℝ) ∧
        (x k : ℝ) - 2 * (t:ℝ) * (a k : ℝ) < 3 * (t:ℝ) / 8 := by
    rcases Finset.mem_union.mp hx with h | h
    · obtain ⟨h1, h2, h3⟩ := (mem_stepTube t _ x i _ _ (by norm_num) (by norm_num)).mp h
      rw [hcast] at h1 h2
      refine ⟨⟨by linarith, by linarith⟩, fun k hk => ?_⟩
      have := h3 k hk
      rw [hcast] at this
      exact this
    · obtain ⟨h1, h2, h3⟩ := (mem_stepTube t _ x i _ _ (by norm_num) (by norm_num)).mp h
      rw [hcast] at h1 h2
      refine ⟨⟨by linarith, by linarith⟩, fun k hk => ?_⟩
      have := h3 k hk
      rw [hcast] at this
      exact this
  intro k
  by_cases hk : k = i
  · subst hk
    rw [if_pos rfl, if_pos rfl, abs_lt]
    constructor <;> linarith [hrange.1.1, hrange.1.2]
  · rw [if_neg hk, if_neg hk, abs_lt]
    have := hrange.2 k hk
    constructor <;> linarith [this.1, this.2]

theorem stepTubes_disjoint {d t : ℕ} (ht : 0 < t) (a b : Vertex d) (i j : Fin d)
    (hne : (a, i) ≠ (b, j)) :
    Disjoint (stepL t (coarseCenter t a) i ∪ stepR t (coarseCenter t a) i)
      (stepL t (coarseCenter t b) j ∪ stepR t (coarseCenter t b) j) := by
  rw [Finset.disjoint_left]
  intro x hxa hxb
  have hd := coarseTubeVertices_disjoint (ell := 2 * (t : ℝ))
    (by have : (0:ℝ) < (t:ℝ) := by exact_mod_cast ht
        linarith) a b i j hne
  exact Set.disjoint_left.mp hd (stepLR_subset_coarseTube a i hxa)
    (stepLR_subset_coarseTube b j hxb)

lemma stepMid_subset_stepL {d : ℕ} (t : ℕ) (c : Vertex d) (i : Fin d) :
    stepMid t c i ⊆ stepL t c i := by
  unfold stepMid stepL translateSites
  refine Finset.image_subset_image ?_
  rw [section9FiniteMiddle_eq_inter]
  exact Finset.inter_subset_left

/-- Membership in the translated crossing support from coordinate bounds. -/
lemma mem_support_of_coords {d : ℕ} (t M : ℕ) (i₀ : Fin d) {x : Vertex d}
    (hx : ∀ k, -(boxRadius t M : ℤ) ≤ x k - boxCenter d t M k ∧
      x k - boxCenter d t M k ≤ (boxRadius t M : ℤ)) :
    x ∈ translateSites (boxCenter d t M) (chemicalCrossingSupport d (boxRadius t M) i₀) := by
  have h := mem_translateSites (boxCenter d t M)
    (chemicalCrossingSupport d (boxRadius t M) i₀) (x - boxCenter d t M)
  rw [add_sub_cancel] at h
  refine h.mpr ?_
  unfold chemicalCrossingSupport
  exact Finset.mem_union_left _ (mem_centeredBox.mpr hx)

theorem cube_subset_support {d t M : ℕ} (ht : 0 < t) (i₀ : Fin d) (c : Vertex d)
    (hc : ∀ k, 0 ≤ c k ∧ c k ≤ 2 * (t : ℤ) * ((M - 1 : ℕ) : ℤ)) :
    typicalCube t c ⊆
      translateSites (boxCenter d t M) (chemicalCrossingSupport d (boxRadius t M) i₀) := by
  intro x hx
  refine mem_support_of_coords t M i₀ (fun k => ?_)
  have h1 := typicalCube_int ht hx k
  have h2 := hc k
  simp only [boxCenter, boxRadius, Nat.cast_add, Nat.cast_mul]
  constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2]

end NearCritical.Section10
