module

public import NearCritical.Section10StepDiameter
public import NearCritical.Section8ExtensionSourceGeometry
public import NearCritical.Section8ReflectionGeometry

/-! Identification of the Section 10 step geometry (at the origin, direction
`i`, scale `n = t`) with the sets in which the Section 9 opened-target theorem
is stated.

* `typicalCube_zero_eq_endCube`: the site cube is `section9FiniteEndCube i t 0`.
* `typicalCube_far_eq_endCube`: the target cube is `section9FiniteEndCube i t (2t)`.
* `splitFace_subset_positiveFaceCore`: source split faces lie in the Section 8
  positive face core.
* `splitFace_subset_negativeFaceCore`: target split faces lie in the negative
  face core of the far cube.
-/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open scoped Classical

lemma mem_typicalCube_iff_int {d t : ℕ} (ht : 0 < t) (c x : Vertex d) :
    x ∈ typicalCube t c ↔
      ∀ k, -(((t - 1) / 2 : ℕ) : ℤ) ≤ x k - c k ∧ x k - c k ≤ (((t - 1) / 2 : ℕ) : ℤ) := by
  rw [typicalCube_eq_translated_centeredBox ht c]
  have h := mem_translateSites c (centeredBox d ((t - 1) / 2)) (x - c)
  rw [add_sub_cancel] at h
  rw [h, mem_centeredBox]
  rfl

/-- Integer half-side versus open real interval. -/
lemma halfSide_iff {t : ℕ} (ht : 0 < t) (u : ℤ) :
    (-(((t - 1) / 2 : ℕ) : ℤ) ≤ u ∧ u ≤ (((t - 1) / 2 : ℕ) : ℤ)) ↔
      (-(t : ℝ) / 2 < (u : ℝ) ∧ (u : ℝ) < (t : ℝ) / 2) := by
  obtain ⟨r, hr⟩ : ∃ r, (t - 1) / 2 = r := ⟨_, rfl⟩
  rw [hr]
  have hr1 : 2 * r + 1 ≤ t := by omega
  have hr2 : t ≤ 2 * r + 2 := by omega
  have hr1' : (2:ℝ) * (r : ℝ) + 1 ≤ (t : ℝ) := by exact_mod_cast hr1
  constructor
  · rintro ⟨h1, h2⟩
    have h1' : -(r : ℝ) ≤ (u : ℝ) := by exact_mod_cast h1
    have h2' : (u : ℝ) ≤ (r : ℝ) := by exact_mod_cast h2
    constructor <;> linarith
  · rintro ⟨h1, h2⟩
    have h3 : (2 * u : ℤ) < (t : ℤ) := by
      have : ((2 * u : ℤ) : ℝ) < ((t : ℤ) : ℝ) := by push_cast; linarith
      exact_mod_cast this
    have h4 : -(t : ℤ) < (2 * u : ℤ) := by
      have : ((-(t : ℤ) : ℤ) : ℝ) < ((2 * u : ℤ) : ℝ) := by push_cast; linarith
      exact_mod_cast this
    constructor <;> omega

theorem typicalCube_zero_eq_endCube {d t : ℕ} (ht : 0 < t) (i : Fin d) :
    typicalCube t (0 : Vertex d) = section9FiniteEndCube i t 0 := by
  have hn : (0:ℝ) ≤ (t : ℝ) := Nat.cast_nonneg t
  ext x
  rw [mem_typicalCube_iff_int ht, mem_section9FiniteEndCube i t 0 ⟨by linarith, by linarith⟩]
  refine forall_congr' (fun j => ?_)
  rw [Pi.zero_apply, sub_zero, halfSide_iff ht]
  simp only [ite_self, sub_zero]

theorem typicalCube_far_eq_endCube {d t : ℕ} (ht : 0 < t) (i : Fin d) :
    typicalCube t (farCenter t (0 : Vertex d) i) = section9FiniteEndCube i t (2 * (t : ℝ)) := by
  have hn : (0:ℝ) ≤ (t : ℝ) := Nat.cast_nonneg t
  ext x
  rw [mem_typicalCube_iff_int ht,
    mem_section9FiniteEndCube i t (2 * (t : ℝ)) ⟨by linarith, by linarith⟩]
  refine forall_congr' (fun j => ?_)
  rw [halfSide_iff ht]
  by_cases hj : j = i
  · subst hj
    rw [farCenter_apply_self, if_pos rfl]
    push_cast
    simp only [Pi.zero_apply, Int.cast_zero, zero_add]
  · rw [farCenter_apply_ne t 0 i hj, if_neg hj]
    simp only [Pi.zero_apply, sub_zero]

theorem splitFace_subset_positiveFaceCore {d t : ℕ} (ht : 0 < t) (i : Fin d) (pl : Bool) :
    typicalSplitFace t (0 : Vertex d) (i, true) pl ⊆ section8ExtensionPositiveFaceCore i t := by
  intro x hx
  have htR : (0:ℝ) < (t : ℝ) := by exact_mod_cast ht
  obtain ⟨hface, htrans⟩ := Finset.mem_filter.mp hx
  obtain ⟨hcube, hxi⟩ := Finset.mem_filter.mp hface
  have hxi' : x i = (((t - 1) / 2 : ℕ) : ℤ) := by simpa using hxi
  unfold section8ExtensionPositiveFaceCore
  refine Finset.mem_filter.mpr ⟨?_, ?_, ?_⟩
  · rw [← typicalCube_zero_eq_endCube ht i]
    exact hcube
  · intro htip
    rw [← typicalCube_zero_eq_endCube ht i, mem_typicalCube_iff_int ht] at htip
    have h := (htip i).2
    have hval : bondTip (x, i) i = x i + 1 := by simp [bondTip]
    rw [hval, Pi.zero_apply, sub_zero, hxi'] at h
    omega
  · intro j hj
    have h := htrans j hj
    simp only [Pi.zero_apply, sub_zero] at h
    cases pl with
    | true =>
      simp only [if_true] at h
      constructor <;> linarith [h.1, h.2]
    | false =>
      simp only [Bool.false_eq_true, if_false] at h
      constructor <;> linarith [h.1, h.2]

theorem splitFace_subset_negativeFaceCore {d t : ℕ} (ht : 0 < t) (i : Fin d) (pl : Bool) :
    typicalSplitFace t (farCenter t (0 : Vertex d) i) (i, false) pl ⊆
      section8ExtensionNegativeFaceCore i t := by
  intro x hx
  have htR : (0:ℝ) < (t : ℝ) := by exact_mod_cast ht
  obtain ⟨hface, htrans⟩ := Finset.mem_filter.mp hx
  obtain ⟨hcube, hxi⟩ := Finset.mem_filter.mp hface
  have hxi' : x i - farCenter t (0 : Vertex d) i i = -(((t - 1) / 2 : ℕ) : ℤ) := by
    simpa using hxi
  unfold section8ExtensionNegativeFaceCore
  refine Finset.mem_filter.mpr ⟨?_, ?_, ?_⟩
  · rw [← typicalCube_far_eq_endCube ht i]
    exact hcube
  · intro hpred
    rw [← typicalCube_far_eq_endCube ht i, mem_typicalCube_iff_int ht] at hpred
    have h := (hpred i).1
    have hval : bondPredecessor x i i = x i - 1 := by simp [bondPredecessor]
    rw [hval] at h
    omega
  · intro j hj
    have h := htrans j hj
    rw [farCenter_apply_ne t 0 i hj] at h
    simp only [Pi.zero_apply, sub_zero] at h
    cases pl with
    | true =>
      simp only [if_true] at h
      constructor <;> linarith [h.1, h.2]
    | false =>
      simp only [Bool.false_eq_true, if_false] at h
      constructor <;> linarith [h.1, h.2]

end NearCritical.Section10
