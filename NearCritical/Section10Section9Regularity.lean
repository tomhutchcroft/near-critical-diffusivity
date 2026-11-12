module

public import NearCritical.Section10Section9Geometry
public import NearCritical.Section8ExtensionErrorGeometry

/-! Regularity base sets of the Section 10 step versus Section 8/9.

* `typicalInnerCube_zero_eq_smallCube`: the inner cube `Lambda_{3t/4}` of the
  site cube is `section8ExtensionSmallCube i t`.
* `typicalInnerCube_far_eq_reflected`: the inner cube of the target cube is the
  reflection of the small cube in the midpoint `t e_i`.
* `sourceRegularPoint_mono`: regularity with a smaller tolerance implies
  regularity with a larger one.

So the regular points of def.spanning.z are regular points in the sense of the
hypotheses of `section9_source_many_opened_pivotal_targets`, once the
tolerance is at most the `delta` of that theorem.
-/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open scoped Classical

lemma mem_smallCube_iff {d t : ℕ} (i : Fin d) (x : Vertex d) :
    x ∈ section8ExtensionSmallCube i t ↔
      x ∈ centeredBox d (3 * t) ∧
        ∀ j, -(3 * (t : ℝ) / 8) < (x j : ℝ) ∧ (x j : ℝ) < 3 * (t : ℝ) / 8 := by
  simp only [section8ExtensionSmallCube, Finset.mem_filter, sprinklingEndCube,
    Set.mem_setOf_eq, ite_self, sub_zero]
  refine and_congr Iff.rfl (forall_congr' (fun j => ?_))
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

lemma mem_typicalInnerCube_iff {d t : ℕ} (c x : Vertex d) :
    x ∈ typicalInnerCube t c ↔
      x ∈ typicalCube t c ∧ ∀ j, 8 * |((x j - c j : ℤ) : ℝ)| < 3 * (t : ℝ) := by
  unfold typicalInnerCube
  rw [Finset.mem_filter]

theorem typicalInnerCube_zero_eq_smallCube {d t : ℕ} (ht : 0 < t) (i : Fin d) :
    typicalInnerCube t (0 : Vertex d) = section8ExtensionSmallCube i t := by
  have htR : (0:ℝ) < (t : ℝ) := by exact_mod_cast ht
  ext x
  rw [mem_typicalInnerCube_iff, mem_smallCube_iff]
  constructor
  · rintro ⟨hcube, hin⟩
    refine ⟨mem_centeredBox.mpr (fun j => ?_), fun j => ?_⟩
    · have h := (mem_typicalCube_iff_int ht 0 x).mp hcube j
      rw [Pi.zero_apply, sub_zero] at h
      constructor <;> omega
    · have h := hin j
      rw [Pi.zero_apply, sub_zero] at h
      have h' := abs_lt.mp (by linarith : |((x j : ℤ) : ℝ)| < 3 * (t : ℝ) / 8)
      constructor <;> linarith [h'.1, h'.2]
  · rintro ⟨_, hin⟩
    refine ⟨(mem_typicalCube_iff_int ht 0 x).mpr (fun j => ?_), fun j => ?_⟩
    · rw [Pi.zero_apply, sub_zero]
      refine (halfSide_iff ht (x j)).mpr ?_
      constructor <;> linarith [(hin j).1, (hin j).2]
    · rw [Pi.zero_apply, sub_zero]
      have : |((x j : ℤ) : ℝ)| < 3 * (t : ℝ) / 8 := abs_lt.mpr ⟨by linarith [(hin j).1], (hin j).2⟩
      linarith

theorem typicalInnerCube_far_eq_reflected {d t : ℕ} (ht : 0 < t) (i : Fin d) :
    typicalInnerCube t (farCenter t (0 : Vertex d) i) =
      (section8ExtensionSmallCube i t).image (affineReflection (Pi.single i (2 * (t : ℤ)))) := by
  have hfar : farCenter t (0 : Vertex d) i = Pi.single i (2 * (t : ℤ)) := by
    unfold farCenter
    rw [zero_add]
  rw [hfar]
  ext x
  have himg : x ∈ (typicalInnerCube t (0 : Vertex d)).image
      (affineReflection (Pi.single i (2 * (t : ℤ)))) ↔
      (Pi.single i (2 * (t : ℤ)) - x) ∈ typicalInnerCube t (0 : Vertex d) := by
    constructor
    · intro h
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp h
      show Pi.single i (2 * (t : ℤ)) - (Pi.single i (2 * (t : ℤ)) - y) ∈ _
      rw [sub_sub_cancel]
      exact hy
    · intro h
      refine Finset.mem_image.mpr ⟨_, h, ?_⟩
      show Pi.single i (2 * (t : ℤ)) - (Pi.single i (2 * (t : ℤ)) - x) = x
      rw [sub_sub_cancel]
  rw [← typicalInnerCube_zero_eq_smallCube ht i, himg, mem_typicalInnerCube_iff,
    mem_typicalInnerCube_iff, mem_typicalCube_iff_int ht, mem_typicalCube_iff_int ht]
  have hneg : ∀ j, ((Pi.single i (2 * (t : ℤ)) : Vertex d) - x) j - (0 : Vertex d) j =
      -(x j - (Pi.single i (2 * (t : ℤ)) : Vertex d) j) := by
    intro j
    simp only [Pi.sub_apply, Pi.zero_apply, sub_zero, neg_sub]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun j => ?_, fun j => ?_⟩
    · rw [hneg j]
      have := h1 j
      constructor <;> omega
    · rw [hneg j, Int.cast_neg, abs_neg]
      exact h2 j
  · rintro ⟨h1, h2⟩
    refine ⟨fun j => ?_, fun j => ?_⟩
    · have := h1 j
      rw [hneg j] at this
      constructor <;> omega
    · have := h2 j
      rw [hneg j, Int.cast_neg, abs_neg] at this
      exact this

theorem sourceRegularPoint_mono {d : ℕ} {F S B : Finset (Vertex d)} {r : ℕ} {δ δ' : ℝ}
    (hδ : δ ≤ δ') {x : Vertex d} (h : sourceRegularPoint F S B r δ x) :
    sourceRegularPoint F S B r δ' x :=
  ⟨h.1, h.2.1.trans hδ, h.2.2.trans hδ⟩

end NearCritical.Section10
