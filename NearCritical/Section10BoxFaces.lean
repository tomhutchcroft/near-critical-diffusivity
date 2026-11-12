module

public import NearCritical.Section10BoxArithmetic

/-! Tubes and faces inside the crossing box.

* `stepLR_range`: coordinates of a point of the two half tubes.
* `stepLR_subset_support` (for `t >= 9`): tubes between two cubes of the coarse
  box lie in the crossing support.
* `bottomFace_mem`, `exitFace_mem`: the bottom face of a level-0 cube is in the
  bottom face of the box; exit bonds of a top cube end in the exit face.
* `exitBond_not_in_tube`: an exit bond of a top cube is not a bond of any tube
  (vertical tubes stop below the top level; transverse tubes are too thin).
-/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open scoped Classical

lemma stepLR_range {d t : ℕ} (c : Vertex d) (i : Fin d) {x : Vertex d}
    (hx : x ∈ stepL t c i ∪ stepR t c i) :
    (3 * (t:ℝ) / 8 < ((x i - c i : ℤ) : ℝ) ∧ ((x i - c i : ℤ) : ℝ) < 13 * (t:ℝ) / 8) ∧
      ∀ k, k ≠ i → -3 * (t:ℝ) / 8 < ((x k - c k : ℤ) : ℝ) ∧
        ((x k - c k : ℤ) : ℝ) < 3 * (t:ℝ) / 8 := by
  have ht0 : (0:ℝ) ≤ (t:ℝ) := Nat.cast_nonneg t
  rcases Finset.mem_union.mp hx with h | h
  · obtain ⟨h1, h2, h3⟩ := (mem_stepTube t c x i _ _ (by norm_num) (by norm_num)).mp h
    exact ⟨⟨by linarith, by linarith⟩, h3⟩
  · obtain ⟨h1, h2, h3⟩ := (mem_stepTube t c x i _ _ (by norm_num) (by norm_num)).mp h
    exact ⟨⟨by linarith, by linarith⟩, h3⟩

/-- Real bounds on the cube half side `h = (t-1)/2`. -/
lemma halfSide_bounds {t : ℕ} (ht : 2 ≤ t) :
    (t:ℝ) - 2 ≤ 2 * (((t - 1) / 2 : ℕ) : ℝ) ∧ 2 * (((t - 1) / 2 : ℕ) : ℝ) ≤ (t:ℝ) - 1 := by
  constructor
  · have : t - 2 ≤ 2 * ((t - 1) / 2) := by omega
    have h' : ((t - 2 : ℕ) : ℝ) ≤ ((2 * ((t - 1) / 2) : ℕ) : ℝ) := Nat.cast_le.mpr this
    rw [Nat.cast_sub ht] at h'
    push_cast at h'
    linarith
  · have : 2 * ((t - 1) / 2) ≤ t - 1 := by omega
    have h' : ((2 * ((t - 1) / 2) : ℕ) : ℝ) ≤ ((t - 1 : ℕ) : ℝ) := Nat.cast_le.mpr this
    rw [Nat.cast_sub (by omega)] at h'
    push_cast at h'
    linarith

theorem stepLR_subset_support {d t M : ℕ} (ht : 9 ≤ t) (i₀ i : Fin d) (c : Vertex d)
    (hc : ∀ k, 0 ≤ c k ∧ c k ≤ 2 * (t : ℤ) * ((M - 1 : ℕ) : ℤ))
    (hci : c i + 2 * (t : ℤ) ≤ 2 * (t : ℤ) * ((M - 1 : ℕ) : ℤ)) :
    stepL t c i ∪ stepR t c i ⊆
      translateSites (boxCenter d t M) (chemicalCrossingSupport d (boxRadius t M) i₀) := by
  intro x hx
  obtain ⟨hi, htr⟩ := stepLR_range c i hx
  obtain ⟨hh1, hh2⟩ := halfSide_bounds (by omega : 2 ≤ t)
  have htR : (9:ℝ) ≤ (t:ℝ) := by exact_mod_cast ht
  obtain ⟨h, hh⟩ : ∃ h : ℕ, h = (t - 1) / 2 := ⟨_, rfl⟩
  rw [← hh] at hh1 hh2
  refine mem_support_of_coords t M i₀ (fun k => ?_)
  have hck0 : (0:ℝ) ≤ (c k : ℝ) := by exact_mod_cast (hc k).1
  have hck1 : (c k : ℝ) ≤ 2 * (t:ℝ) * ((M - 1 : ℕ) : ℝ) := by exact_mod_cast (hc k).2
  have hcast : ((x k - c k : ℤ) : ℝ) = (x k : ℝ) - (c k : ℝ) := by push_cast; ring
  have key : (-(((M - 1 : ℕ) : ℝ) * (t:ℝ) + (h:ℝ)) ≤ (x k : ℝ) - ((M - 1 : ℕ) : ℝ) * (t:ℝ)) ∧
      ((x k : ℝ) - ((M - 1 : ℕ) : ℝ) * (t:ℝ) ≤ ((M - 1 : ℕ) : ℝ) * (t:ℝ) + (h:ℝ)) := by
    by_cases hk : k = i
    · subst hk
      rw [hcast] at hi
      have hci' : (c k : ℝ) + 2 * (t:ℝ) ≤ 2 * (t:ℝ) * ((M - 1 : ℕ) : ℝ) := by
        exact_mod_cast hci
      constructor <;> nlinarith [hi.1, hi.2]
    · have h3 := htr k hk
      rw [hcast] at h3
      constructor <;> nlinarith [h3.1, h3.2]
  simp only [boxCenter, boxRadius]
  rw [← hh]
  constructor
  · have h1 := key.1
    exact_mod_cast h1
  · have h2 := key.2
    exact_mod_cast h2

lemma cube_coords_in_box {d t M : ℕ} (ht : 0 < t) (c : Vertex d)
    (hc : ∀ k, 0 ≤ c k ∧ c k ≤ 2 * (t : ℤ) * ((M - 1 : ℕ) : ℤ)) {x : Vertex d}
    (hx : x ∈ typicalCube t c) (k : Fin d) :
    -(boxRadius t M : ℤ) ≤ x k - boxCenter d t M k ∧
      x k - boxCenter d t M k ≤ (boxRadius t M : ℤ) := by
  have h1 := typicalCube_int ht hx k
  have h2 := hc k
  simp only [boxCenter, boxRadius, Nat.cast_add, Nat.cast_mul]
  constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2]

theorem bottomFace_mem {d t M : ℕ} (ht : 0 < t) (i₀ : Fin d) (c : Vertex d)
    (hc : ∀ k, 0 ≤ c k ∧ c k ≤ 2 * (t : ℤ) * ((M - 1 : ℕ) : ℤ)) (hc0 : c i₀ = 0)
    {pt : Vertex d} (hpt : pt ∈ typicalFace t c (i₀, false)) :
    ∃ x ∈ chemicalBottomFace d (boxRadius t M) i₀, pt = boxCenter d t M + x := by
  unfold typicalFace at hpt
  obtain ⟨hcube, hface⟩ := Finset.mem_filter.mp hpt
  refine ⟨pt - boxCenter d t M, ?_, (add_sub_cancel _ _).symm⟩
  unfold chemicalBottomFace
  refine Finset.mem_filter.mpr ⟨mem_centeredBox.mpr (cube_coords_in_box ht c hc hcube), ?_⟩
  have hf : pt i₀ - c i₀ = -(((t - 1) / 2 : ℕ) : ℤ) := by simpa using hface
  rw [hc0, sub_zero] at hf
  simp only [Pi.sub_apply, boxCenter, boxRadius, Nat.cast_add, Nat.cast_mul]
  rw [hf]
  ring

theorem exitFace_mem {d t M : ℕ} (ht : 0 < t) (i₀ : Fin d) (c : Vertex d)
    (hc : ∀ k, 0 ≤ c k ∧ c k ≤ 2 * (t : ℤ) * ((M - 1 : ℕ) : ℤ))
    (hcM : c i₀ = 2 * (t : ℤ) * ((M - 1 : ℕ) : ℤ))
    {y : Vertex d} (hy : y ∈ typicalFace t c (i₀, true)) :
    ∃ z' ∈ chemicalExitFace d (boxRadius t M) i₀, bondTip (y, i₀) = boxCenter d t M + z' := by
  unfold typicalFace at hy
  obtain ⟨hcube, hface⟩ := Finset.mem_filter.mp hy
  refine ⟨bondTip (y - boxCenter d t M, i₀), ?_, ?_⟩
  · unfold chemicalExitFace
    refine Finset.mem_image.mpr ⟨y - boxCenter d t M, Finset.mem_filter.mpr
      ⟨mem_centeredBox.mpr (cube_coords_in_box ht c hc hcube), ?_⟩, rfl⟩
    have hf : y i₀ - c i₀ = (((t - 1) / 2 : ℕ) : ℤ) := by simpa using hface
    rw [hcM] at hf
    simp only [Pi.sub_apply, boxCenter, boxRadius, Nat.cast_add, Nat.cast_mul]
    linarith
  · funext k
    unfold bondTip
    by_cases hk : k = i₀
    · subst hk
      simp only [Function.update_self, Pi.add_apply, Pi.sub_apply]
      ring
    · simp only [Function.update_of_ne hk, Pi.add_apply, Pi.sub_apply]
      ring

theorem exitBond_not_in_tube {d t M : ℕ} (ht : 9 ≤ t) (i₀ i : Fin d) (c cz : Vertex d)
    (lev : ℤ) (hc : c i₀ = 2 * (t : ℤ) * lev)
    (hcz : cz i₀ = 2 * (t : ℤ) * ((M - 1 : ℕ) : ℤ))
    (hi : i = i₀ → lev + 1 ≤ ((M - 1 : ℕ) : ℤ))
    {y : Vertex d} (hy : y ∈ typicalFace t cz (i₀, true))
    (hy1 : y ∈ stepL t c i ∪ stepR t c i)
    (hy2 : bondTip (y, i₀) ∈ stepL t c i ∪ stepR t c i) : False := by
  unfold typicalFace at hy
  have hface := (Finset.mem_filter.mp hy).2
  have hf : y i₀ - cz i₀ = (((t - 1) / 2 : ℕ) : ℤ) := by simpa using hface
  obtain ⟨hh1, hh2⟩ := halfSide_bounds (by omega : 2 ≤ t)
  have htR : (9:ℝ) ≤ (t:ℝ) := by exact_mod_cast ht
  obtain ⟨h, hh⟩ : ∃ h : ℕ, h = (t - 1) / 2 := ⟨_, rfl⟩
  rw [← hh] at hh1 hh2 hf
  have hyR : (y i₀ : ℝ) = 2 * (t:ℝ) * ((M - 1 : ℕ) : ℝ) + (h : ℝ) := by
    have : y i₀ = 2 * (t : ℤ) * ((M - 1 : ℕ) : ℤ) + (h : ℤ) := by
      rw [← hcz]
      linarith
    exact_mod_cast this
  have hcR : (c i₀ : ℝ) = 2 * (t:ℝ) * (lev : ℝ) := by exact_mod_cast hc
  by_cases hii : i = i₀
  · subst hii
    obtain ⟨h1, _⟩ := stepLR_range c i hy1
    have hcast : ((y i - c i : ℤ) : ℝ) = (y i : ℝ) - (c i : ℝ) := by push_cast; ring
    rw [hcast, hyR, hcR] at h1
    have hlev : (lev : ℝ) + 1 ≤ ((M - 1 : ℕ) : ℝ) := by exact_mod_cast hi rfl
    nlinarith [h1.1, h1.2]
  · obtain ⟨_, h2⟩ := stepLR_range c i hy2
    have h3 := h2 i₀ (fun h => hii h.symm)
    have htip : bondTip (y, i₀) i₀ = y i₀ + 1 := by
      unfold bondTip
      simp
    have hcast : ((bondTip (y, i₀) i₀ - c i₀ : ℤ) : ℝ) = (y i₀ : ℝ) + 1 - (c i₀ : ℝ) := by
      rw [htip]
      push_cast
      ring
    rw [hcast, hyR, hcR] at h3
    rcases le_or_gt lev ((M - 1 : ℕ) : ℤ) with hle | hgt
    · have hleR : (lev : ℝ) ≤ ((M - 1 : ℕ) : ℝ) := by exact_mod_cast hle
      nlinarith [h3.1, h3.2]
    · have hgtR : ((M - 1 : ℕ) : ℝ) + 1 ≤ (lev : ℝ) := by
        exact_mod_cast Int.add_one_le_iff.mpr hgt
      nlinarith [h3.1, h3.2]

end NearCritical.Section10
