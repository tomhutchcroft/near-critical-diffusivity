module

public import NearCritical.Section10SpanTwoSided

/-! The heart of the origin typical cube as a root region.

For the heart `typicalHeart t 0 cc` (`2|x_j| < cc t`), `N = (t-1)/2`:

* `heart_subset_rootRegion`: if `cc <= 1/16` the heart lies in
  `centeredBox d ((t-1)/32)`, the root region of the cited crossing inputs;
* `heart_card_upper`: `|heart| <= 2^d (N+1)^d`;
* `heart_card_lower`: if `0 < cc <= 1/16` and `t >= 64`,
  `(cc/4)^d (N+1)^d <= |heart|`.

These are the conditions on the root set `Z` of `hcand_of_raw`.
-/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open scoped Classical

theorem heart_subset_rootRegion {d : ℕ} (t : ℕ) (ht : 1 ≤ t) {cc : ℝ} (hcc : cc ≤ 1 / 16) :
    typicalHeart t (0 : Vertex d) cc ⊆ centeredBox d ((t - 1) / 32) := by
  intro x hx
  have htR : (0:ℝ) < (t : ℝ) := by exact_mod_cast (by omega : 0 < t)
  rw [mem_centeredBox]
  intro j
  have h := (Finset.mem_filter.mp hx).2 j
  rw [Pi.zero_apply, sub_zero] at h
  have h1 : 32 * |((x j : ℤ) : ℝ)| < (t : ℝ) := by nlinarith [abs_nonneg ((x j : ℤ) : ℝ)]
  have h2 : (32 * |x j| : ℤ) < (t : ℤ) := by
    have : ((32 * |x j| : ℤ) : ℝ) < ((t : ℤ) : ℝ) := by
      push_cast
      exact h1
    exact_mod_cast this
  have h3 := abs_le.mp (le_refl |x j|)
  constructor <;> omega

theorem heart_card_upper {d : ℕ} (t N : ℕ) (ht : 1 ≤ t) (hN : (t - 1) / 2 = N) (cc : ℝ) :
    ((typicalHeart t (0 : Vertex d) cc).card : ℝ) ≤ (2 : ℝ) ^ d * (N + 1 : ℝ) ^ d := by
  have hsub : typicalHeart t (0 : Vertex d) cc ⊆ typicalCube t (0 : Vertex d) :=
    Finset.filter_subset _ _
  have hcard : (typicalCube t (0 : Vertex d)).card = (2 * N + 1) ^ d := by
    rw [typicalCube_zero t ht, hN, card_centeredBox_exact]
  have h1 : ((typicalHeart t (0 : Vertex d) cc).card : ℝ) ≤ ((2 * N + 1 : ℕ) : ℝ) ^ d := by
    have := Finset.card_le_card hsub
    rw [hcard] at this
    exact_mod_cast this
  refine h1.trans ?_
  rw [← mul_pow]
  refine pow_le_pow_left₀ (by positivity) ?_ d
  push_cast
  linarith

theorem heart_card_lower {d : ℕ} (t N : ℕ) (ht : 64 ≤ t) (hN : (t - 1) / 2 = N) {cc : ℝ}
    (hcc0 : 0 < cc) (hcc : cc ≤ 1 / 16) :
    (cc / 4) ^ d * (N + 1 : ℝ) ^ d ≤ ((typicalHeart t (0 : Vertex d) cc).card : ℝ) := by
  have htR : (64:ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
  have ht0 : (0:ℝ) < (t : ℝ) := by linarith
  obtain ⟨m, hm⟩ : ∃ m : ℕ, m = ⌊cc * (t : ℝ) / 4⌋₊ := ⟨_, rfl⟩
  have hmle : (m : ℝ) ≤ cc * (t : ℝ) / 4 := by
    rw [hm]
    exact Nat.floor_le (by positivity)
  have hmlt : cc * (t : ℝ) / 4 < (m : ℝ) + 1 := by
    rw [hm]
    exact Nat.lt_floor_add_one _
  have hNR : (t : ℝ) ≤ 2 * (N : ℝ) + 2 := by
    have : t ≤ 2 * N + 2 := by omega
    exact_mod_cast this
  have hmN : m ≤ N := by
    have h1 : (m : ℝ) ≤ (t : ℝ) / 64 := by nlinarith
    have h2 : (m : ℝ) ≤ (N : ℝ) := by nlinarith
    exact_mod_cast h2
  have hsub : centeredBox d m ⊆ typicalHeart t (0 : Vertex d) cc := by
    intro x hx
    have hxm := mem_centeredBox.mp hx
    unfold typicalHeart
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · rw [mem_typicalCube_iff_int (by omega) 0 x]
      intro k
      obtain ⟨h1, h2⟩ := hxm k
      rw [Pi.zero_apply, sub_zero, hN]
      have : (m : ℤ) ≤ (N : ℤ) := by exact_mod_cast hmN
      constructor <;> omega
    · intro j
      obtain ⟨h1, h2⟩ := hxm j
      rw [Pi.zero_apply, sub_zero]
      have habs : |((x j : ℤ) : ℝ)| ≤ (m : ℝ) := by
        rw [abs_le]
        constructor
        · have : ((-(m : ℤ) : ℤ) : ℝ) ≤ ((x j : ℤ) : ℝ) := by exact_mod_cast h1
          push_cast at this
          exact this
        · exact_mod_cast h2
      nlinarith
  have hcard : ((centeredBox d m).card : ℝ) ≤ ((typicalHeart t (0 : Vertex d) cc).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  refine le_trans ?_ hcard
  rw [card_centeredBox_exact, ← mul_pow]
  push_cast
  refine pow_le_pow_left₀ (by positivity) ?_ d
  have hNt : (N : ℝ) + 1 ≤ (t : ℝ) := by
    have : N + 1 ≤ t := by omega
    exact_mod_cast this
  nlinarith

end NearCritical.Section10
