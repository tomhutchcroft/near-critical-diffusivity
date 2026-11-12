module

public import NearCritical.AppendixFRDSums
public import NearCritical.Section8SourceAnnulusBridge
public import NearCritical.Section10RegularityLoss
public import NearCritical.Section10SpanningCited

/-! Exact rounded cube geometry for the conditional moments at the marked faces. -/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open AppendixVariance NearCritical.Section8
open scoped Classical

/-- The inclusive lattice radius of the heart with its strict real cutoff. -/
def typicalHeartRadius (t : ℕ) (cc : ℝ) : ℕ := ⌈cc * (t : ℝ) / 2⌉₊ - 1

private lemma typicalHeartRadius_lt (t : ℕ) (ht : 1 ≤ t) (cc : ℝ) (hc : 0 < cc) :
    (typicalHeartRadius t cc : ℝ) < cc * (t : ℝ) / 2 := by
  have ht' : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  have hpos : 0 < ⌈cc * (t : ℝ) / 2⌉₊ := Nat.ceil_pos.mpr (by positivity)
  apply Nat.lt_ceil.mp
  unfold typicalHeartRadius
  omega

private lemma typicalHeartRadius_le (t : ℕ) (ht : 1 ≤ t) (cc : ℝ) (hc : 0 < cc) (hc1 : cc ≤ 1) :
    typicalHeartRadius t cc ≤ (t - 1) / 2 := by
  have hlt := typicalHeartRadius_lt t ht cc hc
  have ht0 : (0 : ℝ) ≤ t := Nat.cast_nonneg _
  have hmul : cc * (t : ℝ) ≤ t := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hc1 ht0
  have h : 2 * typicalHeartRadius t cc < t := by
    exact_mod_cast (show 2 * (typicalHeartRadius t cc : ℝ) < t by linarith)
  omega

/-- The strict real heart is exactly the inclusive integer cube at its
rounded radius, also when the real cutoff is itself an integer. -/
theorem typicalHeart_zero_eq_centeredBox {d : ℕ} (t : ℕ) (ht : 1 ≤ t) (cc : ℝ)
    (hc : 0 < cc) (hc1 : cc ≤ 1) :
    typicalHeart t (0 : Vertex d) cc = centeredBox d (typicalHeartRadius t cc) := by
  have hr := typicalHeartRadius_le t ht cc hc hc1
  have hrlt := typicalHeartRadius_lt t ht cc hc
  ext x
  rw [typicalHeart, Finset.mem_filter, typicalCube_zero t ht]
  constructor
  · rintro ⟨_, hx⟩
    apply mem_centeredBox.mpr
    intro i
    have hi := hx i
    simp only [Pi.zero_apply, sub_zero] at hi
    have habs : ((x i).natAbs : ℝ) < cc * (t : ℝ) / 2 := by
      rw [Nat.cast_natAbs, Int.cast_abs]
      linarith
    have hh : (x i).natAbs ≤ typicalHeartRadius t cc := by
      have := Nat.lt_ceil.mpr habs
      unfold typicalHeartRadius
      omega
    have hh' : |x i| ≤ (typicalHeartRadius t cc : ℤ) := by
      rw [← Int.natCast_natAbs]
      exact_mod_cast hh
    exact abs_le.mp hh'
  · intro hx
    refine ⟨centeredBox_mono hr hx, fun i => ?_⟩
    have hi := mem_centeredBox.mp hx i
    have habs : |(x i : ℝ)| ≤ (typicalHeartRadius t cc : ℝ) :=
      abs_le.mpr ⟨by exact_mod_cast hi.1, by exact_mod_cast hi.2⟩
    simp only [Pi.zero_apply, sub_zero]
    linarith

/-- Radius comparison for substituting the heart scale in the numerical
moment bounds. The rounding loss is at most one lattice spacing. -/
theorem typicalHeartRadius_scale (t : ℕ) (ht : 3 ≤ t) (cc : ℝ) (hc : 0 < cc) :
    let N := (t - 1) / 2
    cc * (N : ℝ) - 1 ≤ (typicalHeartRadius t cc : ℝ) ∧
      (typicalHeartRadius t cc : ℝ) ≤ (2 * cc) * (N : ℝ) := by
  intro N
  have ht' : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  have hpos : 0 < ⌈cc * (t : ℝ) / 2⌉₊ := Nat.ceil_pos.mpr (by positivity)
  have hceil := Nat.le_ceil (cc * (t : ℝ) / 2)
  have heq : (typicalHeartRadius t cc : ℝ) + 1 = (⌈cc * (t : ℝ) / 2⌉₊ : ℝ) := by
    exact_mod_cast (show typicalHeartRadius t cc + 1 = ⌈cc * (t : ℝ) / 2⌉₊ by
      unfold typicalHeartRadius
      omega)
  have hlo : 2 * (N : ℝ) ≤ t := by exact_mod_cast (show 2 * N ≤ t by dsimp [N]; omega)
  have hhi : (t : ℝ) ≤ 4 * (N : ℝ) := by exact_mod_cast (show t ≤ 4 * N by dsimp [N]; omega)
  have hlt := typicalHeartRadius_lt t (by omega) cc hc
  constructor
  · nlinarith only [heq, hceil, mul_le_mul_of_nonneg_left hlo hc.le]
  · nlinarith only [hlt, mul_le_mul_of_nonneg_left hhi hc.le]

/-- The branch-point cutoff at half the outer radius lies in the excluded
cube of the first energy. -/
theorem halfBox_subset_typicalInnerCube {d : ℕ} (t : ℕ) (ht : 1 ≤ t) :
    centeredBox d (((t - 1) / 2) / 2) ⊆ typicalInnerCube t (0 : Vertex d) := by
  let N := (t - 1) / 2
  let L := N / 2
  intro x hx
  apply Finset.mem_filter.mpr
  refine ⟨?_, fun i => ?_⟩
  · rw [typicalCube_zero t ht]
    exact centeredBox_mono (show L ≤ N by dsimp [L]; omega) hx
  · have h := mem_centeredBox.mp hx i
    have habs : |(x i : ℝ)| ≤ (L : ℝ) :=
      abs_le.mpr ⟨by exact_mod_cast h.1, by exact_mod_cast h.2⟩
    have hlt : (4 : ℝ) * L < t := by exact_mod_cast (show 4 * L < t by dsimp [L, N]; omega)
    have ht0 : (0 : ℝ) ≤ t := Nat.cast_nonneg _
    simp only [Pi.zero_apply, sub_zero]
    linarith

/-- The marked roots lie on a signed face and satisfy the transverse margin
required by the lower heart-hitting estimate. -/
theorem typMark_face_margin {d : ℕ} (t : ℕ) (ht : 1 ≤ t) {x : Vertex d}
    (hx : x ∈ typMark t (0 : Vertex d)) :
    let N := (t - 1) / 2
    ∃ i : Fin d, (x i = (N : ℤ) ∨ x i = -(N : ℤ)) ∧
      ∀ j, j ≠ i → 2 * |(x j : ℝ)| ≤ (N : ℝ) := by
  intro N
  obtain ⟨⟨⟨i, sign⟩, side⟩, _, hi⟩ := Finset.mem_biUnion.mp hx
  have hi' : x ∈ typicalSplitFace t (0 : Vertex d) (i, sign) side := hi
  obtain ⟨hface, htrans⟩ := Finset.mem_filter.mp hi'
  rw [typicalFace_zero t ht] at hface
  unfold signedCubeFace at hface
  have hsigned := (Finset.mem_filter.mp hface).2
  refine ⟨i, ?_, fun j hj => ?_⟩
  · cases sign
    · exact Or.inr (by simpa [N] using hsigned)
    · exact Or.inl (by simpa [N] using hsigned)
  · have hj' := htrans j hj
    have hlt : 4 * |(x j : ℝ)| < t := by
      cases side
      · simp only [Pi.zero_apply, sub_zero, Bool.false_eq_true, ↓reduceIte] at hj'
        rw [abs_of_neg (by linarith : (x j : ℝ) < 0)]
        linarith
      · simp only [Pi.zero_apply, sub_zero, ↓reduceIte] at hj'
        rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ (x j : ℝ))]
        linarith
    have hlt' : 4 * |x j| < (t : ℤ) := by
      exact_mod_cast (show 4 * ((|x j| : ℤ) : ℝ) < t by simpa only [Int.cast_abs] using hlt)
    rw [← Int.cast_abs]
    exact_mod_cast (show 2 * |x j| ≤ (N : ℤ) by dsimp [N]; omega)

/-- The weight of the second energy uses exactly the integer cube boundary. -/
theorem typicalBoundary_zero_eq_cubeBoundary {k : ℕ} (t : ℕ) (ht : 1 ≤ t) :
    typicalBoundary t (0 : Vertex (k + 1)) = cubeBoundary ((t - 1) / 2) := by
  let N := (t - 1) / 2
  ext x
  constructor
  · intro hx
    obtain ⟨⟨i, sign⟩, _, hface⟩ := Finset.mem_biUnion.mp hx
    rw [typicalFace_zero t ht] at hface
    unfold signedCubeFace at hface
    obtain ⟨hQ, hsigned⟩ := Finset.mem_filter.mp hface
    have hb : x ∈ boundarySites (centeredBox (k + 1) N) := by
      apply (mem_centeredBox_boundary_iff x).mpr
      refine ⟨hQ, i, ?_⟩
      cases sign
      · exact Or.inr (by simpa [N] using hsigned)
      · exact Or.inl (by simpa [N] using hsigned)
    exact Finset.mem_filter.mpr ⟨by rwa [appendix_cube_eq_centeredBox],
      (centeredBox_boundary_norm_iff x).mp hb⟩
  · intro hx
    have hb := (centeredBox_boundary_norm_iff (c := N) x).mpr (Finset.mem_filter.mp hx).2
    obtain ⟨hQ, i, hi | hi⟩ := (mem_centeredBox_boundary_iff x).mp hb
    · refine Finset.mem_biUnion.mpr ⟨(i, true), Finset.mem_univ _, ?_⟩
      rw [typicalFace_zero t ht]
      unfold signedCubeFace
      exact Finset.mem_filter.mpr ⟨hQ, by simpa [N] using hi⟩
    · refine Finset.mem_biUnion.mpr ⟨(i, false), Finset.mem_univ _, ?_⟩
      rw [typicalFace_zero t ht]
      unfold signedCubeFace
      exact Finset.mem_filter.mpr ⟨hQ, by simpa [N] using hi⟩

/-- A single scale threshold makes all the rounded radii admissible for
both mean bounds and the lower heart-hit rate. -/
theorem typicalMomentCube_eventually_scales (cc : ℝ) (hc : 0 < cc) (hc1 : cc ≤ 1 / 32) :
    ∃ t₀ : ℕ, 9 ≤ t₀ ∧ ∀ t : ℕ, t₀ ≤ t →
      let N := (t - 1) / 2
      let L := N / 2
      let H := typicalHeartRadius t cc
      1 ≤ N ∧ 1 ≤ H ∧ 2 * L ≤ N ∧ H ≤ L ∧ 5 * H ≤ N ∧
        (N : ℝ) / 4 ≤ (L : ℝ) - 2 * H ∧
        (cc / 2) * (N : ℝ) ≤ (H : ℝ) ∧ (H : ℝ) ≤ (2 * cc) * (N : ℝ) := by
  obtain ⟨m, hm⟩ := exists_nat_ge (2 / cc)
  refine ⟨max 9 (2 * m + 1), le_max_left _ _, ?_⟩
  intro t ht N L H
  have ht9 : 9 ≤ t := (le_max_left 9 (2 * m + 1)).trans ht
  have htm : 2 * m + 1 ≤ t := (le_max_right 9 (2 * m + 1)).trans ht
  have hN4 : 4 ≤ N := by dsimp [N]; omega
  have hN4' : (4 : ℝ) ≤ N := by exact_mod_cast hN4
  have hmN : (m : ℝ) ≤ N := by exact_mod_cast (show m ≤ N by dsimp [N]; omega)
  have hccN : (2 : ℝ) ≤ cc * N := by
    have h := (div_le_iff₀ hc).mp (hm.trans hmN)
    linarith
  obtain ⟨hlo, hhi⟩ := typicalHeartRadius_scale t (by omega) cc hc
  change cc * (N : ℝ) - 1 ≤ (H : ℝ) at hlo
  change (H : ℝ) ≤ (2 * cc) * (N : ℝ) at hhi
  have hH1 : 1 ≤ H := by exact_mod_cast (show (1 : ℝ) ≤ H by linarith)
  have hL : 2 * L ≤ N := by dsimp [L]; omega
  have hL' : (N : ℝ) ≤ 2 * L + 1 := by
    exact_mod_cast (show N ≤ 2 * L + 1 by dsimp [L]; omega)
  have hHN : (H : ℝ) ≤ (N : ℝ) / 16 := by
    have h := mul_le_mul_of_nonneg_right hc1 (show (0 : ℝ) ≤ N by positivity)
    nlinarith only [h, hhi]
  have hgap : (N : ℝ) / 4 ≤ (L : ℝ) - 2 * H := by linarith
  have hHnonneg : (0 : ℝ) ≤ H := Nat.cast_nonneg H
  have hHL : H ≤ L := by exact_mod_cast (show (H : ℝ) ≤ L by linarith)
  have h5 : 5 * H ≤ N := by exact_mod_cast (show 5 * (H : ℝ) ≤ N by linarith)
  exact ⟨by omega, hH1, hL, hHL, h5, hgap, by linarith, hhi⟩

end NearCritical.Section10
