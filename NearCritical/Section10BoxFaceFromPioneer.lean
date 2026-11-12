module

public import NearCritical.Section10FaceCountUpper
public import NearCritical.LatticeInversion
public import NearCritical.HalfSpaceSubcritical

/-! `BoxFaceFirstMoment` DERIVED from the half-space pioneer mass.

For a root `x` of the box and a face, the box connection is a half-space
connection; translating the root to the origin (and inverting the lattice for
the upper face) turns the sum over the face into part of the pioneer sum
`psi_pc(H_m)` at depth `m = dist(x, face hyperplane) >= 0`.

* `halfSpace_face_sum_le_pioneer`: the translation step.
* `boxFaceFirstMoment_of_pioneerMass`: from `psi_pc(H_m) <= B` for all `m >= 0`.
* `boxFaceFirstMoment_of_normalized`: from the cited
  `HalfSpacePioneerNormalizedInput` (depths `m >= 1`, at `p = p_c`) and the
  depth-0 bound `psi_pc(H_0) <= B` (source eq.expansion_2 at `n = 0`; a separate
  cited hypothesis, since the normalized input excludes `m = 0`).
-/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open MeasureTheory
open scoped Classical ENNReal

theorem halfSpace_face_sum_le_pioneer {d : ℕ} (p : unitInterval) (i : Fin d) (b : ℤ)
    (x : Vertex d) (F : Finset (Vertex d)) (hF : ∀ y ∈ F, y i = b) :
    ∑ y ∈ F, percolation d p (connectionToSetEvent {z | b ≤ z i} x {y}) ≤
      halfSpacePioneerMass p i (x i - b) := by
  have hterm : ∀ y ∈ F, percolation d p (connectionToSetEvent {z | b ≤ z i} x {y}) =
      (fun u : Vertex d => if u i = -(x i - b) then
        percolation d p (connectionToSetEvent {z | -(x i - b) ≤ z i} 0 {u}) else 0) (y - x) := by
    intro y hy
    have h := connectionToSet_probability_translation p x 0 {z | -(x i - b) ≤ z i} {y - x}
    rw [translate_halfSpace] at h
    have e : -(x i - b) + x i = b := by ring
    simp only [add_zero, Set.image_singleton, add_sub_cancel, e] at h
    have hu : (y - x) i = -(x i - b) := by
      rw [Pi.sub_apply, hF y hy]
      ring
    simp only [if_pos hu]
    exact h
  rw [Finset.sum_congr rfl hterm,
    ← Finset.sum_image (f := fun u : Vertex d => if u i = -(x i - b) then
        percolation d p (connectionToSetEvent {z | -(x i - b) ≤ z i} 0 {u}) else 0)
      (g := fun y => y - x) (fun a _ c _ h => sub_left_injective h)]
  exact ENNReal.sum_le_tsum _

lemma neg_image_upper_halfSpace {d : ℕ} (i : Fin d) (N : ℤ) :
    Neg.neg '' {z : Vertex d | z i ≤ N} = {z | -N ≤ z i} := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    change w i ≤ N at hw
    change -N ≤ -w i
    omega
  · intro hz
    change -N ≤ z i at hz
    refine ⟨-z, ?_, neg_neg z⟩
    change -z i ≤ N
    omega

theorem boxFaceFirstMoment_of_pioneerMass {d : ℕ} {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ (i : Fin d) (m : ℕ),
      halfSpacePioneerMass (criticalPoint d) i (m : ℤ) ≤ ENNReal.ofReal B) :
    BoxFaceFirstMoment d B := by
  intro N x hx f
  obtain ⟨i, s⟩ := f
  have hxi := mem_centeredBox.mp hx i
  have hface : ∀ y ∈ signedCubeFace d N (i, s), y i = if s then (N : ℤ) else -(N : ℤ) := by
    intro y hy
    unfold signedCubeFace at hy
    exact (Finset.mem_filter.mp hy).2
  have hE : ∑ y ∈ signedCubeFace d N (i, s), percolation d (criticalPoint d)
      (connectionToSetEvent (centeredBox d N : Set (Vertex d)) x {y}) ≤ ENNReal.ofReal B := by
    cases s
    · have hsub : (centeredBox d N : Set (Vertex d)) ⊆ {z | -(N : ℤ) ≤ z i} :=
        fun z hz => (mem_centeredBox.mp (Finset.mem_coe.mp hz) i).1
      obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le (show (0:ℤ) ≤ x i - -(N : ℤ) by omega)
      calc _ ≤ ∑ y ∈ signedCubeFace d N (i, false), percolation d (criticalPoint d)
            (connectionToSetEvent {z | -(N : ℤ) ≤ z i} x {y}) :=
            Finset.sum_le_sum fun y _ =>
              measure_mono (connectionToSetEvent_mono hsub subset_rfl x)
        _ ≤ halfSpacePioneerMass (criticalPoint d) i (x i - -(N : ℤ)) :=
            halfSpace_face_sum_le_pioneer _ i _ x _ (fun y hy => by simpa using hface y hy)
        _ ≤ _ := by rw [hm]; exact h i m
    · have hsub : (centeredBox d N : Set (Vertex d)) ⊆ {z | z i ≤ (N : ℤ)} :=
        fun z hz => (mem_centeredBox.mp (Finset.mem_coe.mp hz) i).2
      obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le (show (0:ℤ) ≤ (-x) i - -(N : ℤ) by
        rw [Pi.neg_apply]; omega)
      have hinv : ∀ y : Vertex d, percolation d (criticalPoint d)
          (connectionToSetEvent {z | z i ≤ (N : ℤ)} x {y}) =
          percolation d (criticalPoint d)
            (connectionToSetEvent {z | -(N : ℤ) ≤ z i} (-x) {-y}) := by
        intro y
        have h1 := connectionToSet_probability_inversion (criticalPoint d) x
          {z : Vertex d | z i ≤ (N : ℤ)} {y}
        rw [neg_image_upper_halfSpace, Set.image_singleton] at h1
        exact h1.symm
      calc _ ≤ ∑ y ∈ signedCubeFace d N (i, true), percolation d (criticalPoint d)
            (connectionToSetEvent {z | z i ≤ (N : ℤ)} x {y}) :=
            Finset.sum_le_sum fun y _ =>
              measure_mono (connectionToSetEvent_mono hsub subset_rfl x)
        _ = ∑ y ∈ (signedCubeFace d N (i, true)).image Neg.neg, percolation d (criticalPoint d)
            (connectionToSetEvent {z | -(N : ℤ) ≤ z i} (-x) {y}) := by
            rw [Finset.sum_image (fun a _ c _ h => neg_injective h)]
            exact Finset.sum_congr rfl fun y _ => hinv y
        _ ≤ halfSpacePioneerMass (criticalPoint d) i ((-x) i - -(N : ℤ)) :=
            halfSpace_face_sum_le_pioneer _ i _ (-x) _ (fun y hy => by
              obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hy
              have := hface w hw
              simp only [if_true] at this
              rw [Pi.neg_apply, this])
        _ ≤ _ := by rw [hm]; exact h i m
  have hreal : ∑ y ∈ signedCubeFace d N (i, s), (percolation d (criticalPoint d)).real
      (connectionToSetEvent (centeredBox d N : Set (Vertex d)) x {y}) =
      (∑ y ∈ signedCubeFace d N (i, s), percolation d (criticalPoint d)
        (connectionToSetEvent (centeredBox d N : Set (Vertex d)) x {y})).toReal := by
    rw [ENNReal.toReal_sum (fun y _ => measure_ne_top _ _)]
    rfl
  rw [hreal]
  exact ENNReal.toReal_le_of_le_ofReal hB hE

theorem boxFaceFirstMoment_of_normalized {d : ℕ} {B b : ℝ} (hB : 0 ≤ B)
    (pioneers : ∀ i : Fin d, HalfSpacePioneerNormalizedInput i B b)
    (h0 : ∀ i : Fin d,
      halfSpacePioneerMass (criticalPoint d) i (0 : ℤ) ≤ ENNReal.ofReal B) :
    BoxFaceFirstMoment d B := by
  refine boxFaceFirstMoment_of_pioneerMass hB fun i m => ?_
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simpa using h0 i
  · have h := pioneers i (criticalPoint d) m hm
      (by linarith [(criticalPoint d).2.1]) le_rfl
    simpa using h

end NearCritical.Section10
