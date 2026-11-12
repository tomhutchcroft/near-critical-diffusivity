module

public import NearCritical.AppendixBoundaryFirstMoment
public import NearCritical.AppendixErrExpectation
public import NearCritical.Section10MarkCard

/-! Translate the wider slab box and its top face to the root of the
Appendix A lower two-point construction. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory Set
open scoped Classical ENNReal

/-- The wide prism based at a point of the negative face. -/
def appendixWideBox {d : ℕ} (i : Fin d) (h R : ℕ) (x : Vertex d) : Finset (Vertex d) :=
  (boundaryBox i h R).image (fun u => x + u)

/-- The inner face of the translated wide prism. -/
def appendixWideFace {d : ℕ} (i : Fin d) (h R : ℕ) (x : Vertex d) : Finset (Vertex d) :=
  (boundaryTop i h R).image (fun u => x + u)

/-- The translated wide prism and face supply the geometric guards of
`appendix_box_face_avoid_lower_on_domain`. -/
theorem appendixWideBox_geometry {d n h R : ℕ} (i : Fin d) (x : Vertex d) {α : ℝ}
    (hα : α ≤ 1) (hhR : h ≤ R) (hR : (R : ℝ) ≤ α * (n : ℝ) / 4)
    (hxi : x i = -(n : ℤ)) (hx : ∀ j, j ≠ i → |(x j : ℝ)| ≤ (n : ℝ) - α * (n : ℝ)) :
    let Q := appendixWideBox i h R x
    let F := appendixWideFace i h R x
    x ∈ Q ∧ Q ⊆ centeredBox d n ∧ (∀ u ∈ Q, u i ≤ -(n : ℤ) + h) ∧
      F ⊆ Q ∧ (∀ w ∈ F, w i = -(n : ℤ) + h) ∧
      (∀ w ∈ F, ∀ j, j ≠ i → |(w j : ℝ) - (x j : ℝ)| ≤ α * (n : ℝ) / 4) := by
  intro Q F
  have hroot : x ∈ Q := by
    refine Finset.mem_image.mpr ⟨0, ?_, by simp⟩
    exact Finset.mem_filter.mpr ⟨mem_centeredBox.mpr (fun _ => by simp), by simp⟩
  have hQT : Q ⊆ centeredBox d n := by
    intro u hu
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨hvbox, hvheight⟩ := Finset.mem_filter.mp hv
    apply mem_centeredBox.mpr
    intro j
    have hR' : (R : ℝ) ≤ (n : ℝ) :=
      hR.trans (by nlinarith [Nat.cast_nonneg (α := ℝ) n])
    by_cases hj : j = i
    · subst j
      have hnR : R ≤ n := by exact_mod_cast hR'
      rw [Pi.add_apply, hxi]
      obtain ⟨hlo, hhi⟩ := hvheight
      constructor <;> omega
    · have hvj := mem_centeredBox.mp hvbox j
      have hxj := abs_le.mp (hx j hj)
      have hlo : -(n : ℝ) ≤ ((x j : ℤ) : ℝ) + (v j : ℝ) := by
        have hvj' : -(R : ℝ) ≤ (v j : ℝ) := by exact_mod_cast hvj.1
        linarith [Nat.cast_nonneg (α := ℝ) R]
      have hhi : ((x j : ℤ) : ℝ) + (v j : ℝ) ≤ (n : ℝ) := by
        have hvj' : (v j : ℝ) ≤ (R : ℝ) := by exact_mod_cast hvj.2
        linarith [Nat.cast_nonneg (α := ℝ) R]
      rw [Pi.add_apply]
      exact ⟨by exact_mod_cast hlo, by exact_mod_cast hhi⟩
  have hQheight : ∀ u ∈ Q, u i ≤ -(n : ℤ) + h := by
    intro u hu
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hu
    rw [Pi.add_apply, hxi]
    have hvh := (Finset.mem_filter.mp hv).2.2
    omega
  have hFQ : F ⊆ Q := by
    intro u hu
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hu
    exact Finset.mem_image.mpr ⟨v, (Finset.mem_filter.mp hv).1, rfl⟩
  refine ⟨hroot, hQT, hQheight, hFQ, ?_, ?_⟩
  · intro u hu
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hu
    rw [Pi.add_apply, hxi, (Finset.mem_filter.mp hv).2]
  · intro u hu j _
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hu
    have hvj := mem_centeredBox.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hv).1).1 j
    have hv' : |(v j : ℝ)| ≤ (R : ℝ) :=
      abs_le.mpr ⟨by exact_mod_cast hvj.1, by exact_mod_cast hvj.2⟩
    calc
      _ = |(v j : ℝ)| := by rw [Pi.add_apply, Int.cast_add, add_sub_cancel_left]
      _ ≤ _ := hv'.trans hR

/-- The wide face has the correct codimension-one cardinality bound. -/
theorem appendixWideFace_card_le {d : ℕ} (i : Fin d) (h R : ℕ) (x : Vertex d) :
    (appendixWideFace i h R x).card ≤ (2 * R + 1) ^ (d - 1) := by
  refine Finset.card_image_le.trans ?_
  refine le_trans ?_ (Section10.signedCubeFace_card_le d R (i, true))
  refine Finset.card_le_card_of_injOn (fun u : Vertex d => Function.update u i (R : ℤ)) ?_ ?_
  · intro u hu
    obtain ⟨huB, _⟩ := Finset.mem_filter.mp hu
    have hubox := mem_centeredBox.mp (Finset.mem_filter.mp huB).1
    apply Finset.mem_filter.mpr
    refine ⟨mem_centeredBox.mpr ?_, by simp⟩
    intro j
    by_cases hj : j = i
    · subst j
      simp only [Function.update_self, le_refl, and_true]
      omega
    · simpa only [Function.update_of_ne hj] using hubox j
  · intro u hu v hv huv
    have hu' := (Finset.mem_filter.mp (Finset.mem_coe.mp hu)).2
    have hv' := (Finset.mem_filter.mp (Finset.mem_coe.mp hv)).2
    funext j
    by_cases hj : j = i
    · rw [hj, hu', hv']
    · simpa only [Function.update_of_ne hj] using congrFun huv j

/-- The mean cluster mass on a face is exactly its sum of actual two-point
probabilities. -/
theorem appendixBoxClusterMean_face_card_eq {d : ℕ} (p : unitInterval)
    (Q F : Finset (Vertex d)) (x : Vertex d) (hx : x ∈ Q) :
    appendixBoxClusterMean p Q x (fun C => ((C ∩ F).card : ℝ)) =
      ∑ w ∈ F, (percolation d p).real (connectionToSetEvent (Q : Set (Vertex d)) x {w}) := by
  let m (C : Finset (Vertex d)) := (percolation d p).real {ω | finiteBoxCluster ω Q x = C}
  have hstep (C : Finset (Vertex d)) :
      m C * ((C ∩ F).card : ℝ) = ∑ w ∈ F, if w ∈ C then m C else 0 := by
    rw [show ((C ∩ F).card : ℝ) = ∑ _ ∈ C ∩ F, (1 : ℝ) by simp,
      Finset.inter_comm C F, ← Finset.sum_ite_mem, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro w _
    split_ifs <;> simp
  unfold appendixBoxClusterMean
  change (∑ C ∈ Q.powerset, m C * ((C ∩ F).card : ℝ)) = _
  rw [Finset.sum_congr rfl (fun C _ => hstep C), Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w _
  rw [← Finset.sum_filter]
  have hpair := appendix_clusterPairWeight_eq p Q x hx w w
  simp only [and_self] at hpair
  have he : {ω : Configuration d | w ∈ finiteBoxCluster ω Q x} =
      connectionToSetEvent (Q : Set (Vertex d)) x {w} := by
    ext ω
    constructor
    · intro hw
      obtain ⟨hwQ, hreach⟩ := (mem_finiteBoxCluster ω Q x w).mp hw
      exact ⟨hx, w, rfl, hwQ, hreach⟩
    · rintro ⟨_, v, hv, hvQ, hreach⟩
      have hvw : v = w := hv
      subst v
      exact (mem_finiteBoxCluster ω Q x w).mpr ⟨hvQ, hreach⟩
  rw [he] at hpair
  exact hpair

/-- Transfer the top-face lower bound to the actual finite cluster measure
used in the two-point lower-bound argument. -/
theorem appendixWideBox_face_mass_lower {d : ℕ} (i : Fin d) (h R : ℕ) (x : Vertex d) (a : ℝ)
    (hmass : a ≤ ∑ w ∈ boundaryTop i h R, (percolation d (criticalPoint d)).real
      (connectionToSetEvent (boundaryBox i h R : Set (Vertex d)) 0 {w})) :
    a ≤ appendixBoxClusterMean (criticalPoint d) (appendixWideBox i h R x) x
      (fun C => ((C ∩ appendixWideFace i h R x).card : ℝ)) := by
  let p := criticalPoint d
  let B := boundaryBox i h R
  let Q := appendixWideBox i h R x
  have hx : x ∈ Q := by
    refine Finset.mem_image.mpr ⟨0, ?_, by simp⟩
    exact Finset.mem_filter.mpr ⟨mem_centeredBox.mpr (fun _ => by simp), by simp⟩
  have hcoe : (Q : Set (Vertex d)) = (fun u : Vertex d => x + u) '' (B : Set (Vertex d)) := by
    ext u
    exact Finset.mem_image
  rw [appendixBoxClusterMean_face_card_eq p Q _ x hx]
  unfold appendixWideFace
  rw [Finset.sum_image (fun _ _ _ _ h => add_left_cancel h)]
  refine hmass.trans (le_of_eq ?_)
  apply Finset.sum_congr rfl
  intro u _
  have h := connectionToSet_probability_translation p x 0 (B : Set (Vertex d)) {u}
  rw [← hcoe, add_zero, Set.image_singleton] at h
  exact congrArg ENNReal.toReal h.symm

end NearCritical
