module

public import NearCritical.FiniteSlabConvolution
public import NearCritical.FiniteTwoPhaseSlabModel
public import NearCritical.ProfileCountableBKStrict

/-! NEW actual finite two-phase slab convolution. The maximum-height path
split is deterministic; BK uses the proved actual independent-profile law.
Changing the profile top uses only the restricted event's local rate identity.
The backward row remains in the SAME finite U, without cutoff stationarity. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Set MeasureTheory
open scoped Classical

private lemma twoPhase_finite_cutoff_real {d : ℕ} (i : Fin d) (m h n : ℤ)
    (hhn : h ≤ n) (p q : unitInterval) (U : Finset (Vertex d)) (x y : Vertex d) :
    (percolationProfile d (twoPhaseSlabProfile i m n p q)).real
      (finiteSlabConnectionEvent U i 0 h x y) =
    (percolationProfile d (twoPhaseSlabProfile i m h p q)).real
      (finiteSlabConnectionEvent U i 0 h x y) := by
  have he := twoPhaseSlab_connection_cutoff_law i m h n hhn p q
    (finiteHeightSlab i 0 h ∩ (U : Set (Vertex d))) (fun _ hv ↦ hv.1.2) x {y}
  exact congrArg ENNReal.toReal he

private lemma twoPhase_finite_height_regroup {d : ℕ} (U : Finset (Vertex d)) (i : Fin d)
    (a b : ℤ) (f : Vertex d → ℝ) :
    (∑ z ∈ U, if a ≤ z i ∧ z i ≤ b then f z else 0) =
      ∑ h ∈ Finset.Icc a b, ∑ z ∈ U, if z i = h then f z else 0 := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z _
  simp [eq_comm]

/-- Actual finite maximum-height union and profile BK. Both profile factors
are retained, then individually identified with the smaller-top law ONLY on
that restricted event. No convolution or BK inequality is a premise. -/
theorem finiteTwoPhaseSlab_connection_maximum_bk {d : ℕ} (p q P : unitInterval)
    (hP : (P : ℝ) < 1) (hpP : p ≤ P) (hqP : q ≤ P)
    (U : Finset (Vertex d)) (i : Fin d) (m n : ℤ) (x y : Vertex d) :
    (percolationProfile d (twoPhaseSlabProfile i m n p q)).real
      (finiteSlabConnectionEvent U i 0 n x y) ≤
      ∑ h ∈ Finset.Icc (max (x i) (y i)) n, ∑ z ∈ U, if z i = h then
        (percolationProfile d (twoPhaseSlabProfile i m h p q)).real
          (finiteSlabConnectionEvent U i 0 h x z) *
        (percolationProfile d (twoPhaseSlabProfile i m h p q)).real
          (finiteSlabConnectionEvent U i 0 h y z) else 0 := by
  let μ := percolationProfile d (twoPhaseSlabProfile i m n p q)
  have hr : ∀ e, twoPhaseSlabProfile i m n p q e ≤ P := by
    intro e
    unfold twoPhaseSlabProfile
    split_ifs
    · exact hqP
    · exact hpP
  let C := fun z : Vertex d ↦ {ω : Configuration d | max (x i) (y i) ≤ z i ∧ z i ≤ n ∧
    DisjointOccurrence (finiteSlabConnectionEvent U i 0 (z i) x z)
      (finiteSlabConnectionEvent U i 0 (z i) y z) ω}
  have hsub : finiteSlabConnectionEvent U i 0 n x y ⊆ ⋃ z ∈ U, C z := by
    intro ω hω
    obtain ⟨z,hzU,hxy,hzn,hdis⟩ := finiteSlab_connection_maximum_split U i 0 n x y hω
    exact Set.mem_iUnion.mpr ⟨z,Set.mem_iUnion.mpr ⟨hzU,hxy,hzn,hdis⟩⟩
  calc
    _ ≤ μ.real (⋃ z ∈ U, C z) := measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ ∑ z ∈ U, μ.real (C z) := measureReal_biUnion_finset_le U C
    _ ≤ ∑ z ∈ U, if max (x i) (y i) ≤ z i ∧ z i ≤ n then
        (percolationProfile d (twoPhaseSlabProfile i m (z i) p q)).real
          (finiteSlabConnectionEvent U i 0 (z i) x z) *
        (percolationProfile d (twoPhaseSlabProfile i m (z i) p q)).real
          (finiteSlabConnectionEvent U i 0 (z i) y z) else 0 := by
      apply Finset.sum_le_sum
      intro z _
      by_cases hz : max (x i) (y i) ≤ z i ∧ z i ≤ n
      · rw [ite_eq_left hz]
        have hBK := percolationProfile_bk_of_uniform_lt_one d (twoPhaseSlabProfile i m n p q)
          P hP hr (finiteSlabConnectionEvent U i 0 (z i) x z)
          (finiteSlabConnectionEvent U i 0 (z i) y z)
          (finiteSlabConnectionEvent_increasing U i 0 (z i) x z)
          (finiteSlabConnectionEvent_increasing U i 0 (z i) y z)
        have hb := (measureReal_mono (show C z ⊆ {ω | DisjointOccurrence
          (finiteSlabConnectionEvent U i 0 (z i) x z)
          (finiteSlabConnectionEvent U i 0 (z i) y z) ω} from fun _ h ↦ h.2.2)
          (measure_ne_top _ _)).trans hBK
        rw [twoPhase_finite_cutoff_real i m (z i) n hz.2 p q U x z,
          twoPhase_finite_cutoff_real i m (z i) n hz.2 p q U y z] at hb
        exact hb
      · have hempty : C z = ∅ := by
          ext ω
          simp only [C,Set.mem_ofPred_eq,Set.mem_empty_iff_false,iff_false]
          exact fun h ↦ hz ⟨h.1,h.2.1⟩
        simp only [ite_eq_right hz,hempty,measureReal_empty,le_refl]
    _ = _ := by
      rw [twoPhase_finite_height_regroup]
      apply Finset.sum_congr rfl
      intro h _
      apply Finset.sum_congr rfl
      intro z _
      by_cases hz : z i = h
      · rw [ite_eq_left hz,ite_eq_left hz,hz]
      · simp only [ite_eq_right hz]

private lemma twoPhase_finite_sum_ite_sum {Y H : Type*} (U : Finset Y) (J : Finset H)
    (P : Y → Prop) [DecidablePred P] (g : Y → H → ℝ) :
    (∑ y ∈ U, if P y then ∑ h ∈ J, g y h else 0) =
      ∑ h ∈ J, ∑ y ∈ U, if P y then g y h else 0 := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  by_cases hy : P y <;> simp [hy]

/-- Exact finite double-plane regrouping. Endpoint reversal turns the second
factor into the actual backward row FROM z in the SAME cutoff U and law. -/
lemma finiteTwoPhaseSlab_double_plane_sum {d : ℕ} (p q : unitInterval)
    (U : Finset (Vertex d)) (i : Fin d) (m h j : ℤ) (x : Vertex d) :
    (∑ y ∈ U, if y i = j then ∑ z ∈ U, if z i = h then
      (percolationProfile d (twoPhaseSlabProfile i m h p q)).real
        (finiteSlabConnectionEvent U i 0 h x z) *
      (percolationProfile d (twoPhaseSlabProfile i m h p q)).real
        (finiteSlabConnectionEvent U i 0 h y z) else 0 else 0) =
      ∑ z ∈ U, if z i = h then
        (percolationProfile d (twoPhaseSlabProfile i m h p q)).real
          (finiteSlabConnectionEvent U i 0 h x z) *
            finiteTwoPhaseSlabRowMean p q U i m h z j else 0 := by
  calc
    _ = ∑ y ∈ U, ∑ z ∈ U, if z i = h then
        (percolationProfile d (twoPhaseSlabProfile i m h p q)).real
          (finiteSlabConnectionEvent U i 0 h x z) *
        (if y i = j then (percolationProfile d (twoPhaseSlabProfile i m h p q)).real
          (finiteSlabConnectionEvent U i 0 h y z) else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro y _
      by_cases hy : y i = j <;> simp [hy]
    _ = ∑ z ∈ U, ∑ y ∈ U, if z i = h then
        (percolationProfile d (twoPhaseSlabProfile i m h p q)).real
          (finiteSlabConnectionEvent U i 0 h x z) *
        (if y i = j then (percolationProfile d (twoPhaseSlabProfile i m h p q)).real
          (finiteSlabConnectionEvent U i 0 h y z) else 0) else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro z _
      by_cases hz : z i = h
      · simp only [ite_eq_left hz,finiteTwoPhaseSlabRowMean,Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro y _
        by_cases hy : y i = j
        · simp only [ite_eq_left hy]
          rw [show finiteSlabConnectionEvent U i 0 h y z = finiteSlabConnectionEvent U i 0 h z y from
            connectionToSetEvent_singleton_symm _ y z]
        · simp only [ite_eq_right hy,mul_zero]
      · simp only [ite_eq_right hz,Finset.sum_const_zero]

/-- Actual finite two-phase row convolution. The smaller-top profile equality
was proved event-locally above; the backward finite row remains unaltered. -/
theorem finiteTwoPhaseSlabRowMean_convolution {d : ℕ} (p q P : unitInterval)
    (hP : (P : ℝ) < 1) (hpP : p ≤ P) (hqP : q ≤ P)
    (U : Finset (Vertex d)) (i : Fin d) (m n : ℤ) (x : Vertex d) (j : ℤ) :
    finiteTwoPhaseSlabRowMean p q U i m n x j ≤
      ∑ h ∈ Finset.Icc (max (x i) j) n, ∑ z ∈ U, if z i = h then
        (percolationProfile d (twoPhaseSlabProfile i m h p q)).real
          (finiteSlabConnectionEvent U i 0 h x z) *
            finiteTwoPhaseSlabRowMean p q U i m h z j else 0 := by
  calc
    _ ≤ ∑ y ∈ U, if y i = j then ∑ h ∈ Finset.Icc (max (x i) j) n,
        ∑ z ∈ U, if z i = h then
          (percolationProfile d (twoPhaseSlabProfile i m h p q)).real
            (finiteSlabConnectionEvent U i 0 h x z) *
          (percolationProfile d (twoPhaseSlabProfile i m h p q)).real
            (finiteSlabConnectionEvent U i 0 h y z) else 0 else 0 := by
      apply Finset.sum_le_sum
      intro y _
      by_cases hy : y i = j
      · rw [ite_eq_left hy,ite_eq_left hy]
        simpa only [hy] using finiteTwoPhaseSlab_connection_maximum_bk p q P hP hpP hqP U i m n x y
      · simp only [ite_eq_right hy,le_refl]
    _ = ∑ h ∈ Finset.Icc (max (x i) j) n, ∑ y ∈ U, if y i = j then
        ∑ z ∈ U, if z i = h then
          (percolationProfile d (twoPhaseSlabProfile i m h p q)).real
            (finiteSlabConnectionEvent U i 0 h x z) *
          (percolationProfile d (twoPhaseSlabProfile i m h p q)).real
            (finiteSlabConnectionEvent U i 0 h y z) else 0 else 0 :=
      twoPhase_finite_sum_ite_sum U (Finset.Icc (max (x i) j) n) (fun y : Vertex d ↦ y i = j) _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro h _
      exact finiteTwoPhaseSlab_double_plane_sum p q U i m h j x

end NearCritical
