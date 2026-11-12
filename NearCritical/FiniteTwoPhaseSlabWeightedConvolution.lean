module

public import NearCritical.FiniteTwoPhaseSlabConvolution
public import NearCritical.FiniteTwoPhaseSlabBoundaryFamily

/-! Weighted actual finite two-phase convolution. Both forward and backward
rows remain in the same cutoff. No stationarity or convolution estimate is
supplied as a hypothesis. Only individual finite-family entries are used. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Set Finset MeasureTheory
open scoped Classical

/-- The actual finite convolution and the actual weighted boundary family give
an off-diagonal bound. The source and target need not be interchangeable in a
fixed cutoff: the backward family is retained separately. -/
theorem finiteTwoPhaseSlabRowMean_weighted_le_boundaryMaximum_sq {d : ℕ}
    (p q P : unitInterval) (hP : (P : ℝ) < 1) (hpP : p ≤ P) (hqP : q ≤ P)
    (c : ℝ) (hc : 0 ≤ c) (U : Finset (Vertex d)) (i : Fin d)
    (m n : ℤ) (N : ℕ) (hnN : n ≤ (N : ℤ))
    (x : Vertex d) (hx : x ∈ U) (j : ℤ) (hj : j ∈ Finset.Icc (0 : ℤ) n) :
    Real.exp (c * Real.sqrt ((criticalPoint d : ℝ) - (q : ℝ)) *
      twoPhaseSlabDistance m (x i) j) *
        finiteTwoPhaseSlabRowMean p q U i m n x j ≤
      (N + 1 : ℝ) * (finiteTwoPhaseBoundaryMaximum q c (p : ℝ) U i m (N : ℤ)) ^ 2 := by
  let a : ℝ := c * Real.sqrt ((criticalPoint d : ℝ) - (q : ℝ))
  let M : ℝ := finiteTwoPhaseBoundaryMaximum q c (p : ℝ) U i m (N : ℤ)
  let W : ℝ := Real.exp (a * twoPhaseSlabDistance m (x i) j)
  have ha : 0 ≤ a := mul_nonneg hc (Real.sqrt_nonneg _)
  have hM : 0 ≤ M := finiteTwoPhaseBoundaryMaximum_nonneg q c (p : ℝ) U i m (N : ℤ)
  have hW : 0 ≤ W := Real.exp_nonneg _
  have hlevels : Finset.Icc (max (x i) j) n ⊆ Finset.Icc (0 : ℤ) (N : ℤ) := by
    intro h hh
    obtain ⟨hhlo, hhhi⟩ := Finset.mem_Icc.mp hh
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hj).1.trans ((le_max_right _ _).trans hhlo),
      hhhi.trans hnN⟩
  have hcut (h : ℤ) (hh : h ∈ Finset.Icc (max (x i) j) n) :
      W * (∑ z ∈ U, if z i = h then
        (percolationProfile d (twoPhaseSlabProfile i m h p q)).real
          (finiteSlabConnectionEvent U i 0 h x z) *
            finiteTwoPhaseSlabRowMean p q U i m h z j else 0) ≤ M ^ 2 := by
    have hhN := hlevels hh
    have hjh : j ∈ Finset.Icc (0 : ℤ) h := Finset.mem_Icc.mpr
      ⟨(Finset.mem_Icc.mp hj).1, (le_max_right _ _).trans (Finset.mem_Icc.mp hh).1⟩
    let A : ℝ := Real.exp (a * twoPhaseSlabDistance m (x i) h)
    let B : ℝ := Real.exp (a * twoPhaseSlabDistance m h j)
    have hAB : W ≤ A * B := by
      dsimp [W, A, B]
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have ht := mul_le_mul_of_nonneg_left (twoPhaseSlabDistance_triangle m (x i) j h) ha
      nlinarith
    have hforward : A * finiteTwoPhaseSlabRowMean p q U i m h x h ≤ M :=
      finiteTwoPhase_forward_row_le_boundaryMaximum p q c U i m (N : ℤ) h hhN x hx
    calc
      _ ≤ ∑ z ∈ U, if z i = h then
          (A * (percolationProfile d (twoPhaseSlabProfile i m h p q)).real
            (finiteSlabConnectionEvent U i 0 h x z)) *
          (B * finiteTwoPhaseSlabRowMean p q U i m h z j) else 0 := by
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro z hz
        by_cases hzh : z i = h
        · rw [ite_eq_left hzh, ite_eq_left hzh]
          have hnon : 0 ≤
              (percolationProfile d (twoPhaseSlabProfile i m h p q)).real
                (finiteSlabConnectionEvent U i 0 h x z) *
              finiteTwoPhaseSlabRowMean p q U i m h z j := by
            apply mul_nonneg measureReal_nonneg
            rw [finiteTwoPhaseSlabRowMean_eq_expectation]
            exact finiteTwoPhaseSlabRowExpectation_nonneg p q U i m h z j
          convert mul_le_mul_of_nonneg_right hAB hnon using 1 <;> ring
        · simp only [ite_eq_right hzh, mul_zero, le_refl]
      _ ≤ ∑ z ∈ U, if z i = h then
          (A * (percolationProfile d (twoPhaseSlabProfile i m h p q)).real
            (finiteSlabConnectionEvent U i 0 h x z)) * M else 0 := by
        apply Finset.sum_le_sum
        intro z hz
        by_cases hzh : z i = h
        · rw [ite_eq_left hzh, ite_eq_left hzh]
          have hback : B * finiteTwoPhaseSlabRowMean p q U i m h z j ≤ M :=
            finiteTwoPhase_backward_row_le_boundaryMaximum p q c U i m (N : ℤ) h
              hhN z hz hzh j hjh
          exact mul_le_mul_of_nonneg_left hback (mul_nonneg (Real.exp_nonneg _) measureReal_nonneg)
        · simp only [ite_eq_right hzh, le_refl]
      _ = (A * finiteTwoPhaseSlabRowMean p q U i m h x h) * M := by
        unfold finiteTwoPhaseSlabRowMean
        rw [Finset.mul_sum, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro z hz
        by_cases hzh : z i = h <;> simp [hzh]
      _ ≤ M * M := mul_le_mul_of_nonneg_right hforward hM
      _ = M ^ 2 := by ring
  have hcard : ((Finset.Icc (max (x i) j) n).card : ℝ) ≤ (N + 1 : ℝ) := by
    have hcount : (Finset.Icc (0 : ℤ) (N : ℤ)).card = N + 1 := by
      rw [Int.card_Icc]
      omega
    have h := Finset.card_le_card hlevels
    rw [hcount] at h
    exact_mod_cast h
  change W * finiteTwoPhaseSlabRowMean p q U i m n x j ≤ (N + 1 : ℝ) * M ^ 2
  calc
    _ ≤ W * (∑ h ∈ Finset.Icc (max (x i) j) n, ∑ z ∈ U, if z i = h then
        (percolationProfile d (twoPhaseSlabProfile i m h p q)).real
          (finiteSlabConnectionEvent U i 0 h x z) *
            finiteTwoPhaseSlabRowMean p q U i m h z j else 0) :=
      mul_le_mul_of_nonneg_left
        (finiteTwoPhaseSlabRowMean_convolution p q P hP hpP hqP U i m n x j) hW
    _ = ∑ h ∈ Finset.Icc (max (x i) j) n, W * (∑ z ∈ U, if z i = h then
        (percolationProfile d (twoPhaseSlabProfile i m h p q)).real
          (finiteSlabConnectionEvent U i 0 h x z) *
            finiteTwoPhaseSlabRowMean p q U i m h z j else 0) := Finset.mul_sum _ _ _
    _ ≤ ∑ _h ∈ Finset.Icc (max (x i) j) n, M ^ 2 := Finset.sum_le_sum hcut
    _ = ((Finset.Icc (max (x i) j) n).card : ℝ) * M ^ 2 := by
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right hcard (sq_nonneg M)

/-- The same actual row bound with its separation decay displayed explicitly.
The two finite boundary factors, not cutoff stationarity, supply the square. -/
theorem finiteTwoPhaseSlabRowMean_le_boundaryMaximum_sq_decay {d : ℕ}
    (p q P : unitInterval) (hP : (P : ℝ) < 1) (hpP : p ≤ P) (hqP : q ≤ P)
    (c : ℝ) (hc : 0 ≤ c) (U : Finset (Vertex d)) (i : Fin d)
    (m n : ℤ) (N : ℕ) (hnN : n ≤ (N : ℤ))
    (x : Vertex d) (hx : x ∈ U) (j : ℤ) (hj : j ∈ Finset.Icc (0 : ℤ) n) :
    finiteTwoPhaseSlabRowMean p q U i m n x j ≤
      (N + 1 : ℝ) * (finiteTwoPhaseBoundaryMaximum q c (p : ℝ) U i m (N : ℤ)) ^ 2 *
        Real.exp (-(c * Real.sqrt ((criticalPoint d : ℝ) - (q : ℝ)) *
          twoPhaseSlabDistance m (x i) j)) := by
  let w : ℝ := c * Real.sqrt ((criticalPoint d : ℝ) - (q : ℝ)) *
    twoPhaseSlabDistance m (x i) j
  have h := finiteTwoPhaseSlabRowMean_weighted_le_boundaryMaximum_sq
    p q P hP hpP hqP c hc U i m n N hnN x hx j hj
  have hinv : Real.exp w * Real.exp (-w) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  calc
    _ = (Real.exp w * finiteTwoPhaseSlabRowMean p q U i m n x j) * Real.exp (-w) := by
      rw [mul_right_comm, hinv, one_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right h (Real.exp_nonneg _)

end NearCritical
