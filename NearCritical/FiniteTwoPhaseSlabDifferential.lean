module

public import NearCritical.FiniteTwoPhaseSlabModel
public import NearCritical.FiniteSlabProfileOpening

/-! Actual finite two-phase slab Russo envelope. Only p-bonds vary; q stays
fixed. Both physical orientations and both original profile factors remain. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Set Finset BernoulliCalculus MeasureTheory ProbabilityTheory
open scoped Classical

/-- Exact real-parameter Russo identity for the literal finite row extension. -/
theorem finiteTwoPhaseSlabRowExpectation_russo {d : ℕ} (q p : ℝ) (hp : p ≠ 1)
    (U : Finset (Vertex d)) (i : Fin d) (m n : ℤ) (x : Vertex d) (j : ℤ) :
    HasDerivAt (fun t ↦ finiteTwoPhaseSlabRowExpectation q t U i m n x j)
      ((1-p)⁻¹ * ∑ e ∈ finiteTwoPhaseVariableMask U i m n,
        finiteExpectationProfile (maskProfile (finiteTwoPhaseVariableMask U i m n) q p)
          (fun η ↦ finiteSlabRowObservable U i 0 n x j (forceOpen e η) -
            finiteSlabRowObservable U i 0 n x j η)) p := by
  simpa only [finiteTwoPhaseSlabRowExpectation] using
    finiteExpectationProfile_russo (finiteTwoPhaseVariableMask U i m n) q p hp
      (finiteSlabRowObservable U i 0 n x j)

private lemma finiteTwoPhase_expectation_finsetSum {E Y : Type*} [Fintype E]
    (r : E → ℝ) (U : Finset Y) (g : Y → (E → Bool) → ℝ) :
    finiteExpectationProfile r (fun η ↦ ∑ y ∈ U, g y η) = ∑ y ∈ U, finiteExpectationProfile r (g y) := by
  simp only [finiteExpectationProfile, Finset.sum_mul]
  exact Finset.sum_comm

private lemma finiteTwoPhase_rowObservable_opening {d : ℕ} (U : Finset (Vertex d))
    (i : Fin d) (m n : ℤ) (x : Vertex d) (j : ℤ) (e : internalBondSet U)
    (η : (k : internalBondSet U) → Bool) :
    finiteSlabRowObservable U i m n x j (forceOpen e η) - finiteSlabRowObservable U i m n x j η =
      ∑ y ∈ U, if y i = j then
        (if forceOpen e η ∈ finiteSlabLocalConnectionEvent U i m n x y then (1 : ℝ) else 0) -
          (if η ∈ finiteSlabLocalConnectionEvent U i m n x y then 1 else 0) else 0 := by
  unfold finiteSlabRowObservable
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro y _
  by_cases hy : y i = j <;> simp [hy]

/-- Sum the actual profile opening bound over the target plane. Membership
in the variable mask proves that the tested edge has rate p, not q. -/
theorem finiteTwoPhaseSlab_row_opening_expectation_le {d : ℕ}
    (p q P : unitInterval) (hP : (P : ℝ) < 1) (hpP : p ≤ P) (hqP : q ≤ P)
    (U : Finset (Vertex d)) (i : Fin d) (m n : ℤ) (x : Vertex d) (j : ℤ)
    (e : internalBondSet U) (he : e ∈ finiteTwoPhaseVariableMask U i m n) :
    (1-(p : ℝ))⁻¹ * finiteExpectationProfile
      (maskProfile (finiteTwoPhaseVariableMask U i m n) (q : ℝ) (p : ℝ))
      (fun η ↦ finiteSlabRowObservable U i 0 n x j (forceOpen e η) -
        finiteSlabRowObservable U i 0 n x j η) ≤
      (percolationProfile d (twoPhaseSlabProfile i m n p q)).real
          (finiteSlabConnectionEvent U i 0 n x e.val.1) *
        finiteTwoPhaseSlabRowMean p q U i m n (bondTip e.val) j +
      (percolationProfile d (twoPhaseSlabProfile i m n p q)).real
          (finiteSlabConnectionEvent U i 0 n x (bondTip e.val)) *
        finiteTwoPhaseSlabRowMean p q U i m n e.val.1 j := by
  have hr : ∀ b, twoPhaseSlabProfile i m n p q b ≤ P := by
    intro b
    simp only [twoPhaseSlabProfile]
    split_ifs
    · exact hqP
    · exact hpP
  have hbit : twoPhaseSlabProfile i m n p q e.val = p := by
    have hn := (mem_finiteTwoPhaseVariableMask U i m n e).mp he
    simp only [twoPhaseSlabProfile,hn,ite_false]
  have hper (y : Vertex d) := finiteSlab_profile_opening_expectation_le
    (twoPhaseSlabProfile i m n p q) P hP hr U i 0 n x y e
  simp only [hbit,finiteTwoPhaseSlabProfile_restrict] at hper
  calc
    _ = ∑ y ∈ U, if y i = j then (1-(p : ℝ))⁻¹ * finiteExpectationProfile
        (maskProfile (finiteTwoPhaseVariableMask U i m n) (q : ℝ) (p : ℝ))
        (fun η ↦ (if forceOpen e η ∈ finiteSlabLocalConnectionEvent U i 0 n x y then (1 : ℝ) else 0) -
          (if η ∈ finiteSlabLocalConnectionEvent U i 0 n x y then 1 else 0)) else 0 := by
      simp_rw [finiteTwoPhase_rowObservable_opening]
      rw [finiteTwoPhase_expectation_finsetSum,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _
      by_cases hy : y i = j
      · simp only [ite_eq_left hy]
      · simp only [ite_eq_right hy,finiteExpectationProfile,zero_mul,Finset.sum_const_zero,mul_zero]
    _ ≤ ∑ y ∈ U, if y i = j then
        (percolationProfile d (twoPhaseSlabProfile i m n p q)).real
            (finiteSlabConnectionEvent U i 0 n x e.val.1) *
          (percolationProfile d (twoPhaseSlabProfile i m n p q)).real
            (finiteSlabConnectionEvent U i 0 n (bondTip e.val) y) +
        (percolationProfile d (twoPhaseSlabProfile i m n p q)).real
            (finiteSlabConnectionEvent U i 0 n x (bondTip e.val)) *
          (percolationProfile d (twoPhaseSlabProfile i m n p q)).real
            (finiteSlabConnectionEvent U i 0 n e.val.1 y) else 0 := by
      apply Finset.sum_le_sum
      intro y _
      by_cases hy : y i = j
      · rw [ite_eq_left hy,ite_eq_left hy]
        exact hper y
      · simp only [ite_eq_right hy,le_refl]
    _ = _ := by
      unfold finiteTwoPhaseSlabRowMean
      rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro y _
      by_cases hy : y i = j <;> simp [hy]

/-- The NEW finite two-phase row derivative envelope, proved from actual
opening support, profile Mecke and profile BK; no derivative estimate is input. -/
theorem finiteTwoPhaseSlabRowExpectation_deriv_le {d : ℕ}
    (p q P : unitInterval) (hP : (P : ℝ) < 1) (hpP : p ≤ P) (hqP : q ≤ P)
    (U : Finset (Vertex d)) (i : Fin d) (m n : ℤ) (x : Vertex d) (j : ℤ) :
    deriv (fun t ↦ finiteTwoPhaseSlabRowExpectation (q : ℝ) t U i m n x j) (p : ℝ) ≤
      ∑ e ∈ finiteTwoPhaseVariableMask U i m n,
        ((percolationProfile d (twoPhaseSlabProfile i m n p q)).real
            (finiteSlabConnectionEvent U i 0 n x e.val.1) *
          finiteTwoPhaseSlabRowMean p q U i m n (bondTip e.val) j +
        (percolationProfile d (twoPhaseSlabProfile i m n p q)).real
            (finiteSlabConnectionEvent U i 0 n x (bondTip e.val)) *
          finiteTwoPhaseSlabRowMean p q U i m n e.val.1 j) := by
  have hp : (p : ℝ) ≠ 1 := ne_of_lt (lt_of_le_of_lt hpP hP)
  rw [(finiteTwoPhaseSlabRowExpectation_russo (q : ℝ) (p : ℝ) hp U i m n x j).deriv,
    Finset.mul_sum]
  exact Finset.sum_le_sum (fun e he ↦
    finiteTwoPhaseSlab_row_opening_expectation_le p q P hP hpP hqP U i m n x j e he)

end NearCritical
