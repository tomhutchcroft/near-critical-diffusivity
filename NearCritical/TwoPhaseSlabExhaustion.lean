module

public import NearCritical.FiniteTwoPhaseSlabInitial
public import NearCritical.FiniteDomainExhaustion
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-! Actual mixed-law cutoff exhaustion, with the profile top fixed throughout.
All infinite sums stay in ENNReal; no infinite-volume derivative is taken. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Set MeasureTheory
open scoped Classical ENNReal

private lemma twoPhase_tsum_iSup_monotone {d : ℕ} (f : ℕ → Vertex d → ℝ≥0∞)
    (hf : Monotone f) :
    (∑' y, ⨆ R, f R y) = ⨆ R, ∑' y, f R y := by
  have h := lintegral_iSup (μ := Measure.count)
    (fun R ↦ measurable_of_countable (f R)) hf
  simpa only [lintegral_count] using h

theorem twoPhaseSlab_plane_mass_eq_iSup_finiteRows {d : ℕ} (p q : unitInterval)
    (i : Fin d) (m n : ℤ) (x : Vertex d) (j : ℤ) :
    (∑' y : Vertex d, if y i = j then
      percolationProfile d (twoPhaseSlabProfile i m n p q)
        (connectionToSetEvent (finiteHeightSlab i 0 n) x {y}) else 0) =
      ⨆ R : ℕ, ENNReal.ofReal
        (finiteTwoPhaseSlabRowMean p q (latticeSupCube d R) i m n x j) := by
  let μ := percolationProfile d (twoPhaseSlabProfile i m n p q)
  let f : ℕ → Vertex d → ℝ≥0∞ := fun R y ↦ if y i = j then
    μ (finiteSlabConnectionEvent (latticeSupCube d R) i 0 n x y) else 0
  have hf : Monotone f := by
    intro R T hRT y
    dsimp [f]
    by_cases hy : y i = j
    · simp only [ite_eq_left hy]
      exact measure_mono (finiteDomain_connection_mono (finiteHeightSlab i 0 n) {y} x hRT)
    · simp only [ite_eq_right hy]
      exact le_rfl
  have he (y : Vertex d) :
      (if y i = j then μ
        (connectionToSetEvent (finiteHeightSlab i 0 n) x {y}) else 0) = ⨆ R, f R y := by
    by_cases hy : y i = j
    · simp only [f,ite_eq_left hy]
      change _ = ⨆ R, μ (connectionToSetEvent
        (finiteHeightSlab i 0 n ∩ (latticeSupCube d R : Set (Vertex d))) x {y})
      rw [connectionToSetEvent_eq_iUnion_finiteDomain,
        (finiteDomain_connection_mono (finiteHeightSlab i 0 n) {y} x).measure_iUnion]
    · simp [f,hy]
  change (∑' y, if y i = j then μ
    (connectionToSetEvent (finiteHeightSlab i 0 n) x {y}) else 0) = _
  simp_rw [he]
  rw [twoPhase_tsum_iSup_monotone f hf]
  apply iSup_congr
  intro R
  exact (finiteTwoPhaseSlabRowMean_ofReal_eq_tsum p q (latticeSupCube d R) i m n x j).symm

theorem twoPhaseSlabPioneerMass_eq_iSup_finiteRows {d : ℕ} (p q : unitInterval)
    (i : Fin d) (m n k j : ℤ) :
    twoPhaseSlabPioneerMass i p q m n k j =
      ⨆ R : ℕ, ENNReal.ofReal
        (finiteTwoPhaseSlabRowMean p q (latticeSupCube d R) i m n (Pi.single i k) j) := by
  have h := twoPhaseSlab_plane_mass_eq_iSup_finiteRows p q i m n (Pi.single i k) j
  rw [twoPhaseSlab_plane_sum_forward] at h
  simpa only [Pi.single_eq_same] using h

/-- Generic limit-transfer interface only. The finite bound must still be
supplied by the actual weighted bootstrap; it is not a new standard input. -/
theorem twoPhaseSlabPioneerMass_top_le_of_finite_weighted_max {d : ℕ}
    (p q : unitInterval) (c : ℝ) (i : Fin d) (m : ℤ) (N : ℕ) (t k : ℤ)
    (ht : t ∈ Finset.Icc (0 : ℤ) (N : ℤ)) {B : ℝ} (hB : 0 ≤ B)
    (hfinite : ∀ U : Finset (Vertex d),
      finiteTwoPhaseBoundaryMaximum q c (p : ℝ) U i m N ≤ B) :
    twoPhaseSlabPioneerMass i p q m t k t ≤ ENNReal.ofReal
      (B*Real.exp (-(c*Real.sqrt ((criticalPoint d : ℝ)-(q : ℝ))*
        twoPhaseSlabDistance m k t))) := by
  rw [twoPhaseSlabPioneerMass_eq_iSup_finiteRows]
  apply iSup_le
  intro R
  apply ENNReal.ofReal_le_ofReal
  let x : Vertex d := Pi.single i k
  let w : ℝ := c*Real.sqrt ((criticalPoint d : ℝ)-(q : ℝ))*twoPhaseSlabDistance m k t
  by_cases hx : x ∈ latticeSupCube d R
  · have h := (finiteTwoPhase_forward_row_le_boundaryMaximum p q c
      (latticeSupCube d R) i m N t ht x hx).trans (hfinite _)
    have h' : Real.exp w * finiteTwoPhaseSlabRowMean p q (latticeSupCube d R) i m t x t ≤ B := by
      simpa only [x,Pi.single_eq_same] using h
    calc
      _ = (Real.exp w*finiteTwoPhaseSlabRowMean p q (latticeSupCube d R) i m t x t)*
          Real.exp (-w) := by
        rw [mul_right_comm,← Real.exp_add,add_neg_cancel,Real.exp_zero,one_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right h' (Real.exp_nonneg _)
  · have hout : x ∉ finiteHeightSlab i 0 t ∩ (latticeSupCube d R : Set (Vertex d)) :=
      fun h ↦ hx h.2
    rw [finiteTwoPhaseSlabRowMean_zero_of_start_outside p q _ i m t x t hout]
    exact mul_nonneg hB (Real.exp_nonneg _)

end NearCritical
