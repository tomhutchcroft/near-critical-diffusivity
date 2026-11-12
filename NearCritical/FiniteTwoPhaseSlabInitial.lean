module

public import NearCritical.FiniteTwoPhaseSlabBoundaryFamily
public import NearCritical.TwoPhaseSlabPlaneSums
public import NearCritical.TwoPhaseCriticalInitial

/-! Actual finite-cutoff domination and the critical starting estimate for the
mixed weighted bootstrap. No stationarity of a fixed finite cutoff is used. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Set MeasureTheory
open scoped Classical ENNReal

lemma finiteTwoPhaseSlabRowMean_ofReal_eq_tsum {d : ℕ} (p q : unitInterval)
    (U : Finset (Vertex d)) (i : Fin d) (m n : ℤ) (x : Vertex d) (j : ℤ) :
    ENNReal.ofReal (finiteTwoPhaseSlabRowMean p q U i m n x j) =
      ∑' y : Vertex d, if y i = j then
        percolationProfile d (twoPhaseSlabProfile i m n p q)
          (finiteSlabConnectionEvent U i 0 n x y) else 0 := by
  rw [tsum_eq_sum (s := U) (fun y hy ↦ ?_)]
  · unfold finiteTwoPhaseSlabRowMean
    rw [ENNReal.ofReal_sum_of_nonneg (fun y _ ↦ by split_ifs <;> positivity)]
    apply Finset.sum_congr rfl
    intro y hy
    by_cases hj : y i = j
    · simp only [ite_eq_left hj]
      exact ofReal_measureReal
    · simp only [ite_eq_right hj, ENNReal.ofReal_zero]
  · have hout : y ∉ finiteHeightSlab i 0 n ∩ (U : Set (Vertex d)) := fun h ↦ hy h.2
    rw [finiteSlabConnectionEvent_empty_of_end_outside U i 0 n x y hout]
    simp

lemma finiteTwoPhaseSlabRowMean_ofReal_le_mass {d : ℕ} (p q : unitInterval)
    (U : Finset (Vertex d)) (i : Fin d) (m n : ℤ) (x : Vertex d) (j : ℤ) :
    ENNReal.ofReal (finiteTwoPhaseSlabRowMean p q U i m n x j) ≤
      twoPhaseSlabPioneerMass i p q m n (x i) j := by
  rw [finiteTwoPhaseSlabRowMean_ofReal_eq_tsum,
    ← twoPhaseSlab_plane_sum_forward i p q m n x j]
  apply ENNReal.tsum_le_tsum
  intro y
  by_cases hy : y i = j
  · simp only [ite_eq_left hy]
    apply measure_mono
    exact connectionToSetEvent_mono (fun _ h ↦ h.1) (Subset.refl _) x
  · simp only [ite_eq_right hy,le_refl]

lemma finiteTwoPhaseSlabRowMean_le_of_mass_le {d : ℕ} (p q : unitInterval)
    (U : Finset (Vertex d)) (i : Fin d) (m n : ℤ) (x : Vertex d) (j : ℤ)
    {A : ℝ} (hA : 0 ≤ A)
    (h : twoPhaseSlabPioneerMass i p q m n (x i) j ≤ ENNReal.ofReal A) :
    finiteTwoPhaseSlabRowMean p q U i m n x j ≤ A := by
  exact (ENNReal.ofReal_le_ofReal_iff hA).mp
    ((finiteTwoPhaseSlabRowMean_ofReal_le_mass p q U i m n x j).trans h)

lemma finiteTwoPhaseSlabRowMean_zero_of_start_outside {d : ℕ} (p q : unitInterval)
    (U : Finset (Vertex d)) (i : Fin d) (m n : ℤ) (x : Vertex d) (j : ℤ)
    (hx : x ∉ finiteHeightSlab i 0 n ∩ (U : Set (Vertex d))) :
    finiteTwoPhaseSlabRowMean p q U i m n x j = 0 := by
  have he (y : Vertex d) := finiteSlabConnectionEvent_empty_of_start_outside U i 0 n x y hx
  simp only [finiteTwoPhaseSlabRowMean,he,measureReal_empty,ite_self,Finset.sum_const_zero]

/-- The source critical estimate transfers to both actual finite boundary
orientations, with one amplitude and rate before every cutoff and height. -/
theorem finiteTwoPhaseSlab_critical_boundary_initial {d : ℕ} (i : Fin d)
    {B b : ℝ} (hB : 0 < B) (hb : 0 < b) (hpc : 0 < (criticalPoint d : ℝ))
    (pioneers : HalfSpacePioneerExponentialInput i B b) :
    ∃ M c : ℝ, 0 < M ∧ 0 < c ∧ ∀ (U : Finset (Vertex d)) (m k j : ℕ),
      k ≤ j → ∀ (q : unitInterval), q ≤ criticalPoint d →
      (∀ x : Vertex d, x i = (k : ℤ) →
        finiteTwoPhaseSlabRowMean (criticalPoint d) q U i m j x j ≤
          M*Real.exp (-c*Real.sqrt ((criticalPoint d : ℝ)-(q : ℝ))*
            twoPhaseSlabDistance m k j)) ∧
      (∀ z : Vertex d, z i = (j : ℤ) →
        finiteTwoPhaseSlabRowMean (criticalPoint d) q U i m j z k ≤
          M*Real.exp (-c*Real.sqrt ((criticalPoint d : ℝ)-(q : ℝ))*
            twoPhaseSlabDistance m k j)) := by
  obtain ⟨M,c,hM,hc,hbound⟩ :=
    twoPhaseSlabPioneerMass_critical_initial_exponential i hB hb hpc pioneers
  refine ⟨M,c,hM,hc,?_⟩
  intro U m k j hkj q hq
  have h := hbound m k j hkj q hq
  constructor
  · intro x hx
    apply finiteTwoPhaseSlabRowMean_le_of_mass_le _ _ _ _ _ _ _ _ (by positivity)
    simpa only [hx] using h
  · intro z hz
    apply finiteTwoPhaseSlabRowMean_le_of_mass_le _ _ _ _ _ _ _ _ (by positivity)
    rw [hz,twoPhaseSlabPioneerMass_symm]
    exact h

end NearCritical
