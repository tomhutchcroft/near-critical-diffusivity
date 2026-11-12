module

public import NearCritical.FiniteSlabNearCriticalBootstrap
public import NearCritical.FiniteDomainExhaustion
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-! Actual cutoff exhaustion for the source slab mass. All infinite sums remain
ENNReal until an explicit finite upper bound has been proved. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Set MeasureTheory
open scoped Classical ENNReal

private lemma slab_tsum_iSup_monotone {d : ℕ} (f : ℕ → Vertex d → ℝ≥0∞)
    (hf : Monotone f) :
    (∑' y, ⨆ R, f R y) = ⨆ R, ∑' y, f R y := by
  have h := lintegral_iSup (μ := Measure.count)
    (fun R ↦ measurable_of_countable (f R)) hf
  simpa only [lintegral_count] using h

/-- The apparent finite endpoint sum is exactly an unrestricted ENNReal sum:
endpoints outside the cutoff have the ACTUAL confined event empty. -/
lemma finiteSlabRowMean_ofReal_eq_tsum {d : ℕ} (p : unitInterval)
    (U : Finset (Vertex d)) (i : Fin d) (m n : ℤ) (x : Vertex d) (j : ℤ) :
    ENNReal.ofReal (finiteSlabRowMean p U i m n x j) =
      ∑' y : Vertex d, if y i = j then
        percolation d p (finiteSlabConnectionEvent U i m n x y) else 0 := by
  rw [tsum_eq_sum (s := U) (fun y hy ↦ ?_)]
  · unfold finiteSlabRowMean
    rw [ENNReal.ofReal_sum_of_nonneg (fun y _ ↦ by split_ifs <;> positivity)]
    apply Finset.sum_congr rfl
    intro y hy
    by_cases hj : y i = j
    · simp only [ite_eq_left hj]
      exact ofReal_measureReal
    · simp only [ite_eq_right hj, ENNReal.ofReal_zero]
  · have hout : y ∉ finiteHeightSlab i m n ∩ (U : Set (Vertex d)) := fun h ↦ hy h.2
    rw [finiteSlabConnectionEvent_empty_of_end_outside U i m n x y hout]
    simp

/-- Exact actual finite-domain exhaustion AND plane-sum passage, with no
finite-mass premise. Nil paths are covered by the event exhaustion theorem. -/
theorem slab_plane_mass_eq_iSup_finiteSlabRows {d : ℕ} (p : unitInterval)
    (i : Fin d) (m n : ℤ) (x : Vertex d) (j : ℤ) :
    (∑' y : Vertex d, if y i = j then
      percolation d p (connectionToSetEvent (finiteHeightSlab i m n) x {y}) else 0) =
      ⨆ R : ℕ, ENNReal.ofReal (finiteSlabRowMean p (latticeSupCube d R) i m n x j) := by
  let f : ℕ → Vertex d → ℝ≥0∞ := fun R y ↦ if y i = j then
    percolation d p (finiteSlabConnectionEvent (latticeSupCube d R) i m n x y) else 0
  have hf : Monotone f := by
    intro R T hRT y
    dsimp [f]
    by_cases hy : y i = j
    · simp only [ite_eq_left hy]
      exact measure_mono (finiteDomain_connection_mono (finiteHeightSlab i m n) {y} x hRT)
    · simp only [ite_eq_right hy]
      exact le_rfl
  have he (y : Vertex d) :
      (if y i = j then percolation d p
        (connectionToSetEvent (finiteHeightSlab i m n) x {y}) else 0) = ⨆ R, f R y := by
    by_cases hy : y i = j
    · simp only [f, ite_eq_left hy]
      change _ = ⨆ R, percolation d p (connectionToSetEvent
        (finiteHeightSlab i m n ∩ (latticeSupCube d R : Set (Vertex d))) x {y})
      rw [connectionToSetEvent_eq_iUnion_finiteDomain,
        (finiteDomain_connection_mono (finiteHeightSlab i m n) {y} x).measure_iUnion]
    · simp [f, hy]
  simp_rw [he]
  rw [slab_tsum_iSup_monotone f hf]
  apply iSup_congr
  intro R
  exact (finiteSlabRowMean_ofReal_eq_tsum p (latticeSupCube d R) i m n x j).symm

/-- Exact exhaustion of the LITERAL source A_p(m,n;k,j). -/
theorem slabPioneerMass_eq_iSup_finiteSlabRows {d : ℕ} (p : unitInterval)
    (i : Fin d) (m n k j : ℤ) :
    slabPioneerMass p i m n k j =
      ⨆ R : ℕ, ENNReal.ofReal
        (finiteSlabRowMean p (latticeSupCube d R) i m n (Pi.single i k) j) :=
  slab_plane_mass_eq_iSup_finiteSlabRows p i m n (Pi.single i k) j

private lemma finiteSlabRowMean_zero_of_start_not_mem {d : ℕ} (p : unitInterval)
    (U : Finset (Vertex d)) (i : Fin d) (m n : ℤ) (x : Vertex d) (j : ℤ)
    (hx : x ∉ U) : finiteSlabRowMean p U i m n x j = 0 := by
  have hout : x ∉ finiteHeightSlab i m n ∩ (U : Set (Vertex d)) := fun h ↦ hx h.2
  have he (y : Vertex d) := finiteSlabConnectionEvent_empty_of_start_outside U i m n x y hout
  simp only [finiteSlabRowMean, he, measureReal_empty, ite_self, Finset.sum_const_zero]

/-- A finite-family bound passes to the ACTUAL infinite slab top-target mass.
The displayed finite-bound hypothesis is a generic limit-transfer interface;
the final theorem below supplies it from the proved near-critical bootstrap. -/
theorem slabPioneerMass_top_le_of_finite_max {d : ℕ} (p : unitInterval)
    (i : Fin d) (N : ℕ) (t k : ℤ) (ht : t ∈ Finset.Icc (0 : ℤ) (N : ℤ))
    {B : ℝ} (hB : 0 ≤ B)
    (hfinite : ∀ U : Finset (Vertex d), finiteSlabBoundaryMaximum (p : ℝ) U i 0 (N : ℤ) ≤ B) :
    slabPioneerMass p i 0 t k t ≤ ENNReal.ofReal B := by
  rw [slabPioneerMass_eq_iSup_finiteSlabRows]
  apply iSup_le
  intro R
  apply ENNReal.ofReal_le_ofReal
  by_cases hx : Pi.single i k ∈ latticeSupCube d R
  · exact (finiteSlabRowMean_le_boundaryMaximum p (latticeSupCube d R) i 0 (N : ℤ) t ht
      (Pi.single i k) hx).trans (hfinite _)
  · rw [finiteSlabRowMean_zero_of_start_not_mem p _ i 0 t (Pi.single i k) t hx]
    exact hB

/-- The entire actual slab mass is bounded via the PROVED infinite-slab
maximum-height convolution, not a derivative or stationarity of an infinite mass. -/
theorem slabPioneerMass_le_of_finite_max {d : ℕ} (p : unitInterval)
    (i : Fin d) (N : ℕ) (k j : ℤ)
    (hk : k ∈ Finset.Icc (0 : ℤ) (N : ℤ)) (_hj : j ∈ Finset.Icc (0 : ℤ) (N : ℤ))
    {B : ℝ} (hB : 0 ≤ B)
    (hfinite : ∀ U : Finset (Vertex d), finiteSlabBoundaryMaximum (p : ℝ) U i 0 (N : ℤ) ≤ B) :
    slabPioneerMass p i 0 (N : ℤ) k j ≤ ENNReal.ofReal ((N+1 : ℝ)*B^2) := by
  have hsub : Finset.Icc (max k j) (N : ℤ) ⊆ Finset.Icc (0 : ℤ) (N : ℤ) := by
    intro t ht
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hk).1.trans
      ((le_max_left _ _).trans (Finset.mem_Icc.mp ht).1), (Finset.mem_Icc.mp ht).2⟩
  have hcard : ((Finset.Icc (max k j) (N : ℤ)).card : ℝ) ≤ N+1 := by
    have hc : (Finset.Icc (0 : ℤ) (N : ℤ)).card = N+1 := by rw [Int.card_Icc]; omega
    exact_mod_cast (hc ▸ Finset.card_le_card hsub)
  calc
    _ ≤ ∑ t ∈ Finset.Icc (max k j) (N : ℤ),
        slabPioneerMass p i 0 t k t * slabPioneerMass p i 0 t j t :=
      slabPioneerMass_convolution p i 0 (N : ℤ) k j
    _ ≤ ∑ _t ∈ Finset.Icc (max k j) (N : ℤ), ENNReal.ofReal (B^2) := by
      apply Finset.sum_le_sum
      intro t ht
      have h1 := slabPioneerMass_top_le_of_finite_max p i N t k (hsub ht) hB hfinite
      have h2 := slabPioneerMass_top_le_of_finite_max p i N t j (hsub ht) hB hfinite
      exact (mul_le_mul' h1 h2).trans_eq (by rw [← ENNReal.ofReal_mul hB, pow_two])
    _ = ENNReal.ofReal (((Finset.Icc (max k j) (N : ℤ)).card : ℝ)*B^2) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      rw [ENNReal.ofReal_mul (by positivity)]
      simp
    _ ≤ _ := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hcard (sq_nonneg B))

/-- Literal source infinite slab upper estimate in a uniform near-critical
window, derived from cited weighted critical pioneer input and NEW proofs.
Constants are selected before all N,p,k,j; no infinite-mass bound is assumed. -/
theorem slabPioneerMass_nearCritical_upper_of_weighted {d : ℕ} (i : Fin d)
    {C c : ℝ} (hC : 0 < C) (hc : 0 < c) (hpc : 0 < (criticalPoint d : ℝ))
    (hpc1 : (criticalPoint d : ℝ) < 1)
    (decay : WeightedPositiveHeightPioneerDecay (criticalPoint d) i C c) :
    ∃ ε K : ℝ, 0 < ε ∧ 0 < K ∧ (criticalPoint d : ℝ)+ε < 1 ∧
      ∀ (N : ℕ) (p : unitInterval), (criticalPoint d : ℝ) ≤ (p : ℝ) →
        (p : ℝ) ≤ (criticalPoint d : ℝ)+ε/(N+1 : ℝ)^2 →
        (∀ t ∈ Finset.Icc (0 : ℤ) (N : ℤ), ∀ k : ℤ,
          slabPioneerMass p i 0 t k t ≤ ENNReal.ofReal (2*K)) ∧
        (∀ k ∈ Finset.Icc (0 : ℤ) (N : ℤ), ∀ j ∈ Finset.Icc (0 : ℤ) (N : ℤ),
          slabPioneerMass p i 0 (N : ℤ) k j ≤ ENNReal.ofReal ((N+1 : ℝ)*(2*K)^2)) := by
  obtain ⟨ε, K, hε, hK, hend, hbound⟩ :=
    finiteSlabBoundaryMaximum_nearCritical_uniform i hC hc hpc hpc1 decay
  refine ⟨ε, K, hε, hK, hend, ?_⟩
  intro N p hp hpwin
  have hfinite := fun U ↦ hbound U N p hp hpwin
  constructor
  · intro t ht k
    exact slabPioneerMass_top_le_of_finite_max p i N t k ht (by positivity) hfinite
  · intro k hk j hj
    exact slabPioneerMass_le_of_finite_max p i N k j hk hj (by positivity) hfinite

end NearCritical
