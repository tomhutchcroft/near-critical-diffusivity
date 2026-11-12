module

public import NearCritical.RestrictedSusceptibility
public import NearCritical.SlabPioneerExhaustion

/-! Actual finite-height slab susceptibility and nonpercolation in the proved
near-critical window. Only the cited critical weighted pioneer input remains;
the zero infinite-cluster event is derived by the actual first moment. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Set MeasureTheory
open scoped Classical ENNReal

/-- A slab's total actual connection mass is the FINITE sum of its actual plane
masses. Endpoints outside the slab have empty domain-checked connection events. -/
theorem restrictedConnectionMass_slab_eq_sum {d : ℕ} (p : unitInterval)
    (i : Fin d) (m n k : ℤ) :
    restrictedConnectionMass (percolation d p) (finiteHeightSlab i m n) (Pi.single i k) =
      ∑ j ∈ Finset.Icc m n, slabPioneerMass p i m n k j := by
  have heq : restrictedConnectionMass (percolation d p) (finiteHeightSlab i m n) (Pi.single i k) =
      ∑' y : Vertex d, if m ≤ y i ∧ y i ≤ n then
        percolation d p (connectionToSetEvent (finiteHeightSlab i m n) (Pi.single i k) {y}) else 0 := by
    unfold restrictedConnectionMass
    apply tsum_congr
    intro y
    by_cases hy : m ≤ y i ∧ y i ≤ n
    · simp only [ite_eq_left hy]
    · have hempty : connectionToSetEvent (finiteHeightSlab i m n) (Pi.single i k) {y} = ∅ := by
        ext ω
        constructor
        · rintro ⟨_,z,hz,hzS,_⟩
          have hzy : z = y := hz
          subst z
          exact hy hzS
        · intro h
          exact False.elim h
      simp only [ite_eq_right hy, hempty, measure_empty]
  rw [heq, tsum_height_interval]
  rfl

/-- Any finite upper bound on the origin-to-plane masses gives a genuine finite
ENNReal susceptibility bound, with the actual N+1 planes counted. -/
theorem slab_restrictedConnectionMass_le_of_plane_bound {d : ℕ} (p : unitInterval)
    (i : Fin d) (N : ℕ) (B : ℝ) (_hB : 0 ≤ B)
    (hplane : ∀ j ∈ Finset.Icc (0 : ℤ) (N : ℤ),
      slabPioneerMass p i 0 (N : ℤ) 0 j ≤ ENNReal.ofReal B) :
    restrictedConnectionMass (percolation d p) (finiteHeightSlab i 0 (N : ℤ)) 0 ≤
      ENNReal.ofReal ((N+1 : ℝ)*B) := by
  have hcard : (Finset.Icc (0 : ℤ) (N : ℤ)).card = N+1 := by rw [Int.card_Icc]; omega
  calc
    _ = ∑ j ∈ Finset.Icc (0 : ℤ) (N : ℤ), slabPioneerMass p i 0 (N : ℤ) 0 j := by
      simpa only [Pi.single_zero] using restrictedConnectionMass_slab_eq_sum p i 0 (N : ℤ) 0
    _ ≤ ∑ _j ∈ Finset.Icc (0 : ℤ) (N : ℤ), ENNReal.ofReal B :=
      Finset.sum_le_sum hplane
    _ = ENNReal.ofReal (((Finset.Icc (0 : ℤ) (N : ℤ)).card : ℝ)*B) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      rw [ENNReal.ofReal_mul (by positivity)]
      congr 1
      exact (ENNReal.ofReal_natCast _).symm
    _ = _ := by rw [hcard]; simp

/-- Actual no-infinite-cluster probability follows from finite first moment,
not from an assumed nonpercolation or critical-point conclusion. -/
theorem slab_restrictedInfiniteEvent_measure_zero_of_plane_bound {d : ℕ}
    (p : unitInterval) (i : Fin d) (N : ℕ) (B : ℝ) (hB : 0 ≤ B)
    (hplane : ∀ j ∈ Finset.Icc (0 : ℤ) (N : ℤ),
      slabPioneerMass p i 0 (N : ℤ) 0 j ≤ ENNReal.ofReal B) :
    percolation d p (restrictedInfiniteEvent d (finiteHeightSlab i 0 (N : ℤ))) = 0 := by
  apply restrictedInfiniteEvent_measure_zero_of_connectionMass_ne_top
    (percolation d p) (finiteHeightSlab i 0 (N : ℤ)) (by simp [finiteHeightSlab])
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (slab_restrictedConnectionMass_le_of_plane_bound p i N B hB hplane)

theorem slab_restrictedDensity_zero_of_plane_bound {d : ℕ}
    (p : unitInterval) (i : Fin d) (N : ℕ) (B : ℝ) (hB : 0 ≤ B)
    (hplane : ∀ j ∈ Finset.Icc (0 : ℤ) (N : ℤ),
      slabPioneerMass p i 0 (N : ℤ) 0 j ≤ ENNReal.ofReal B) :
    restrictedDensity d (finiteHeightSlab i 0 (N : ℤ)) p = 0 := by
  simp only [restrictedDensity, measureReal_def,
    slab_restrictedInfiniteEvent_measure_zero_of_plane_bound p i N B hB hplane,
    ENNReal.toReal_zero]

/-- Genuine nonpercolation throughout the uniform near-critical slab window,
derived from the PROVED actual infinite slab mass bound and first moment.
Only the named STANDARD critical weighted pioneer decay and 0<pc<1 remain. -/
theorem slab_restrictedInfiniteEvent_nearCritical_zero_of_weighted {d : ℕ} (i : Fin d)
    {C c : ℝ} (hC : 0 < C) (hc : 0 < c) (hpc : 0 < (criticalPoint d : ℝ))
    (hpc1 : (criticalPoint d : ℝ) < 1)
    (decay : WeightedPositiveHeightPioneerDecay (criticalPoint d) i C c) :
    ∃ ε K : ℝ, 0 < ε ∧ 0 < K ∧ (criticalPoint d : ℝ)+ε < 1 ∧
      ∀ (N : ℕ) (p : unitInterval), (criticalPoint d : ℝ) ≤ (p : ℝ) →
        (p : ℝ) ≤ (criticalPoint d : ℝ)+ε/(N+1 : ℝ)^2 →
        restrictedConnectionMass (percolation d p) (finiteHeightSlab i 0 (N : ℤ)) 0 ≤
          ENNReal.ofReal ((N+1 : ℝ)^2*(2*K)^2) ∧
        percolation d p (restrictedInfiniteEvent d (finiteHeightSlab i 0 (N : ℤ))) = 0 ∧
        restrictedDensity d (finiteHeightSlab i 0 (N : ℤ)) p = 0 := by
  obtain ⟨ε,K,hε,hK,hend,hbound⟩ :=
    slabPioneerMass_nearCritical_upper_of_weighted i hC hc hpc hpc1 decay
  refine ⟨ε,K,hε,hK,hend,?_⟩
  intro N p hp hpwin
  have hzero : (0 : ℤ) ∈ Finset.Icc (0 : ℤ) (N : ℤ) := by simp
  have hplane := fun j hj ↦ (hbound N p hp hpwin).2 0 hzero j hj
  have hB : 0 ≤ (N+1 : ℝ)*(2*K)^2 := by positivity
  have hm := slab_restrictedConnectionMass_le_of_plane_bound p i N _ hB hplane
  refine ⟨?_, slab_restrictedInfiniteEvent_measure_zero_of_plane_bound p i N _ hB hplane,
    slab_restrictedDensity_zero_of_plane_bound p i N _ hB hplane⟩
  have heq : (N+1 : ℝ)*((N+1 : ℝ)*(2*K)^2) = (N+1 : ℝ)^2*(2*K)^2 := by ring
  simpa only [heq] using hm

end NearCritical
