module

public import NearCritical.SlabPioneerReflection
public import NearCritical.SlabPioneerExhaustion
public import NearCritical.PercolationMonotonicity

/-! Boundary-distance refinement of the NEW homogeneous near-critical slab
bound. No half-slab 1/(n+1) prefactor or exponential refinement is assumed. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Finset MeasureTheory
open scoped ENNReal

lemma slabPioneerMass_mono_parameter {d : ℕ} {p q : unitInterval} (hpq : p ≤ q)
    (i : Fin d) (m n k j : ℤ) :
    slabPioneerMass p i m n k j ≤ slabPioneerMass q i m n k j := by
  apply ENNReal.tsum_le_tsum
  intro u
  split_ifs
  · exact percolation_increasing_event_mono (measurableSet_connectionToSetEvent _ _ _)
      (connectionToSetEvent_increasing _ _ _) hpq
  · exact le_rfl

def slabBoundaryDistance (N : ℕ) (k j : ℤ) : ℝ :=
  min (min (((N : ℤ)+1-k : ℤ) : ℝ) (((N : ℤ)+1-j : ℤ) : ℝ))
    (min ((k+1 : ℤ) : ℝ) ((j+1 : ℤ) : ℝ))

lemma slabPioneerMass_le_upper_boundary_count {d : ℕ} (p : unitInterval) (i : Fin d)
    (N : ℕ) (k j : ℤ) (hk : k ∈ Icc (0 : ℤ) (N : ℤ))
    (hj : j ∈ Icc (0 : ℤ) (N : ℤ)) {B : ℝ} (hB : 0 ≤ B)
    (htop : ∀ t ∈ Icc (0 : ℤ) (N : ℤ), ∀ a : ℤ,
      slabPioneerMass p i 0 t a t ≤ ENNReal.ofReal B) :
    slabPioneerMass p i 0 N k j ≤ ENNReal.ofReal
      ((((N : ℤ)+1-max k j : ℤ) : ℝ)*B^2) := by
  have hsub : Icc (max k j) (N : ℤ) ⊆ Icc (0 : ℤ) (N : ℤ) := by
    intro t ht
    have h := mem_Icc.mp ht
    have hk0 := (mem_Icc.mp hk).1
    exact mem_Icc.mpr ⟨by omega,h.2⟩
  have hcardZ : ((Icc (max k j) (N : ℤ)).card : ℤ) = (N : ℤ)+1-max k j := by
    rw [Int.card_Icc,Int.toNat_of_nonneg]
    have hku := (mem_Icc.mp hk).2
    have hju := (mem_Icc.mp hj).2
    omega
  have hcard : ((Icc (max k j) (N : ℤ)).card : ℝ) =
      (((N : ℤ)+1-max k j : ℤ) : ℝ) := by exact_mod_cast hcardZ
  calc
    _ ≤ ∑ t ∈ Icc (max k j) (N : ℤ),
        slabPioneerMass p i 0 t k t * slabPioneerMass p i 0 t j t :=
      slabPioneerMass_convolution p i 0 N k j
    _ ≤ ∑ _t ∈ Icc (max k j) (N : ℤ), ENNReal.ofReal (B^2) := by
      apply sum_le_sum
      intro t ht
      exact (mul_le_mul' (htop t (hsub ht) k) (htop t (hsub ht) j)).trans_eq
        (by rw [← ENNReal.ofReal_mul hB,pow_two])
    _ = ENNReal.ofReal (((Icc (max k j) (N : ℤ)).card : ℝ)*B^2) := by
      simp only [sum_const,nsmul_eq_mul]
      rw [ENNReal.ofReal_mul (by positivity)]
      simp
    _ = _ := by rw [hcard]

theorem slabPioneerMass_le_boundary_distance {d : ℕ} (p : unitInterval) (i : Fin d)
    (N : ℕ) (k j : ℤ) (hk : k ∈ Icc (0 : ℤ) (N : ℤ))
    (hj : j ∈ Icc (0 : ℤ) (N : ℤ)) {B : ℝ} (hB : 0 ≤ B)
    (htop : ∀ t ∈ Icc (0 : ℤ) (N : ℤ), ∀ a : ℤ,
      slabPioneerMass p i 0 t a t ≤ ENNReal.ofReal B) :
    slabPioneerMass p i 0 N k j ≤ ENNReal.ofReal (slabBoundaryDistance N k j*B^2) := by
  have hraw := slabPioneerMass_le_upper_boundary_count p i N k j hk hj hB htop
  have hkr : (N : ℤ)-k ∈ Icc (0 : ℤ) (N : ℤ) := by
    have h := mem_Icc.mp hk
    exact mem_Icc.mpr ⟨by omega,by omega⟩
  have hjr : (N : ℤ)-j ∈ Icc (0 : ℤ) (N : ℤ) := by
    have h := mem_Icc.mp hj
    exact mem_Icc.mpr ⟨by omega,by omega⟩
  have href := slabPioneerMass_le_upper_boundary_count p i N _ _ hkr hjr hB htop
  have hid : slabPioneerMass p i 0 N ((N : ℤ)-k) ((N : ℤ)-j) =
      slabPioneerMass p i 0 N k j := by
    simpa only [zero_add] using slabPioneerMass_reflection p i 0 N k j
  rw [hid] at href
  have hreal (a b : ℤ) (hab : a ≤ b) : (a : ℝ)*B^2 ≤ (b : ℝ)*B^2 :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hab) (sq_nonneg B)
  have h1 := hraw.trans (ENNReal.ofReal_le_ofReal (hreal _ ((N : ℤ)+1-k) (by omega)))
  have h2 := hraw.trans (ENNReal.ofReal_le_ofReal (hreal _ ((N : ℤ)+1-j) (by omega)))
  have h3 := href.trans (ENNReal.ofReal_le_ofReal (hreal _ (k+1) (by omega)))
  have h4 := href.trans (ENNReal.ofReal_le_ofReal (hreal _ (j+1) (by omega)))
  have h := le_min (le_min h1 h2) (le_min h3 h4)
  simpa only [slabBoundaryDistance,min_mul_of_nonneg _ _ (sq_nonneg B),ENNReal.ofReal_min] using h

/-- The genuine four-boundary-distance estimate in the near-critical window.
Subcritical parameters are included by actual parameter monotonicity. -/
theorem slabPioneerMass_nearCritical_boundary_bound {d : ℕ} (i : Fin d)
    {C c : ℝ} (hC : 0 < C) (hc : 0 < c) (hpc : 0 < (criticalPoint d : ℝ))
    (hpc1 : (criticalPoint d : ℝ) < 1)
    (decay : WeightedPositiveHeightPioneerDecay (criticalPoint d) i C c) :
    ∃ ε D : ℝ, 0 < ε ∧ 0 < D ∧ (criticalPoint d : ℝ)+ε < 1 ∧
      ∀ (N : ℕ) (p : unitInterval),
        (p : ℝ) ≤ (criticalPoint d : ℝ)+ε/(N+1 : ℝ)^2 →
        ∀ k ∈ Icc (0 : ℤ) (N : ℤ), ∀ j ∈ Icc (0 : ℤ) (N : ℤ),
          slabPioneerMass p i 0 N k j ≤ ENNReal.ofReal (slabBoundaryDistance N k j*D) := by
  obtain ⟨ε,K,hε,hK,hend,hbound⟩ :=
    slabPioneerMass_nearCritical_upper_of_weighted i hC hc hpc hpc1 decay
  refine ⟨ε,(2*K)^2,hε,by positivity,hend,?_⟩
  intro N p hp k hk j hj
  by_cases hcrit : criticalPoint d ≤ p
  · exact slabPioneerMass_le_boundary_distance p i N k j hk hj (by positivity)
      (hbound N p hcrit hp).1
  · have hle : p ≤ criticalPoint d := le_of_lt (lt_of_not_ge hcrit)
    have hwindow : (criticalPoint d : ℝ) ≤
        (criticalPoint d : ℝ)+ε/(N+1 : ℝ)^2 :=
      le_add_of_nonneg_right (div_nonneg hε.le (sq_nonneg _))
    exact (slabPioneerMass_mono_parameter hle i 0 N k j).trans
      (slabPioneerMass_le_boundary_distance (criticalPoint d) i N k j hk hj (by positivity)
        (hbound N (criticalPoint d) le_rfl hwindow).1)

end NearCritical
