module

public import NearCritical.SlabPioneerExhaustion
public import NearCritical.BulkSupercriticalBound

/-! Actual independent-profile slab masses. Polynomial near-critical control
follows from a proved coupling, without inhomogeneous BK or stationarity. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory
open scoped ENNReal

def profileSlabPioneerMass {d : ℕ} (r : Bond d → unitInterval) (i : Fin d)
    (m n k j : ℤ) : ℝ≥0∞ :=
  ∑' u : Vertex d, if u i = j then
    percolationProfile d r
      (connectionToSetEvent (finiteHeightSlab i m n) (Pi.single i k) {u}) else 0

lemma profileSlabPioneerMass_const {d : ℕ} (p : unitInterval) (i : Fin d)
    (m n k j : ℤ) :
    profileSlabPioneerMass (fun _ : Bond d => p) i m n k j = slabPioneerMass p i m n k j := by
  simp only [profileSlabPioneerMass,slabPioneerMass,percolationProfile_const]

theorem profileSlabPioneerMass_le_homogeneous {d : ℕ} (r : Bond d → unitInterval)
    (p : unitInterval) (hr : ∀ e, (r e : ℝ) ≤ (p : ℝ)) (i : Fin d)
    (m n k j : ℤ) :
    profileSlabPioneerMass r i m n k j ≤ slabPioneerMass p i m n k j := by
  apply ENNReal.tsum_le_tsum
  intro u
  split_ifs
  · exact percolationProfile_event_le_homogeneous r p hr
      (measurableSet_connectionToSetEvent _ _ _) (connectionToSetEvent_increasing _ _ _)
  · exact le_rfl

/-- One pair of constants before all cutoffs, parameters and rate profiles.
The final actual profile bounds have no desired probability-bound premise. -/
theorem profileSlabPioneerMass_nearCritical_upper_of_weighted {d : ℕ} (i : Fin d)
    {C c : ℝ} (hC : 0 < C) (hc : 0 < c) (hpc : 0 < (criticalPoint d : ℝ))
    (hpc1 : (criticalPoint d : ℝ) < 1)
    (decay : WeightedPositiveHeightPioneerDecay (criticalPoint d) i C c) :
    ∃ ε K : ℝ, 0 < ε ∧ 0 < K ∧ (criticalPoint d : ℝ)+ε < 1 ∧
      ∀ (N : ℕ) (p : unitInterval) (r : Bond d → unitInterval),
        (criticalPoint d : ℝ) ≤ (p : ℝ) →
        (p : ℝ) ≤ (criticalPoint d : ℝ)+ε/(N+1 : ℝ)^2 →
        (∀ e, (r e : ℝ) ≤ (p : ℝ)) →
        (∀ t ∈ Finset.Icc (0 : ℤ) (N : ℤ), ∀ k : ℤ,
          profileSlabPioneerMass r i 0 t k t ≤ ENNReal.ofReal (2*K)) ∧
        (∀ k ∈ Finset.Icc (0 : ℤ) (N : ℤ), ∀ j ∈ Finset.Icc (0 : ℤ) (N : ℤ),
          profileSlabPioneerMass r i 0 (N : ℤ) k j ≤
            ENNReal.ofReal ((N+1 : ℝ)*(2*K)^2)) := by
  obtain ⟨ε,K,hε,hK,hend,hbound⟩ :=
    slabPioneerMass_nearCritical_upper_of_weighted i hC hc hpc hpc1 decay
  refine ⟨ε,K,hε,hK,hend,?_⟩
  intro N p r hp hw hr
  obtain ⟨htop,hwhole⟩ := hbound N p hp hw
  constructor
  · intro t ht k
    exact (profileSlabPioneerMass_le_homogeneous r p hr i 0 t k t).trans (htop t ht k)
  · intro k hk j hj
    exact (profileSlabPioneerMass_le_homogeneous r p hr i 0 N k j).trans (hwhole k hk j hj)

end NearCritical
