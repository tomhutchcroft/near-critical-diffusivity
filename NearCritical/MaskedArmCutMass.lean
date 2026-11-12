module

public import NearCritical.TwoPhaseSlabPlaneSums
public import NearCritical.MaskedWaterCubeSlabLaw
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

@[expose] public section
namespace NearCritical
open Set MeasureTheory
open scoped Classical ENNReal

/-- A finite normalized cut sum is bounded by the full plane mass under the
same two-phase law. The domain may be any subset of the slab. -/
theorem twoPhaseSlab_finite_cut_mass_le {d : ℕ} (i : Fin d) (p q : unitInterval)
    (m n j : ℤ) (x : Vertex d) (V : Finset (Vertex d))
    (hj : ∀ y ∈ V, y i = j) (S : Set (Vertex d)) (hS : S ⊆ finiteHeightSlab i 0 n) :
    (∑ y ∈ V, percolationProfile d (twoPhaseSlabProfile i m n p q)
      (connectionToSetEvent S x {y})) ≤ twoPhaseSlabPioneerMass i p q m n (x i) j := by
  rw [← twoPhaseSlab_plane_sum_forward i p q m n x j]
  calc
    _ ≤ ∑ y ∈ V, if y i = j then
          percolationProfile d (twoPhaseSlabProfile i m n p q)
            (connectionToSetEvent (finiteHeightSlab i 0 n) x {y}) else 0 := by
      apply Finset.sum_le_sum
      intro y hy
      rw [if_pos (hj y hy)]
      exact measure_mono (connectionToSetEvent_mono hS (Subset.refl _) x)
    _ ≤ _ := ENNReal.sum_le_tsum V

/-- After reindexing the physical cut by translation, its actual bulk-law
mass is bounded by the normalized full plane mass. -/
theorem maskedWaterCube_translated_cut_mass_le {d : ℕ} (i : Fin d)
    (r R : ℕ) (δ : ℝ) (p q : unitInterval) (a x : Vertex d)
    (ha : a i = -(r : ℤ)) (j : ℤ) (V : Finset (Vertex d))
    (hj : ∀ y ∈ V, y i = j) (S : Set (Vertex d))
    (hU : ∀ z ∈ S, a+z ∈ waterCube d i r R)
    (hS : S ⊆ finiteHeightSlab i 0
      ((2*r+1 : ℤ)-⌊δ*(2*(r : ℝ)+1)/2⌋-1)) :
    (∑ y ∈ V, bulkPercolation (waterCube d i r R) i (2*(r : ℝ)+1) δ p q
      (connectionToSetEvent ((fun z => a+z) '' S) (a+x) {a+y})) ≤
      twoPhaseSlabPioneerMass i p q ⌊δ*(2*(r : ℝ)+1)/2⌋
        ((2*r+1 : ℤ)-⌊δ*(2*(r : ℝ)+1)/2⌋-1) (x i) j := by
  have hlaw (y : Vertex d) := bulkPercolation_waterCube_connection_band_law
    i r R δ p q a ha S hU x {y}
  simp only [Set.image_singleton] at hlaw
  simp_rw [hlaw]
  exact twoPhaseSlab_finite_cut_mass_le i p q _ _ j x V hj S hS

end NearCritical
