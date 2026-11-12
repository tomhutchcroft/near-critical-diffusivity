module

public import NearCritical.SlabPioneerExhaustion

/-! Actual whole-plane canonicalization and arbitrary finite-cutoff domination.
No translation invariance of a fixed cutoff is asserted. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Set MeasureTheory
open scoped ENNReal

/-- A whole-plane row from an arbitrary source is exactly the canonical slab
mass at the source height. Uses actual infinite-law endpoint symmetries. -/
lemma slab_plane_mass_eq_canonical {d : ℕ} (p : unitInterval) (i : Fin d)
    (m n : ℤ) (x : Vertex d) (j : ℤ) :
    (∑' y : Vertex d, if y i = j then
      percolation d p (connectionToSetEvent (finiteHeightSlab i m n) x {y}) else 0) =
      slabPioneerMass p i m n (x i) j := by
  calc
    _ = ∑' y : Vertex d, if y i = j then
        percolation d p (connectionToSetEvent (finiteHeightSlab i m n) y {x}) else 0 := by
      apply tsum_congr
      intro y
      rw [connectionToSetEvent_singleton_symm]
    _ = slabPioneerMass p i m n j (x i) := slab_plane_sum_reverse p i m n j x
    _ = _ := slabPioneerMass_symm p i m n j (x i)

/-- Every arbitrary finite-cutoff row is dominated by the actual whole-plane
mass. This is domain inclusion, not finite-cutoff stationarity. -/
lemma finiteSlabRowMean_ofReal_le_slabPioneerMass {d : ℕ} (p : unitInterval)
    (U : Finset (Vertex d)) (i : Fin d) (m n : ℤ) (x : Vertex d) (j : ℤ) :
    ENNReal.ofReal (finiteSlabRowMean p U i m n x j) ≤
      slabPioneerMass p i m n (x i) j := by
  rw [finiteSlabRowMean_ofReal_eq_tsum,← slab_plane_mass_eq_canonical p i m n x j]
  apply ENNReal.tsum_le_tsum
  intro y
  by_cases hy : y i = j
  · simp only [ite_eq_left hy]
    apply measure_mono
    exact connectionToSetEvent_mono (fun _ h ↦ h.1) (Subset.refl _) x
  · simp only [ite_eq_right hy,le_refl]

/-- A finite REAL row inherits an explicit nonnegative actual ENNReal mass
bound, without applying toReal to an unproved-finite slab mass. -/
lemma finiteSlabRowMean_le_of_slabPioneerMass_le {d : ℕ} (p : unitInterval)
    (U : Finset (Vertex d)) (i : Fin d) (m n : ℤ) (x : Vertex d) (j : ℤ)
    {B : ℝ} (hB : 0 ≤ B)
    (h : slabPioneerMass p i m n (x i) j ≤ ENNReal.ofReal B) :
    finiteSlabRowMean p U i m n x j ≤ B := by
  exact (ENNReal.ofReal_le_ofReal_iff hB).mp
    ((finiteSlabRowMean_ofReal_le_slabPioneerMass p U i m n x j).trans h)

end NearCritical
