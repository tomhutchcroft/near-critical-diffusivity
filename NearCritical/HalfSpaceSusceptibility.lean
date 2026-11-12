module

public import NearCritical.HalfSpaceInteriorReduction

/-! The actual boundary susceptibility/pioneer identity used in the paper's
new half-space susceptibility argument. No quantitative estimate is assumed. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Set MeasureTheory
open scoped Classical ENNReal

/-- An actual domain-checked connection to an outside endpoint is impossible. -/
lemma halfSpace_connection_empty_of_negative_height {d : ℕ} (i : Fin d)
    (x y : Vertex d) (hy : y i < 0) :
    connectionToSetEvent {z | 0 ≤ z i} x {y} = ∅ := by
  ext ω
  constructor
  · rintro ⟨_, z, hz, hzS, _⟩
    have hzy : z = y := hz
    subst z
    change 0 ≤ y i at hzS
    exact (not_le_of_gt hy) hzS
  · simp

/-- Source's susceptibility identity, proved for the actual full-lattice law.
The nonnegative sum includes m=0 but assumes no quantitative bound there. -/
theorem halfSpace_susceptibility_eq_tsum_pioneers {d : ℕ} (p : unitInterval)
    (i : Fin d) :
    halfSpaceSusceptibility p i 0 =
      ∑' m : ℕ, halfSpacePioneerMass p i (m : ℤ) := by
  calc
    _ = ∑' y : Vertex d, ∑' m : ℕ, if y i = (m : ℤ) then
        percolation d p (connectionToSetEvent {z | 0 ≤ z i} 0 {y}) else 0 := by
      apply tsum_congr
      intro y
      by_cases hy : 0 ≤ y i
      · have hsingle : (∑' m : ℕ, if y i = (m : ℤ) then
            percolation d p (connectionToSetEvent {z | 0 ≤ z i} 0 {y}) else 0) =
            percolation d p (connectionToSetEvent {z | 0 ≤ z i} 0 {y}) := by
          rw [tsum_eq_single (y i).toNat]
          · simp [Int.toNat_of_nonneg hy]
          · intro m hm
            have hne : y i ≠ (m : ℤ) := by
              intro heq
              apply hm
              omega
            exact ite_eq_right hne
        exact hsingle.symm
      · have hempty := halfSpace_connection_empty_of_negative_height i 0 y (lt_of_not_ge hy)
        simp only [hempty, measure_empty, ite_self, tsum_zero]
    _ = ∑' m : ℕ, ∑' y : Vertex d, if y i = (m : ℤ) then
        percolation d p (connectionToSetEvent {z | 0 ≤ z i} 0 {y}) else 0 :=
      ENNReal.tsum_comm
    _ = _ := tsum_congr (fun m ↦ halfSpace_prefix_sum p i (m : ℤ))

end NearCritical
