module
public import NearCritical.Section8EnergyMoments
public import NearCritical.Section8SourceAnnulusBridge
public import NearCritical.AppendixFRDSums
public import NearCritical.AppendixTwoPointBridge

/-! Exact identification of the existing ERE weights with the literal F_RD kernels.
No probability or analytic estimate is assumed here. -/
@[expose] public section
noncomputable section
namespace NearCritical.Section8
open AppendixVariance
open scoped Classical BigOperators

/-- The source's fractional outer cutoff is exactly the integer floor cube. -/
theorem mem_three_quarter_cube_iff {d n : ℕ} (y : Vertex d) :
    y ∈ (cube (3*n/4) : Finset (Vertex d)) ↔
      latticeDistance 0 y ≤ 3*(n : ℝ)/4 := by
  have hm : y ∈ (cube (3*n/4) : Finset (Vertex d)) ↔ linfDist 0 y ≤ 3*n/4 := by
    simpa only [cube,Int.toNat_natCast] using
      (mem_linfBall_iff_dist (0 : Vertex d) y (Int.natCast_nonneg (3*n/4)))
  rw [hm,Nat.le_div_iff_mul_le (by decide : 0 < 4)]
  rw [← linfDist_cast_eq_latticeDistance]
  constructor
  · intro h
    have hR : (linfDist (0 : Vertex d) y : ℝ)*4 ≤ 3*(n : ℝ) := by exact_mod_cast h
    linarith
  · intro h
    have hR : (linfDist (0 : Vertex d) y : ℝ)*4 ≤ 3*(n : ℝ) := by linarith
    exact_mod_cast hR

private theorem integer_kernel_eq {d a : ℕ} (ha : a ≤ d) (M : ℝ) :
    M^((a : ℤ)-(d : ℤ)) = 1/M^(d-a) := by
  have he : (a : ℤ)-(d : ℤ) = -((d-a : ℕ) : ℤ) := by omega
  rw [he,zpow_neg,zpow_natCast,one_div]

/-- Existing ERE1 weight, summed on the whole cube, equals the literal outer F1 sum.
The arbitrary multiplier can in particular be the actual annulus connection probability. -/
theorem energyOneWeight_sum_eq_literal {d n : ℕ} (hd : 2 ≤ d)
    (r : ℕ) (x : Vertex d) (P : Vertex d → ℝ) :
    (∑ y ∈ (cube n : Finset (Vertex d)), energyOneWeight (cube (3*n/4)) r x y * P y) =
      ∑ y ∈ (cube n : Finset (Vertex d)).filter
        (fun y => 3*(n : ℝ)/4 < latticeDistance 0 y),
        P y/(max (r : ℝ) (latticeDistance x y))^(d-2) := by
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro y _
  have hm := mem_three_quarter_cube_iff (n := n) y
  by_cases hy : y ∈ (cube (3*n/4) : Finset (Vertex d))
  · have hout : ¬ 3*(n : ℝ)/4 < latticeDistance 0 y := not_lt.mpr (hm.mp hy)
    simp [energyOneWeight,hy,hout]
  · have hout : 3*(n : ℝ)/4 < latticeDistance 0 y := lt_of_not_ge (fun h => hy (hm.mpr h))
    simp only [energyOneWeight,hy,not_false_eq_true,ite_true,hout]
    have hk := integer_kernel_eq hd (max (r : ℝ) (latticeDistance x y))
    norm_num only [Nat.cast_ofNat] at hk
    rw [hk]
    ring

/-- Existing ERE2 weight uses the full outer boundary, including the diagonal. -/
theorem energyTwoWeight_sum_eq_literal {d n : ℕ} (hd : 4 ≤ d)
    (r : ℕ) (x : Vertex d) (P : Vertex d → ℝ) :
    (∑ y ∈ (cube n : Finset (Vertex d)), energyTwoWeight (cubeBoundary n) r x y * P y) =
      ∑ y ∈ (cubeBoundary n : Finset (Vertex d)),
        P y/(max (r : ℝ) (latticeDistance x y))^(d-4) := by
  unfold cubeBoundary
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro y hy
  simp only [energyTwoWeight,Finset.mem_filter,hy,true_and]
  split_ifs
  · have hk := integer_kernel_eq hd (max (r : ℝ) (latticeDistance x y))
    norm_num only [Nat.cast_ofNat] at hk
    rw [hk]
    ring
  · ring

end NearCritical.Section8
