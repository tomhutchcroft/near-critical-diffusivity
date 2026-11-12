module

public import NearCritical.LatticeShells
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.SumIntegralComparisons
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! Quantitative lattice power tails derived from surface-order shell counts. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Finset

/-- Scalar power-tail estimate from the improper integral test. -/
theorem nat_rpow_tail_le (N : ℕ) (hN : 1 ≤ N) (r : ℝ) (hr : r < -1) :
    (∑' k : ℕ, (N + k + 1 : ℝ) ^ r) ≤ (N : ℝ) ^ (r + 1) / (-r - 1) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hanti : AntitoneOn (fun x : ℝ => x ^ r) (Set.Ici (N : ℝ)) := by
    intro x hx y hy hxy
    exact Real.rpow_le_rpow_of_nonpos (hNpos.trans_le hx) hxy (by linarith)
  have hi := AntitoneOn.tsum_comp_add_le_integral N hanti
    (integrableOn_Ioi_rpow_of_lt hr hNpos)
    (fun x hx => Real.rpow_nonneg (le_of_lt (hNpos.trans hx)) r)
  rw [integral_Ioi_rpow_of_lt hr hNpos] at hi
  convert hi using 1
  · congr 1
    funext k
    simp only [Nat.cast_add, Nat.cast_one]
    rw [add_comm (k : ℝ) (N : ℝ)]
  · rw [show -r - 1 = -(r + 1) by ring, div_neg, neg_div]

/-- Exact annular decomposition followed by the proved shellwise power bound. -/
theorem sum_cube_sdiff_power_le {d : ℕ} (hd : 1 ≤ d) (N M : ℕ)
    (r : ℝ) (hr : r ≤ 0) :
    ∑ x ∈ latticeSupCube d (N + M) \ latticeSupCube d N,
      (max 1 (euclideanNorm x)) ^ r ≤
      (2 * (d : ℝ) * 3 ^ (d - 1)) *
        ∑ k ∈ range M, (N + k + 1 : ℝ) ^ ((d : ℝ) - 1 + r) := by
  classical
  let f : Vertex d → ℝ := fun x => (max 1 (euclideanNorm x)) ^ r
  have hm : Monotone (fun k => latticeSupCube d (N + k)) := by
    intro a b hab
    exact latticeSupCube_mono d (Nat.add_le_add_left hab N)
  have heq := Finset.sum_eq_sum_range_sdiff (fun k => latticeSupCube d (N + k)) hm f M
  have hs := Finset.sum_sdiff (f := f) (latticeSupCube_mono d (Nat.le_add_right N M))
  simp only [Nat.add_zero, ← Nat.add_assoc] at heq
  calc
    _ = ∑ k ∈ range M, ∑ x ∈ latticeSupCube d (N + k + 1) \ latticeSupCube d (N + k), f x := by
      change (∑ x ∈ latticeSupCube d (N + M) \ latticeSupCube d N, f x) = _
      linarith
    _ ≤ ∑ k ∈ range M, (2 * (d : ℝ) * 3 ^ (d - 1)) *
        (N + k + 1 : ℝ) ^ ((d : ℝ) - 1 + r) := by
      apply Finset.sum_le_sum
      intro k hk
      simpa only [Nat.cast_add, Nat.cast_one, f] using
        sum_latticeSupShell_power_le hd (N + k) r hr
    _ = _ := (Finset.mul_sum _ _ _).symm

/-- A quantitative bound for every finite partial sum outside a radius-N cube.
The exponent and denominator are the sharp radial-integral ones. -/
theorem sum_outside_latticeSupCube_power_le {d : ℕ} (hd : 1 ≤ d)
    (N : ℕ) (hN : 1 ≤ N) (r : ℝ) (hr : r < -(d : ℝ))
    (s : Finset (Vertex d)) (hs : ∀ x ∈ s, x ∉ latticeSupCube d N) :
    ∑ x ∈ s, (max 1 (euclideanNorm x)) ^ r ≤
      (2 * (d : ℝ) * 3 ^ (d - 1)) * (N : ℝ) ^ ((d : ℝ) + r) / (-(d : ℝ) - r) := by
  classical
  obtain ⟨M, hM⟩ := exists_subset_latticeSupCube s
  have hK : 0 ≤ 2 * (d : ℝ) * 3 ^ (d - 1) := by positivity
  have hr0 : r ≤ 0 := le_trans hr.le (neg_nonpos.mpr (Nat.cast_nonneg d))
  have he : (d : ℝ) - 1 + r < -1 := by linarith
  have hsum : Summable (fun k : ℕ => (N + k + 1 : ℝ) ^ ((d : ℝ) - 1 + r)) := by
    have hbase := (Real.summable_nat_rpow.mpr he).comp_injective
      (show Function.Injective (fun k : ℕ => N + k + 1) from by
        intro a b hab
        dsimp at hab
        omega)
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using hbase
  calc
    _ ≤ ∑ x ∈ latticeSupCube d (N + M) \ latticeSupCube d N,
        (max 1 (euclideanNorm x)) ^ r := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro x hx
        exact mem_sdiff.mpr ⟨latticeSupCube_mono d (Nat.le_add_left M N) (hM hx), hs x hx⟩
      · intro x hx hxs
        positivity
    _ ≤ _ := (sum_cube_sdiff_power_le hd N M r hr0).trans (by
      calc
        _ ≤ (2 * (d : ℝ) * 3 ^ (d - 1)) *
            ∑' k : ℕ, (N + k + 1 : ℝ) ^ ((d : ℝ) - 1 + r) :=
          mul_le_mul_of_nonneg_left (hsum.sum_le_tsum _ (fun k hk => by positivity)) hK
        _ ≤ (2 * (d : ℝ) * 3 ^ (d - 1)) *
            ((N : ℝ) ^ (((d : ℝ) - 1 + r) + 1) / (-((d : ℝ) - 1 + r) - 1)) :=
          mul_le_mul_of_nonneg_left (nat_rpow_tail_le N hN _ he) hK
        _ = _ := by
          have he1 : ((d : ℝ) - 1 + r) + 1 = (d : ℝ) + r := by ring
          have he2 : -((d : ℝ) - 1 + r) - 1 = -(d : ℝ) - r := by ring
          rw [he1, he2]
          ring)

/-- Full lattice tail estimate, with a zero indicator inside the counting cube. -/
theorem tsum_outside_latticeSupCube_power_le {d : ℕ} (hd : 1 ≤ d)
    (N : ℕ) (hN : 1 ≤ N) (r : ℝ) (hr : r < -(d : ℝ)) :
    (∑' x : Vertex d, if x ∈ latticeSupCube d N then 0 else
      (max 1 (euclideanNorm x)) ^ r) ≤
      (2 * (d : ℝ) * 3 ^ (d - 1)) * (N : ℝ) ^ ((d : ℝ) + r) / (-(d : ℝ) - r) := by
  classical
  apply Real.tsum_le_of_sum_le
  · intro x
    change 0 ≤ (if x ∈ latticeSupCube d N then 0 else (max 1 (euclideanNorm x)) ^ r)
    split_ifs <;> positivity
  · intro s
    have h := sum_outside_latticeSupCube_power_le hd N hN r hr
      (s.filter (fun x => x ∉ latticeSupCube d N)) (by simp)
    simpa only [Finset.sum_filter, ite_not] using h

end NearCritical
