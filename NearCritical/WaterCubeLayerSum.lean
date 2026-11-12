module

public import NearCritical.WaterCube
public import Mathlib.NumberTheory.Harmonic.Bounds

/-! Exact issued-edge layer counts for the NEW a-priori conductivity argument.
No probability estimate or assumed layer-count envelope enters these proofs. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Finset
open scoped Classical

/-- Base layer numbered from zero at the negative face of the water cube. -/
def waterCubeLayer {d : ℕ} (i : Fin d) (r : ℕ) (x : Vertex d) : ℕ :=
  (x i + (r : ℤ)).toNat

lemma waterCubeLayer_lt {d : ℕ} (i : Fin d) (r R : ℕ) {x : Vertex d}
    (hx : x ∈ waterCube d i r R) : waterCubeLayer i r x < 2 * r + 1 := by
  have hi := (mem_rectangularBox.mp hx) i
  simp only [ite_true] at hi
  unfold waterCubeLayer
  omega

/-- The transverse slice count is exact, including d=1. -/
theorem card_waterCube_layer {d : ℕ} (i : Fin d) (r R k : ℕ) (hk : k < 2 * r + 1) :
    ((waterCube d i r R).filter (fun x => waterCubeLayer i r x = k)).card =
      (2 * R + 1) ^ (d - 1) := by
  have heq : (waterCube d i r R).filter (fun x => waterCubeLayer i r x = k) =
      (waterCube d i r R).filter (fun x => x i = (k : ℤ) - (r : ℤ)) := by
    ext x
    simp only [mem_filter]
    constructor
    · rintro ⟨hx, hl⟩
      have hi := (mem_rectangularBox.mp hx) i
      simp only [ite_true] at hi
      exact ⟨hx, by unfold waterCubeLayer at hl; omega⟩
    · rintro ⟨hx, hl⟩
      exact ⟨hx, by unfold waterCubeLayer; omega⟩
  rw [heq]
  unfold waterCube rectangularBox
  rw [Fintype.card_filter_piFinset_eq_of_mem
    (fun j : Fin d => Icc (-(if j = i then r else R : ℕ) : ℤ)
      (if j = i then r else R : ℕ)) i]
  · calc
      _ = ∏ _j ∈ (univ : Finset (Fin d)).erase i, (2 * R + 1) := by
        apply prod_congr rfl
        intro j hj
        rw [ite_eq_right (mem_erase.mp hj).1, Int.card_Icc]
        omega
      _ = _ := by simp
  · simp only [ite_true, mem_Icc]
    constructor <;> omega

/-- Every base-layer observable factors into a transverse count and the
one-dimensional layer sum. -/
theorem sum_waterCube_layers {d : ℕ} (i : Fin d) (r R : ℕ) (f : ℕ → ℝ) :
    (∑ x ∈ waterCube d i r R, f (waterCubeLayer i r x)) =
      ((2 * R + 1) ^ (d - 1) : ℕ) * ∑ k ∈ range (2 * r + 1), f k := by
  rw [← Finset.sum_fiberwise_of_maps_to' (fun x hx => mem_range.mpr (waterCubeLayer_lt i r R hx)) f]
  calc
    _ = ∑ k ∈ range (2 * r + 1), ((2 * R + 1) ^ (d - 1) : ℕ) * f k := by
      apply sum_congr rfl
      intro k hk
      rw [sum_const, nsmul_eq_mul, card_waterCube_layer i r R k (mem_range.mp hk)]
    _ = _ := (mul_sum _ _ _).symm

/-- Issued bonds are base vertices times ALL positive coordinate directions.
Thus no unoriented-edge factor or face-reflection identification is assumed. -/
theorem sum_issued_waterCube_layers {d : ℕ} (i : Fin d) (r R : ℕ) (f : ℕ → ℝ) :
    (∑ e : IssuedBond (waterCube d i r R), f (waterCubeLayer i r e.val.1)) =
      (d : ℝ) * ((2 * R + 1) ^ (d - 1) : ℕ) * ∑ k ∈ range (2 * r + 1), f k := by
  calc
    _ = ∑ e ∈ issuedBondSet (waterCube d i r R), f (waterCubeLayer i r e.1) :=
      Finset.sum_attach _ _
    _ = (d : ℝ) * ∑ x ∈ waterCube d i r R, f (waterCubeLayer i r x) := by
      simp [issuedBondSet, Finset.sum_product, ← Finset.mul_sum]
    _ = _ := by rw [sum_waterCube_layers]; ring

/-- Symmetric BASE-layer depth proxy. It is not asserted to be the graph
metric distance of an issued edge to a face. -/
def waterCubeBaseDepth {d : ℕ} (i : Fin d) (r : ℕ) (x : Vertex d) : ℕ :=
  min (waterCubeLayer i r x) (2 * r - waterCubeLayer i r x)

lemma inv_min_nat_add_one_le (a b : ℕ) :
    1 / (min a b + 1 : ℝ) ≤ 1 / (a + 1 : ℝ) + 1 / (b + 1 : ℝ) := by
  rcases le_total a b with h | h
  · rw [min_eq_left h]
    have hp : 0 ≤ 1 / (b + 1 : ℝ) := by positivity
    linarith
  · rw [min_eq_right h]
    have hp : 0 ≤ 1 / (a + 1 : ℝ) := by positivity
    linarith

/-- The nearest-layer reciprocal sum is bounded by two harmonic sums. -/
lemma sum_inverse_symmetric_layers_le (h : ℕ) :
    (∑ k ∈ range h, 1 / (min k (h - 1 - k) + 1 : ℝ)) ≤ 2 * (1 + Real.log h) := by
  have hb : (∑ k ∈ range h, 1 / (min k (h - 1 - k) + 1 : ℝ)) ≤
      ∑ k ∈ range h, (1 / (k + 1 : ℝ) + 1 / ((h - 1 - k : ℕ) + 1 : ℝ)) :=
    sum_le_sum (fun k hk => inv_min_nat_add_one_le _ _)
  rw [sum_add_distrib, sum_range_reflect (fun k => 1 / (k + 1 : ℝ)) h] at hb
  have he : (∑ k ∈ range h, 1 / (k + 1 : ℝ)) = (harmonic h : ℝ) := by
    simp [harmonic, one_div]
  rw [he] at hb
  have hh := harmonic_le_one_add_log h
  linarith

/-- The actual issued-edge harmonic layer sum in source eq.aa_bound_step2. -/
theorem sum_issued_waterCube_inverse_depth_le {d : ℕ} (i : Fin d) (r R : ℕ) :
    (∑ e : IssuedBond (waterCube d i r R), 1 / (waterCubeBaseDepth i r e.val.1 + 1 : ℝ)) ≤
      2 * (d : ℝ) * ((2 * R + 1) ^ (d - 1) : ℕ) * (1 + Real.log (2 * r + 1 : ℕ)) := by
  rw [show (∑ e : IssuedBond (waterCube d i r R), 1 / (waterCubeBaseDepth i r e.val.1 + 1 : ℝ)) =
      (d : ℝ) * ((2 * R + 1) ^ (d - 1) : ℕ) *
        ∑ k ∈ range (2 * r + 1), 1 / (min k (2 * r - k) + 1 : ℝ) from
    sum_issued_waterCube_layers i r R (fun k => 1 / (min k (2 * r - k) + 1 : ℝ))]
  have he : 2 * r + 1 - 1 = 2 * r := by omega
  have hh := sum_inverse_symmetric_layers_le (2 * r + 1)
  rw [he] at hh
  exact (mul_le_mul_of_nonneg_left hh (by positivity)).trans_eq (by ring)

end NearCritical
