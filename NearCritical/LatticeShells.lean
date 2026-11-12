module

public import NearCritical.LatticePowerSummability
public import NearCritical.WaterCube

/-! Quantitative lattice shell geometry for spatial convolution estimates.
These analytic counting cubes have integer radius n, independently of the
source's odd-side water-cube parametrization. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Finset

/-- The inclusive integer sup cube of radius n. -/
def latticeSupCube (d n : ℕ) : Finset (Vertex d) := rectangularBox (fun _ => n)

lemma mem_latticeSupCube {d n : ℕ} {x : Vertex d} :
    x ∈ latticeSupCube d n ↔ ∀ i, |x i| ≤ (n : ℤ) := by
  simp only [latticeSupCube, mem_rectangularBox, abs_le]

lemma latticeSupCube_mono (d : ℕ) {m n : ℕ} (h : m ≤ n) :
    latticeSupCube d m ⊆ latticeSupCube d n := by
  intro x hx
  apply mem_latticeSupCube.mpr
  intro i
  exact (mem_latticeSupCube.mp hx i).trans (by exact_mod_cast h)

lemma card_latticeSupCube (d n : ℕ) : (latticeSupCube d n).card = (2 * n + 1) ^ d := by
  simp [latticeSupCube, card_rectangularBox]

lemma latticeSupCube_zero (d : ℕ) : latticeSupCube d 0 = {0} := by
  ext x
  simp only [mem_latticeSupCube, Nat.cast_zero, mem_singleton]
  constructor
  · intro h
    funext i
    have hi := abs_le.mp (h i)
    change x i = 0
    omega
  · intro h
    subst x
    simp

/-- The radius-(n+1) shell has the correct surface-order cardinality. -/
theorem card_latticeSupShell_le (d n : ℕ) :
    (latticeSupCube d (n + 1) \ latticeSupCube d n).card ≤
      2 * d * (2 * n + 3) ^ (d - 1) := by
  rw [card_sdiff_of_subset (latticeSupCube_mono d (Nat.le_succ n)),
    card_latticeSupCube, card_latticeSupCube]
  grind [abs_pow_sub_pow_le (α := ℤ) (2 * n + 3) (2 * n + 1) d]

lemma latticeSupShell_euclidean_lower {d n : ℕ} {x : Vertex d}
    (hx : x ∈ latticeSupCube d (n + 1) \ latticeSupCube d n) :
    (n + 1 : ℝ) ≤ euclideanNorm x := by
  have hout := (mem_sdiff.mp hx).2
  rw [mem_latticeSupCube] at hout
  push Not at hout
  obtain ⟨i, hi⟩ := hout
  have hi' : (n + 1 : ℝ) ≤ |(x i : ℝ)| := by
    have hz : (n : ℤ) + 1 ≤ |x i| := by omega
    exact_mod_cast hz
  exact hi'.trans (Real.abs_le_sqrt
    (Finset.single_le_sum (fun j _ => sq_nonneg (x j : ℝ)) (Finset.mem_univ i)))

/-- A shellwise Euclidean power upper bound derived from actual geometry. -/
theorem sum_latticeSupShell_rpow_le (d n : ℕ) (r : ℝ) (hr : r ≤ 0) :
    ∑ x ∈ latticeSupCube d (n + 1) \ latticeSupCube d n,
      (max 1 (euclideanNorm x)) ^ r ≤
    (2 * d * (2 * n + 3) ^ (d - 1) : ℕ) * (n + 1 : ℝ) ^ r := by
  calc
    _ ≤ ∑ _x ∈ latticeSupCube d (n + 1) \ latticeSupCube d n, (n + 1 : ℝ) ^ r := by
      apply Finset.sum_le_sum
      intro x hx
      exact Real.rpow_le_rpow_of_nonpos (by positivity)
        ((latticeSupShell_euclidean_lower hx).trans (le_max_right _ _)) hr
    _ = ((latticeSupCube d (n + 1) \ latticeSupCube d n).card : ℝ) * (n + 1 : ℝ) ^ r := by
      simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast card_latticeSupShell_le d n)
      (Real.rpow_nonneg (by positivity) _)

/-- General surface-weighted power bound, with the dimension and exponent
combined explicitly for subsequent tail estimates. -/
theorem sum_latticeSupShell_power_le {d : ℕ} (hd : 1 ≤ d) (n : ℕ)
    (r : ℝ) (hr : r ≤ 0) :
    ∑ x ∈ latticeSupCube d (n + 1) \ latticeSupCube d n,
      (max 1 (euclideanNorm x)) ^ r ≤
      (2 * (d : ℝ) * 3 ^ (d - 1)) * (n + 1 : ℝ) ^ ((d : ℝ) - 1 + r) := by
  calc
    _ ≤ (2 * d * (2 * n + 3) ^ (d - 1) : ℕ) * (n + 1 : ℝ) ^ r :=
      sum_latticeSupShell_rpow_le d n r hr
    _ ≤ (2 * d * (3 * (n + 1)) ^ (d - 1) : ℕ) * (n + 1 : ℝ) ^ r := by
      gcongr
      omega
    _ = (2 * (d : ℝ) * 3 ^ (d - 1)) *
        ((n + 1 : ℝ) ^ (d - 1) * (n + 1 : ℝ) ^ r) := by
      push_cast
      rw [mul_pow]
      ring
    _ = _ := by
      rw [← Real.rpow_natCast (n + 1 : ℝ) (d - 1), ← Real.rpow_add (by positivity),
        Nat.cast_sub hd, Nat.cast_one]

/-- At the critical Green exponent, every shell contributes at most a
constant times its integer radius. -/
theorem sum_latticeSupShell_green_le {d : ℕ} (hd : 2 ≤ d) (n : ℕ) :
    ∑ x ∈ latticeSupCube d (n + 1) \ latticeSupCube d n,
      (max 1 (euclideanNorm x)) ^ ((2 : ℝ) - (d : ℝ)) ≤
      (2 * (d : ℝ) * 3 ^ (d - 1)) * (n + 1 : ℝ) := by
  have hd' : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have h := sum_latticeSupShell_power_le (by omega : 1 ≤ d) n
    ((2 : ℝ) - (d : ℝ)) (sub_nonpos.mpr hd')
  have he : (d : ℝ) - 1 + (2 - (d : ℝ)) = 1 := by ring
  simpa only [he, Real.rpow_one] using h

/-- Quantitative truncated critical-kernel mass, quadratic in radius.
No probabilistic or summability premise is assumed. -/
theorem sum_latticeSupCube_green_le {d : ℕ} (hd : 2 ≤ d) (N : ℕ) :
    ∑ x ∈ latticeSupCube d N, (max 1 (euclideanNorm x)) ^ ((2 : ℝ) - (d : ℝ)) ≤
      1 + (2 * (d : ℝ) * 3 ^ (d - 1)) * (N + 1 : ℝ) ^ 2 := by
  have hK : 0 ≤ 2 * (d : ℝ) * 3 ^ (d - 1) := by positivity
  induction N with
  | zero =>
    simp only [latticeSupCube_zero, sum_singleton, euclideanNorm, Pi.zero_apply,
      Int.cast_zero, zero_pow (by decide : 2 ≠ 0), sum_const_zero, Real.sqrt_zero,
      max_eq_left zero_le_one, Real.one_rpow, Nat.cast_zero, zero_add, one_pow, mul_one]
    linarith
  | succ N ih =>
    have hs := sum_latticeSupShell_green_le hd N
    have heq := Finset.sum_sdiff (f := fun x : Vertex d =>
      (max 1 (euclideanNorm x)) ^ ((2 : ℝ) - (d : ℝ)))
      (latticeSupCube_mono d (Nat.le_succ N))
    simp only [Nat.cast_add, Nat.cast_one] at *
    have hN : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
    nlinarith [mul_nonneg hK hN]

/-- The actual integer cubes exhaust all lattice vertices. -/
theorem exists_mem_latticeSupCube {d : ℕ} (x : Vertex d) :
    ∃ N : ℕ, x ∈ latticeSupCube d N := by
  refine ⟨∑ i, (x i).natAbs, mem_latticeSupCube.mpr ?_⟩
  intro i
  have hi : (x i).natAbs ≤ ∑ j, (x j).natAbs :=
    Finset.single_le_sum (f := fun j : Fin d => (x j).natAbs)
      (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
  simpa only [Int.natCast_natAbs] using (Int.ofNat_le.mpr hi)

/-- Every finite set can be bounded by one of these cubes, so shell estimates
apply to arbitrary finite partial sums, not just a fixed exhaustion. -/
theorem exists_subset_latticeSupCube {d : ℕ} (s : Finset (Vertex d)) :
    ∃ N : ℕ, s ⊆ latticeSupCube d N := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, Finset.empty_subset _⟩
  | @insert x s hx ih =>
    obtain ⟨N, hN⟩ := exists_mem_latticeSupCube x
    obtain ⟨M, hM⟩ := ih
    refine ⟨max N M, ?_⟩
    intro y hy
    rcases Finset.mem_insert.mp hy with rfl | hy
    · exact latticeSupCube_mono d (le_max_left _ _) hN
    · exact latticeSupCube_mono d (le_max_right _ _) (hM hy)

end NearCritical
