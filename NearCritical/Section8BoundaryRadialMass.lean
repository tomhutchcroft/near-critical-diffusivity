module

public import NearCritical.AppendixFRDSums
public import NearCritical.Bernoulli
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-! Boundary radial estimates for the global F2 convolution. -/
@[expose] public section
noncomputable section
namespace NearCritical.Section8
open AppendixVariance
open scoped Classical

/-- A decreasing radial weight on a subset of the cube boundary is bounded
by the corresponding lower-dimensional ball sums on its signed faces. -/
theorem boundary_radial_projection_sum_le {k n R : ℕ} (x : Vertex (k + 1))
    (U : Finset (Vertex (k + 1))) (hU : U ⊆ cubeBoundary n)
    (hR : ∀ y ∈ U, linfDist x y ≤ R) (f : ℕ → ℝ) (hf : ∀ m, 0 ≤ f m) (hmono : Antitone f)
    (C : ℝ) (hC : 0 ≤ C)
    (hball : ∀ z : Vertex k, ∑ u ∈ linfBall z (R : ℤ), f (linfDist z u) ≤ C) :
    ∑ y ∈ U, f (linfDist x y) ≤ ((k : ℝ) + 1) * (2 * C) := by
  let signs : Finset ℤ := {(n : ℤ), -(n : ℤ)}
  let J := (Finset.univ : Finset (Fin (k + 1))) ×ˢ signs
  let face (j : Fin (k + 1) × ℤ) := linfBall (Fin.removeNth j.1 x) (R : ℤ)
  let P := J.sigma face
  let lift (p : Σ _ : Fin (k + 1) × ℤ, Vertex k) : Vertex (k + 1) :=
    Fin.insertNth (α := fun _ => ℤ) p.1.1 p.1.2 p.2
  have hcover : U ⊆ P.image lift := by
    intro y hy
    have hyN := (Finset.mem_filter.mp (hU hy)).2
    obtain ⟨j, _, hj⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (Fin (k + 1)))
      Finset.univ_nonempty (fun i => (y i).natAbs)
    have hyj : (y j).natAbs = n := by rw [← hyN, linfDist_zero, hj]
    refine Finset.mem_image.mpr ⟨⟨(j, y j), Fin.removeNth j y⟩, ?_, Fin.insertNth_self_removeNth j y⟩
    apply Finset.mem_sigma.mpr
    refine ⟨?_, ?_⟩
    · simp only [J, signs, Finset.mem_product, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
      omega
    · apply (mem_linfBall_iff_dist _ _ (Int.natCast_nonneg R)).mpr
      rw [Int.toNat_natCast]
      have h := linfDist_removeNth_le x j (y j) (Fin.removeNth j y)
      rw [Fin.insertNth_self_removeNth] at h
      exact h.trans (hR y hy)
  have hface (j : Fin (k + 1) × ℤ) : ∑ u ∈ face j, f (linfDist x (lift ⟨j, u⟩)) ≤ C := by
    refine (Finset.sum_le_sum (fun u _ => hmono (linfDist_removeNth_le x j.1 j.2 u))).trans ?_
    exact hball (Fin.removeNth j.1 x)
  have hsigns : signs.card ≤ 2 := (Finset.card_insert_le _ _).trans (by simp)
  calc
    _ ≤ ∑ y ∈ P.image lift, f (linfDist x y) :=
      Finset.sum_le_sum_of_subset_of_nonneg hcover (fun y _ _ => hf _)
    _ ≤ ∑ p ∈ P, f (linfDist x (lift p)) := Finset.sum_image_le_of_nonneg (fun y _ => hf _)
    _ = ∑ j ∈ J, ∑ u ∈ face j, f (linfDist x (lift ⟨j, u⟩)) := by
      dsimp only [P]
      rw [Finset.sum_sigma]
    _ ≤ ∑ _j ∈ J, C := Finset.sum_le_sum fun j _ => hface j
    _ = ((k : ℝ) + 1) * ((signs.card : ℝ) * C) := by
      simp only [J, Finset.sum_const, Finset.card_product, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (by exact_mod_cast hsigns) hC) (by positivity)

/-- The ERE2 radial weight has cubic mass on any boundary ball. -/
theorem boundary_cutoff_mass_in_ball_le {k n R r : ℕ} (hk : 3 ≤ k) (x : Vertex (k + 1))
    (U : Finset (Vertex (k + 1))) (hU : U ⊆ cubeBoundary n) (hR : ∀ y ∈ U, linfDist x y ≤ R) :
    ∑ y ∈ U, frdKernel r (k - 3) x y ≤
      ((k : ℝ) + 1) * (2 * (2 * (k : ℝ) * 3 ^ (k - 1) * ((R : ℝ) + 1) ^ 3)) := by
  let f (m : ℕ) : ℝ := 1 / (max (r : ℝ) ((m + 1 : ℕ) : ℝ)) ^ (k - 3)
  have hmono : Antitone f := by
    intro a b hab
    dsimp [f]
    apply one_div_le_one_div_of_le (by positivity)
    exact pow_le_pow_left₀ (by positivity) (max_le_max le_rfl (by exact_mod_cast Nat.succ_le_succ hab)) _
  exact boundary_radial_projection_sum_le x U hU hR f (fun _ => by dsimp [f]; positivity) hmono
    _ (by positivity) (fun z => ball_maxr_pow_cubic hk z r R)

/-- Summing the shifted boundary kernel of degree `d` cancels the factor
`1 + depth` at the starting point. -/
theorem boundary_depth_kernel_mass_le {k n : ℕ} (hk : 1 ≤ k) (u : Vertex (k + 1))
    (hu : u ∈ (cube n : Finset (Vertex (k + 1)))) :
    ∑ y ∈ (cubeBoundary n : Finset (Vertex (k + 1))),
      (((n - linfDist 0 u + 1 : ℕ) : ℝ) / ((linfDist u y + 1 : ℕ) : ℝ) ^ (k + 1)) ≤
      ((k : ℝ) + 1) * (2 * (4 * (k : ℝ) * 3 ^ (k - 1))) := by
  let l := n - linfDist 0 u + 1
  let f (m : ℕ) : ℝ := 1 / (max (l : ℝ) ((m + 1 : ℕ) : ℝ)) ^ (k + 1)
  let C : ℝ := 4 * (k : ℝ) * 3 ^ (k - 1)
  let U : Finset (Vertex (k + 1)) := cubeBoundary n
  have hl : 1 ≤ l := by dsimp [l]; omega
  have hl0 : (0 : ℝ) < l := by exact_mod_cast hl
  have hrad : ∀ y ∈ U, linfDist u y ≤ 2 * n := by
    intro y hy
    have hyQ := (Finset.mem_filter.mp hy).1
    have h := (mem_linfBall_iff_dist u y (Int.natCast_nonneg (2 * n))).mp
      (cube_subset_linfBall_two hu hyQ)
    simpa only [Int.toNat_natCast] using h
  have hmono : Antitone f := by
    intro a b hab
    dsimp [f]
    apply one_div_le_one_div_of_le (by positivity)
    exact pow_le_pow_left₀ (by positivity) (max_le_max le_rfl (by exact_mod_cast Nat.succ_le_succ hab)) _
  have hball (z : Vertex k) : ∑ y ∈ linfBall z ((2 * n : ℕ) : ℤ), f (linfDist z y) ≤ C / (l : ℝ) := by
    have h := radial_power_sum_le hk z (t := 1) (r := l) (by decide) hl (2 * n)
    simp only [show k - 1 + (1 + 1) = k + 1 by omega] at h
    refine h.trans (le_of_eq ?_)
    dsimp [C]
    norm_num <;> ring
  have h := boundary_radial_projection_sum_le u U (Finset.Subset.refl _) hrad f
    (fun _ => by dsimp [f]; positivity) hmono (C / (l : ℝ)) (by positivity) hball
  change (∑ y ∈ U, (l : ℝ) / ((linfDist u y + 1 : ℕ) : ℝ) ^ (k + 1)) ≤ _
  calc
    _ = ∑ y ∈ U, (l : ℝ) * f (linfDist u y) := by
      apply Finset.sum_congr rfl
      intro y hy
      have hyn := (Finset.mem_filter.mp hy).2
      have htri := linfDist_triangle 0 u y
      rw [hyn] at htri
      have hle : l ≤ linfDist u y + 1 := by dsimp [l]; omega
      dsimp [f]
      rw [max_eq_right (by exact_mod_cast hle), ← mul_div_assoc, mul_one]
    _ = (l : ℝ) * (∑ y ∈ U, f (linfDist u y)) := by rw [Finset.mul_sum]
    _ ≤ (l : ℝ) * (((k : ℝ) + 1) * (2 * (C / (l : ℝ)))) := mul_le_mul_of_nonneg_left h hl0.le
    _ = _ := by dsimp [C]; field_simp [hl0.ne'] <;> ring

end NearCritical.Section8
