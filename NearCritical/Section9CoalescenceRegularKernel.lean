module

public import NearCritical.NestRegularBoundary

@[expose] public section
namespace NearCritical

/-- The source regularity energy controls the clipped bubble row on every
selected subset of the same revealed boundary, including the diagonal. -/
theorem section9_regular_bubble_row_le {d : ℕ} (hd : 4 ≤ d)
    (F S boundary Y : Finset (Vertex d)) (r : ℕ) (hr : 1 ≤ r)
    (δ : ℝ) (x : Vertex d) (hx : sourceRegularPoint F S boundary r δ x)
    (hY : Y ⊆ F ∩ boundary) :
    ∑ y ∈ Y, (max 1 (latticeDistance x y)) ^ ((4:ℝ)-(d:ℝ)) ≤
      (r:ℝ) ^ ((d:ℝ)-4) * δ := by
  have hr1 : (1:ℝ) ≤ r := by exact_mod_cast hr
  have hr0 : (0:ℝ) < r := zero_lt_one.trans_le hr1
  have hd' : (4:ℝ) ≤ d := by exact_mod_cast hd
  let k := (4:ℝ)-(d:ℝ)
  have hk : k ≤ 0 := sub_nonpos.mpr hd'
  have hpoint (y : Vertex d) :
      (max 1 (latticeDistance x y)) ^ k ≤
        (r:ℝ) ^ (-k) * (max (r:ℝ) (latticeDistance x y)) ^ k := by
    let D := latticeDistance x y
    have hD : 0 ≤ D := dist_nonneg
    have hmul : max (r:ℝ) D ≤ (r:ℝ) * max 1 D := by
      apply max_le
      · simpa only [mul_one] using mul_le_mul_of_nonneg_left
          (le_max_left (1:ℝ) D) hr0.le
      · exact (le_max_right (1:ℝ) D).trans
          (by simpa only [one_mul] using
            (mul_le_mul_of_nonneg_right hr1 (zero_le_one.trans (le_max_left (1:ℝ) D))))
    have hpow := Real.rpow_le_rpow_of_nonpos
      (hr0.trans_le (le_max_left (r:ℝ) D)) hmul hk
    rw [Real.mul_rpow hr0.le (zero_le_one.trans (le_max_left (1:ℝ) D))] at hpow
    have hInv : (r:ℝ)^(-k) * (r:ℝ)^k = 1 := by
      rw [← Real.rpow_add hr0, neg_add_cancel, Real.rpow_zero]
    have h := mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg hr0.le (-k))
    rwa [← mul_assoc, hInv, one_mul] at h
  have hEnergy : (∑ y ∈ F ∩ boundary,
      (max (r:ℝ) (latticeDistance x y)) ^ k) ≤ δ := by
    simpa only [regularityEnergyTwo, k, ← Real.rpow_intCast, Int.cast_sub,
      Int.cast_ofNat, Int.cast_natCast] using hx.2.2
  have he : -k = (d:ℝ)-4 := by dsimp [k]; ring
  calc
    _ ≤ ∑ y ∈ Y, (r:ℝ)^(-k) * (max (r:ℝ) (latticeDistance x y))^k :=
      Finset.sum_le_sum fun y _ => hpoint y
    _ ≤ _ := by
      rw [← Finset.mul_sum, ← he]
      exact mul_le_mul_of_nonneg_left ((Finset.sum_le_sum_of_subset_of_nonneg hY
        (fun y _ _ => by positivity)).trans hEnergy) (Real.rpow_nonneg hr0.le _)

/-- Applying the regularity row estimate from either root family gives
the smaller cardinality in the Case 1 sum. -/
theorem section9_regular_bubble_pair_sum_le {d : ℕ} (hd : 4 ≤ d)
    (F S boundary X Y : Finset (Vertex d)) (r : ℕ) (hr : 1 ≤ r) (δ : ℝ)
    (hX : ∀ x ∈ X, sourceRegularPoint F S boundary r δ x)
    (hY : ∀ y ∈ Y, sourceRegularPoint F S boundary r δ y) :
    (∑ x ∈ X, ∑ y ∈ Y, (max 1 (latticeDistance x y)) ^ ((4:ℝ)-(d:ℝ))) ≤
      (min X.card Y.card : ℕ) * ((r:ℝ)^((d:ℝ)-4) * δ) := by
  let K := (r:ℝ)^((d:ℝ)-4) * δ
  have hx : X ⊆ F ∩ boundary := fun x hx => (hX x hx).1
  have hy : Y ⊆ F ∩ boundary := fun y hy => (hY y hy).1
  have hrow : (∑ x ∈ X, ∑ y ∈ Y, (max 1 (latticeDistance x y)) ^ ((4:ℝ)-(d:ℝ))) ≤
      (X.card : ℝ) * K := by
    calc
      _ ≤ ∑ _x ∈ X, K := Finset.sum_le_sum fun x hx =>
        section9_regular_bubble_row_le hd F S boundary Y r hr δ x (hX x hx) hy
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  have hcol : (∑ x ∈ X, ∑ y ∈ Y, (max 1 (latticeDistance x y)) ^ ((4:ℝ)-(d:ℝ))) ≤
      (Y.card : ℝ) * K := by
    rw [Finset.sum_comm]
    calc
      _ ≤ ∑ _y ∈ Y, K := by
        apply Finset.sum_le_sum
        intro y hy'
        simp_rw [latticeDistance_comm _ y]
        exact section9_regular_bubble_row_le hd F S boundary X r hr δ y (hY y hy') hx
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  by_cases h : X.card ≤ Y.card
  · simpa only [min_eq_left h] using hrow
  · simpa only [min_eq_right (Nat.le_of_not_ge h)] using hcol

end NearCritical
