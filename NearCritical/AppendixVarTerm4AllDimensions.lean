module
public import NearCritical.AppendixShellCount

/-! Finite-cutoff repair of the fourth variance-term estimate at dimension nine.
Constants are explicit and independent of the scales. Pointwise and inner-region
percolation estimates remain hypotheses. -/
@[expose] public section
namespace NearCritical.AppendixVariance
open scoped BigOperators

/-- The finite cutoff supplies one extra denominator power. This covers d=9
without using an infinite borderline harmonic sum. -/
theorem scaled_radial_term4_le {d : ℕ} (hd : 9 ≤ d) (x : Fin d → ℤ)
    {n r : ℕ} (hr : 1 ≤ r) (hrn : r ≤ n) :
    ((n : ℝ)^3)⁻¹ * ∑ w ∈ linfBall x ((2*n : ℕ) : ℤ),
      ((linfDist x w + 1 : ℕ) : ℝ) /
        (max (r : ℝ) ((linfDist x w + 1 : ℕ) : ℝ))^(2*d-8) ≤
      (3 * (2*(d : ℝ)*3^(d-1)*
        ((((d-8 : ℕ) : ℝ)+1)/((d-8 : ℕ) : ℝ)))) / (r : ℝ)^(d-6) := by
  let t := d-8
  let A : ℝ := 2*(d : ℝ)*3^(d-1)*(((t : ℝ)+1)/(t : ℝ))
  have ht : 1 ≤ t := by dsimp [t]; omega
  have ht0 : (0 : ℝ) < t := by exact_mod_cast ht
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le hr0 (by exact_mod_cast hrn)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (hr.trans hrn)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  let R := fun w => ((linfDist x w + 1 : ℕ) : ℝ)
  let M := fun w => max (r : ℝ) (R w)
  have hMpos (w) : 0 < M w := lt_of_lt_of_le hr0 (le_max_left _ _)
  have hM (w) (hw : w ∈ linfBall x ((2*n : ℕ) : ℤ)) : M w ≤ 3*(n : ℝ) := by
    have hk := (mem_linfBall_iff_dist x w (by positivity)).mp hw
    simp only [Int.toNat_natCast] at hk
    have hkR : (linfDist x w : ℝ) ≤ 2*(n : ℝ) := by exact_mod_cast hk
    have hrR : (r : ℝ) ≤ n := by exact_mod_cast hrn
    dsimp [M, R]
    push_cast
    apply max_le <;> linarith
  have hpoint (w) (hw : w ∈ linfBall x ((2*n : ℕ) : ℤ)) :
      R w / M w^(2*d-8) ≤ 3*(n : ℝ)*(R w / M w^(2*d-7)) := by
    have he : 2*d-7 = (2*d-8)+1 := by omega
    calc
      _ = M w*(R w / M w^(2*d-7)) := by
        rw [he, pow_succ]
        field_simp [ne_of_gt (hMpos w)]
      _ ≤ _ := mul_le_mul_of_nonneg_right (hM w hw) (by dsimp [R]; positivity)
  have hrad : ∑ w ∈ linfBall x ((2*n : ℕ) : ℤ), R w/M w^(2*d-7) ≤ A/(r : ℝ)^t := by
    have h := radial_weighted_power_sum_le (by omega : 1 ≤ d) x 1 ht hr (2*n)
    have he : 1+(d-1)+(t+1) = 2*d-7 := by dsimp [t]; omega
    simp only [pow_one, he] at h
    refine h.trans (le_of_eq ?_)
    dsimp [A]
    ring
  have hsum : ∑ w ∈ linfBall x ((2*n : ℕ) : ℤ), R w/M w^(2*d-8) ≤
      3*(n : ℝ)*(A/(r : ℝ)^t) := by
    calc
      _ ≤ ∑ w ∈ linfBall x ((2*n : ℕ) : ℤ), 3*(n : ℝ)*(R w/M w^(2*d-7)) :=
        Finset.sum_le_sum hpoint
      _ = 3*(n : ℝ)*∑ w ∈ linfBall x ((2*n : ℕ) : ℤ), R w/M w^(2*d-7) := by
        rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left hrad (by positivity)
  change ((n : ℝ)^3)⁻¹ * _ ≤ (3*A)/(r : ℝ)^(d-6)
  calc
    _ ≤ ((n : ℝ)^3)⁻¹ * (3*(n : ℝ)*(A/(r : ℝ)^t)) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = (3*A/(r : ℝ)^t) * (1/(n : ℝ)^2) := by
      field_simp [ne_of_gt hn0, ne_of_gt hr0]
      <;> ring
    _ ≤ (3*A/(r : ℝ)^t) * (1/(r : ℝ)^2) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact one_div_le_one_div_of_le (pow_pos hr0 2)
        (pow_le_pow_left₀ hr0.le (by exact_mod_cast hrn) 2)
    _ = (3*A)/(r : ℝ)^(d-6) := by
      have he : d-6 = t+2 := by dsimp [t]; omega
      rw [he, pow_add]
      ring

/-- Fourth-term conditional reduction for every source dimension d>=9.
Its displayed constant depends only on dimension and the supplied uniform
pointwise/inner constants, not on n,r or the summation region. -/
theorem var_term_4_all_dimensions {d : ℕ} (hd : 9 ≤ d) (x : Fin d → ℤ)
    {n r : ℕ} (hr : 1 ≤ r) (hrn : r ≤ n)
    (Ann outer : Finset (Fin d → ℤ)) (g F : (Fin d → ℤ) → ℝ)
    (Couter Cin : ℝ) (hCouter : 0 ≤ Couter)
    (houter_sub : outer ⊆ Ann)
    (houter_ball : outer ⊆ linfBall x ((2*n : ℕ) : ℤ))
    (hptwise : ∀ w ∈ outer, g w*F w^2 ≤ Couter*((n : ℝ)^3)⁻¹ *
      (((linfDist x w+1 : ℕ) : ℝ) /
        (max (r : ℝ) ((linfDist x w+1 : ℕ) : ℝ))^(2*d-8)))
    (hinner : ∑ w ∈ Ann \ outer, g w*F w^2 ≤ Cin/(r : ℝ)^(d-6)) :
    ∑ w ∈ Ann, g w*F w^2 ≤
      (Couter*(3*(2*(d : ℝ)*3^(d-1)*
        ((((d-8 : ℕ) : ℝ)+1)/((d-8 : ℕ) : ℝ))))+Cin)/(r : ℝ)^(d-6) := by
  let A : ℝ := 3*(2*(d : ℝ)*3^(d-1)*
    ((((d-8 : ℕ) : ℝ)+1)/((d-8 : ℕ) : ℝ)))
  have houter : ∑ w ∈ outer, g w*F w^2 ≤ Couter*A/(r : ℝ)^(d-6) := by
    calc
      _ ≤ ∑ w ∈ outer, Couter*((n : ℝ)^3)⁻¹ *
          (((linfDist x w+1 : ℕ) : ℝ) /
            (max (r : ℝ) ((linfDist x w+1 : ℕ) : ℝ))^(2*d-8)) :=
        Finset.sum_le_sum hptwise
      _ = Couter * (((n : ℝ)^3)⁻¹ * ∑ w ∈ outer,
          (((linfDist x w+1 : ℕ) : ℝ) /
            (max (r : ℝ) ((linfDist x w+1 : ℕ) : ℝ))^(2*d-8))) := by
        rw [← Finset.mul_sum, mul_assoc]
      _ ≤ Couter * (((n : ℝ)^3)⁻¹ * ∑ w ∈ linfBall x ((2*n : ℕ) : ℤ),
          (((linfDist x w+1 : ℕ) : ℝ) /
            (max (r : ℝ) ((linfDist x w+1 : ℕ) : ℝ))^(2*d-8))) := by
        apply mul_le_mul_of_nonneg_left _ hCouter
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact Finset.sum_le_sum_of_subset_of_nonneg houter_ball (fun w _ _ => by positivity)
      _ ≤ Couter*(A/(r : ℝ)^(d-6)) :=
        mul_le_mul_of_nonneg_left (scaled_radial_term4_le hd x hr hrn) hCouter
      _ = _ := by ring
  calc
    _ = (∑ w ∈ Ann \ outer, g w*F w^2) + ∑ w ∈ outer, g w*F w^2 :=
      (Finset.sum_sdiff houter_sub).symm
    _ ≤ Cin/(r : ℝ)^(d-6) + Couter*A/(r : ℝ)^(d-6) := add_le_add hinner houter
    _ = _ := by dsimp [A]; ring

end NearCritical.AppendixVariance
