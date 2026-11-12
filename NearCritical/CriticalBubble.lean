module

public import NearCritical.LatticePowerSummability

/-! Critical bubble convergence derived from the explicit source assumption (A).
This does not assert the triangle condition or the spatial bubble decay bound. -/
@[expose] public section
namespace NearCritical

/-- General moment convergence deduced from the actual Green bound and lattice
power convergence. The exponent threshold is q*(2-d)<-d. -/
theorem critical_twoPoint_rpow_summable {d : ℕ} (hd : 2 ≤ d)
    (h : TwoPointAsymptotics d) (q : ℝ) (hq : 0 < q)
    (he : ((2 : ℝ) - (d : ℝ)) * q < -(d : ℝ)) :
    Summable (fun x : Vertex d => (twoPoint d (criticalPoint d) 0 x) ^ q) := by
  obtain ⟨C, hC, hb⟩ := critical_twoPoint_global_upper hd h
  have hs := (summable_regularized_euclideanNorm_rpow d
    (((2 : ℝ) - (d : ℝ)) * q) he).mul_left (C ^ q)
  apply hs.of_nonneg_of_le (fun x => Real.rpow_nonneg (twoPoint_nonneg _ _ _) q)
  intro x
  have hbound := hb 0 x
  simp only [zero_sub, euclideanNorm_neg] at hbound
  have hp := Real.rpow_le_rpow (twoPoint_nonneg _ _ _) hbound hq.le
  rw [Real.mul_rpow hC.le (Real.rpow_nonneg (by positivity) _),
    ← Real.rpow_mul (by positivity)] at hp
  exact hp

/-- The actual critical two-point function is square summable in d>4. -/
theorem critical_twoPoint_square_summable {d : ℕ} (hd : 4 < d)
    (h : TwoPointAsymptotics d) :
    Summable (fun x : Vertex d => (twoPoint d (criticalPoint d) 0 x) ^ 2) := by
  obtain ⟨C, hC, hb⟩ := critical_twoPoint_global_upper (by omega) h
  have hd' : (4 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hs := (summable_regularized_euclideanNorm_rpow d
    (4 - 2 * (d : ℝ)) (by linarith)).mul_left (C ^ 2)
  apply hs.of_nonneg_of_le (fun x => sq_nonneg _)
  intro x
  have hbound := hb 0 x
  simp only [zero_sub, euclideanNorm_neg] at hbound
  have hsq := pow_le_pow_left₀ (twoPoint_nonneg _ _ _) hbound 2
  have hp : ((max 1 (euclideanNorm x)) ^ ((2 : ℝ) - (d : ℝ))) ^ (2 : ℕ) =
      (max 1 (euclideanNorm x)) ^ (4 - 2 * (d : ℝ)) := by
    rw [← Real.rpow_mul_natCast (by positivity)]
    congr 1
    ring
  simpa only [mul_pow, hp] using hsq

end NearCritical
