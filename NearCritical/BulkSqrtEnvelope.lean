module

public import NearCritical.BulkUpperFromEnvelopes

@[expose] public section
namespace NearCritical

/-- The probability bound for the auxiliary energy gives the square-root
envelope used by the bulk differential inequality. -/
theorem bulk_sqrt_le_of_exponential_envelope {u C H s : ℝ}
    (hC : 0 ≤ C) (hH : 0 < H)
    (hu : u ≤ C/H^2 * Real.exp (-H*s/C)) :
    Real.sqrt u ≤ Real.sqrt C/H * Real.exp (-(H*s/C)/2) := by
  refine (Real.sqrt_le_sqrt hu).trans_eq ?_
  have hexp : Real.exp (-H*s/C) = (Real.exp (-(H*s/C)/2))^2 := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [Real.sqrt_mul (div_nonneg hC (sq_nonneg _)), Real.sqrt_div hC,
    Real.sqrt_sq hH.le, hexp, Real.sqrt_sq (Real.exp_nonneg _)]

end NearCritical
