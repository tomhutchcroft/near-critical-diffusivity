module

public import NearCritical.AppendixShellCount

/-! The paper's standing assumption (A) (`eq:two_point_assumption`, source line 373, tag `(A)`):
`P_{p_c}(x ↔ y) ∼ A‖x-y‖^{-d+2}`. Every theorem of the paper — including the main result
`thm.main` and both appendices — is stated conditionally: "If `d ≥ 9` and (A) holds then …".
The paper ASSUMES (A) (citing Hara–Slade / Fitzner–van der Hofstad), it does not prove it; so a
faithful formalization necessarily takes the two-point bound as a hypothesis.

Here `TwoPointBound tau` is the upper-bound form of (A) for an abstract two-point function `tau`
(the only part the Appendix-B variance estimates use). `bubble_from_twopoint` shows the bubble /
convolution estimate `∑ τ(x,y)τ(u,y) ≲ (1+|x-u|_∞)^{4-d}`-type bound follows from (A) via the
verified `bubble_bound` — i.e. the Appendix-B analytic engine composes with the paper's root
assumption. -/
@[expose] public section
namespace NearCritical.AppendixVariance
open scoped BigOperators

/-- Assumption (A), upper-bound form: the two-point function `tau` is nonnegative and obeys the
Green's-function power-law decay `tau a b ≤ C / (|a-b|_∞ + 1)^{d-2}`. This is the standing
hypothesis the whole paper is conditional on. -/
def TwoPointBound {d : ℕ} (tau : (Fin d → ℤ) → (Fin d → ℤ) → ℝ) (C : ℝ) : Prop :=
  ∀ a b, 0 ≤ tau a b ∧ tau a b ≤ C / ((linfDist a b + 1 : ℕ) : ℝ) ^ (d - 2)

/-- Under assumption (A) (`TwoPointBound`), the bubble / two-point convolution over `T ⊆ ball u K
∩ ball x K` is bounded by `C² · (full bubble bound)`: the paper's standing two-point hypothesis
composes with the verified `bubble_bound`. This is the Appendix-B bubble estimate reduced to the
paper's root assumption (A) — as unconditional as the paper itself is. -/
theorem bubble_from_twopoint {d : ℕ} (hd : 2 ≤ d) (tau : (Fin d → ℤ) → (Fin d → ℤ) → ℝ)
    {C : ℝ} (hC : 0 ≤ C) (hA : TwoPointBound tau C)
    (x u : Fin d → ℤ) (K : ℕ) (T : Finset (Fin d → ℤ))
    (hTu : T ⊆ linfBall u (K : ℤ)) (hTx : T ⊆ linfBall x (K : ℤ)) :
    ∑ y ∈ T, tau x y * tau u y
      ≤ C ^ 2 * (2 * ((1 / ((linfDist x u / 2 + 1 : ℕ) : ℝ) ^ (d - 2))
            * (2 * (d : ℝ) * 3 ^ (d - 1) * ((K : ℝ) + 1) ^ 2))) := by
  calc ∑ y ∈ T, tau x y * tau u y
      ≤ ∑ y ∈ T, (C / ((linfDist x y + 1 : ℕ) : ℝ) ^ (d - 2))
            * (C / ((linfDist u y + 1 : ℕ) : ℝ) ^ (d - 2)) := by
        apply Finset.sum_le_sum
        intro y _
        exact mul_le_mul (hA x y).2 (hA u y).2 (hA u y).1 (div_nonneg hC (by positivity))
    _ = C ^ 2 * ∑ y ∈ T, (1 / ((linfDist x y + 1 : ℕ) : ℝ) ^ (d - 2))
            * (1 / ((linfDist u y + 1 : ℕ) : ℝ) ^ (d - 2)) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun y _ => by ring)
    _ ≤ C ^ 2 * (2 * ((1 / ((linfDist x u / 2 + 1 : ℕ) : ℝ) ^ (d - 2))
            * (2 * (d : ℝ) * 3 ^ (d - 1) * ((K : ℝ) + 1) ^ 2))) :=
        mul_le_mul_of_nonneg_left (bubble_bound hd x u K T hTu hTx) (by positivity)

end NearCritical.AppendixVariance
