module

public import NearCritical.Section9MeanEnvelope
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-! Quantitative upper mean scale for the actual finite open-coordinate model.
Source face conventions and all lower/variance estimates remain separate. -/
@[expose] public section
noncomputable section
namespace NearCritical
open scoped Classical

lemma section9MeanEnvelope_normalize (d : ℕ) (n C a b : ℝ)
    (hn : 1 ≤ n) (hC : 0 ≤ C) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    2*(6*n+1)^d*(d:ℝ)*((a*(C*(n/8)^((2:ℝ)-(d:ℝ))))*
      (b*(C*(n/8)^((2:ℝ)-(d:ℝ))))) ≤
    (2*(d:ℝ)*(7:ℝ)^d*(C*(1/8:ℝ)^((2:ℝ)-(d:ℝ)))^2)*
      n^((4:ℝ)-(d:ℝ))*a*b := by
  have hnpos : 0 < n := lt_of_lt_of_le zero_lt_one hn
  let q : ℝ := (2:ℝ)-(d:ℝ)
  have hdiv : (n/8)^q = n^q*(1/8:ℝ)^q := by
    simpa only [div_eq_mul_inv, one_mul] using
      (Real.mul_rpow hnpos.le (show 0 ≤ (8:ℝ)⁻¹ by positivity) (z := q))
  have hp : n^(d:ℝ)*(n^q)^2 = n^((4:ℝ)-(d:ℝ)) := by
    calc
      n^(d:ℝ)*(n^q)^2 = n^(d:ℝ)*n^(q*2) := by
        rw [Real.rpow_mul hnpos.le, Real.rpow_two]
      _ = n^((d:ℝ)+q*2) := (Real.rpow_add hnpos _ _).symm
      _ = n^((4:ℝ)-(d:ℝ)) := by congr 1; dsimp [q]; ring
  have hvol : (6*n+1)^d ≤ (7:ℝ)^d*n^d := by
    calc
      (6*n+1)^d ≤ (7*n)^d := by gcongr <;> nlinarith
      _ = _ := mul_pow _ _ _
  change 2*(6*n+1)^d*(d:ℝ)*((a*(C*(n/8)^q))*(b*(C*(n/8)^q))) ≤ _
  calc
    _ ≤ 2*((7:ℝ)^d*n^d)*(d:ℝ)*((a*(C*(n/8)^q))*(b*(C*(n/8)^q))) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hvol (by norm_num))
          (Nat.cast_nonneg d)) (by positivity)
    _ = (2*(d:ℝ)*(7:ℝ)^d*(C*(1/8:ℝ)^q)^2)*(n^(d:ℝ)*(n^q)^2)*a*b := by
      simp only [hdiv, Real.rpow_natCast]
      ring
    _ = _ := by rw [hp]

/-- Actual conditional pivot mean has the source n^(4-d)|A||B| upper scale,
with one positive constant for all positive integer scales and target sets.
The model here uses the existing explicit open-coordinate finite shapes. -/
theorem section9ConditionalMean_upper_scale {d : ℕ} (hd : 2 ≤ d)
    (h : TwoPointAsymptotics d) :
    ∃ D : ℝ, 0 < D ∧ ∀ (i : Fin d) (n : ℕ), 0 < n →
      ∀ (H₁ H₃ F₁ F₃ A B : Finset (Vertex d)),
      H₁ ⊆ section9FiniteEndCube i n 0 → H₃ ⊆ section9FiniteEndCube i n (2*(n:ℝ)) →
      A ⊆ section9FiniteEndCube i n 0 → B ⊆ section9FiniteEndCube i n (2*(n:ℝ)) →
      percolation d (criticalPoint d) (section9RevealEvent
        (section9FiniteEndCube i n 0) H₁ (section9FiniteEndCube i n (2*(n:ℝ))) H₃ F₁ F₃) ≠ 0 →
      section9PivotalMean (section9RevealedLaw (criticalPoint d)
        (section9FiniteEndCube i n 0) H₁ (section9FiniteEndCube i n (2*(n:ℝ))) H₃ F₁ F₃)
        (orientedLatticePairs (section9FiniteMiddle i n))
        (section9FiniteTube i n (-(5:ℝ)/8) (3/8))
        (section9FiniteTube i n (-(3:ℝ)/8) (5/8))
        (section9FiniteEndCube i n 0) F₁ (section9FiniteEndCube i n (2*(n:ℝ))) F₃ A B ≤
        D*(n:ℝ)^((4:ℝ)-(d:ℝ))*(A.card:ℝ)*(B.card:ℝ) := by
  obtain ⟨C,hC,hbound⟩ := section9ConditionalMean_source_envelope hd h
  let D : ℝ := 2*(d:ℝ)*(7:ℝ)^d*(C*(1/8:ℝ)^((2:ℝ)-(d:ℝ)))^2
  have hdpos : (0:ℝ) < d := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hd)
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨D,hD,?_⟩
  intro i n hn H₁ H₃ F₁ F₃ A B hH₁ hH₃ hA hB hpos
  have hu := hbound i n hn H₁ H₃ F₁ F₃ A B hH₁ hH₃ hA hB hpos
  have hnNat : 1 ≤ n := hn
  have hnreal : (1:ℝ) ≤ n := by exact_mod_cast hnNat
  have halg := section9MeanEnvelope_normalize d (n:ℝ) C (A.card:ℝ) (B.card:ℝ)
    hnreal hC.le (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  apply hu.trans
  simpa only [D, Nat.cast_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one, mul_assoc] using halg

end NearCritical
