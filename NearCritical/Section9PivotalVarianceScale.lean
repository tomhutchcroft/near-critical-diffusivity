module
public import NearCritical.Section9OverlapSourceSum
public import NearCritical.Section9CovarianceScale

/-! Actual source-scale pivotal variance, combining both proved branches. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory
open scoped Classical BigOperators

/-- Quantitative variance of the actual conditioned pivot count. All original
and replacement overlap estimates are discharged from two-point asymptotics. -/
theorem section9_conditioned_pivotal_variance_source_bound {d : ℕ} (hd : 9 ≤ d)
    (asymptotics : TwoPointAsymptotics d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (i : Fin d) (n : ℕ), 0 < n →
      ∀ (L R Q₁ H₁ F₁ Q₃ H₃ F₃ A B : Finset (Vertex d)),
      H₁ ⊆ Q₁ → H₃ ⊆ Q₃ →
      percolation d (criticalPoint d) (section9RevealEvent Q₁ H₁ Q₃ H₃ F₁ F₃) ≠ 0 →
      Disjoint L Q₃ → Disjoint R Q₁ → L ⊆ centeredBox d (3*n) → R ⊆ centeredBox d (3*n) →
      A ⊆ section9FiniteEndCube i n 0 → B ⊆ section9FiniteEndCube i n (2*(n:ℝ)) →
      let ν := section9RevealedLaw (criticalPoint d) Q₁ H₁ Q₃ H₃ F₁ F₃
      let E := orientedLatticePairs (section9FiniteMiddle i n)
      (∫ ω, (section9PivotalCount E L R Q₁ F₁ Q₃ F₃ A B ω -
        section9PivotalMean ν E L R Q₁ F₁ Q₃ F₃ A B)^2 ∂ν) ≤
      C*((n : ℝ)^((4 : ℝ)-(d : ℝ))*(A.card : ℝ)*(B.card : ℝ) +
        (n : ℝ)^((10 : ℝ)-2*(d : ℝ))*
          ((A.card : ℝ)*(B.card : ℝ)^2+(A.card : ℝ)^2*(B.card : ℝ)) +
        (n : ℝ)^((16 : ℝ)-3*(d : ℝ))*(A.card : ℝ)^2*(B.card : ℝ)^2) +
      C*(n : ℝ)^((8 : ℝ)-2*(d : ℝ)) *
        ((B.card : ℝ)^2 * (∑ x ∈ A, ∑ y ∈ A,
            (max 1 (latticeDistance x y))^((8 : ℝ)-(d : ℝ))) +
         (A.card : ℝ)^2 * (∑ x ∈ B, ∑ y ∈ B,
            (max 1 (latticeDistance x y))^((8 : ℝ)-(d : ℝ)))) := by
  obtain ⟨Ko,hKo,hOverlap⟩ := section9_conditioned_overlap_source_sum_bound hd asymptotics
  obtain ⟨Kr,hKr,hReplacement⟩ :=
    section9_conditioned_pivotal_variance_replacement_source_bound hd asymptotics
  refine ⟨Ko+Kr,add_nonneg hKo hKr,?_⟩
  intro i n hn L R Q₁ H₁ F₁ Q₃ H₃ F₃ A B hH₁ hH₃ hpos hLQ₃ hRQ₁ hL hR hA hB ν E
  have ho := hOverlap i n hn L R Q₁ H₁ F₁ Q₃ H₃ F₃ A B
    hH₁ hH₃ hpos hLQ₃ hRQ₁ hL hR hA hB
  have hr := hReplacement i n hn L R Q₁ H₁ F₁ Q₃ H₃ F₃ A B
    hH₁ hH₃ hpos hLQ₃ hRQ₁ hL hR hA hB
  dsimp only at ho hr
  have hsA : 0 ≤ ∑ x ∈ A, ∑ y ∈ A,
      (max 1 (latticeDistance x y))^((8 : ℝ)-(d : ℝ)) :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
      Real.rpow_nonneg (zero_le_one.trans (le_max_left _ _)) _
  have hsB : 0 ≤ ∑ x ∈ B, ∑ y ∈ B,
      (max 1 (latticeDistance x y))^((8 : ℝ)-(d : ℝ)) :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
      Real.rpow_nonneg (zero_le_one.trans (le_max_left _ _)) _
  have h4 := Real.rpow_nonneg (Nat.cast_nonneg n) ((4 : ℝ)-(d : ℝ))
  have h10 := Real.rpow_nonneg (Nat.cast_nonneg n) ((10 : ℝ)-2*(d : ℝ))
  have h16 := Real.rpow_nonneg (Nat.cast_nonneg n) ((16 : ℝ)-3*(d : ℝ))
  have h8 := Real.rpow_nonneg (Nat.cast_nonneg n) ((8 : ℝ)-2*(d : ℝ))
  have hA0 : (0 : ℝ) ≤ A.card := Nat.cast_nonneg _
  have hB0 : (0 : ℝ) ≤ B.card := Nat.cast_nonneg _
  nlinarith only [hr,ho,hKo,hKr,
    mul_nonneg hKr (mul_nonneg (mul_nonneg h4 hA0) hB0),
    mul_nonneg hKr (mul_nonneg h10
      (add_nonneg (mul_nonneg hA0 (sq_nonneg (B.card : ℝ))) (mul_nonneg (sq_nonneg (A.card : ℝ)) hB0))),
    mul_nonneg hKr (mul_nonneg (mul_nonneg h16 (sq_nonneg (A.card : ℝ))) (sq_nonneg (B.card : ℝ))),
    mul_nonneg hKo (mul_nonneg h8
      (add_nonneg (mul_nonneg (sq_nonneg (B.card : ℝ)) hsA)
        (mul_nonneg (sq_nonneg (A.card : ℝ)) hsB))),
    mul_nonneg hKo (mul_nonneg (mul_nonneg h16 (sq_nonneg (A.card : ℝ))) (sq_nonneg (B.card : ℝ)))]

end NearCritical
