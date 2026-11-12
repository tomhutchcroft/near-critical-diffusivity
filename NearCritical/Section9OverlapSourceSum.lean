module
public import NearCritical.Section9CrossOverlapScale
public import NearCritical.Section9OverlapSameLeftSum
public import NearCritical.Section9OverlapSameRight
public import NearCritical.Section9OverlapParallelSum

/-! Assemble all six original component-overlap patterns at source scale. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory
open scoped Classical BigOperators

private theorem overlap_pattern_sum_six (F : Section9OverlapPattern → ℝ) :
    (∑ k, F k) = F .singleLeft + F .parallel + F .leftRight +
      F .cross + F .rightLeft + F .singleRight := by
  change (∑ k ∈ ({.singleLeft,.parallel,.leftRight,.cross,.rightLeft,.singleRight} :
    Finset Section9OverlapPattern), F k) = _
  simp [add_assoc]

/-- The actual original-overlap probability double sum is bounded by
its six exact matching-pattern probability double sums, including the diagonal. -/
theorem section9_overlap_sum_le_six_pattern_sums {d : ℕ}
    (ν : Measure (Configuration d)) [IsFiniteMeasure ν]
    (E : Finset (Vertex d × Vertex d))
    (L R Q₁ F₁ Q₃ F₃ A B : Finset (Vertex d)) :
    (∑ e ∈ E, ∑ f ∈ E,
      ν.real (section9CovarianceOverlapEvent L R Q₁ F₁ Q₃ F₃ A B e f)) ≤
    (∑ e ∈ E, ∑ f ∈ E,
      ν.real (section9OverlapPatternEvent .singleLeft L R Q₁ F₁ Q₃ F₃ A B e f)) +
    (∑ e ∈ E, ∑ f ∈ E,
      ν.real (section9OverlapPatternEvent .parallel L R Q₁ F₁ Q₃ F₃ A B e f)) +
    (∑ e ∈ E, ∑ f ∈ E,
      ν.real (section9OverlapPatternEvent .leftRight L R Q₁ F₁ Q₃ F₃ A B e f)) +
    (∑ e ∈ E, ∑ f ∈ E,
      ν.real (section9OverlapPatternEvent .cross L R Q₁ F₁ Q₃ F₃ A B e f)) +
    (∑ e ∈ E, ∑ f ∈ E,
      ν.real (section9OverlapPatternEvent .rightLeft L R Q₁ F₁ Q₃ F₃ A B e f)) +
    (∑ e ∈ E, ∑ f ∈ E,
      ν.real (section9OverlapPatternEvent .singleRight L R Q₁ F₁ Q₃ F₃ A B e f)) := by
  calc
    _ ≤ ∑ e ∈ E, ∑ f ∈ E,
        ∑ k : Section9OverlapPattern,
          ν.real (section9OverlapPatternEvent k L R Q₁ F₁ Q₃ F₃ A B e f) := by
      apply Finset.sum_le_sum
      intro e _
      apply Finset.sum_le_sum
      intro f _
      exact (measureReal_mono
        (section9_covariance_overlap_pattern_cover L R Q₁ F₁ Q₃ F₃ A B e f)
        (measure_ne_top _ _)).trans
        (measureReal_iUnion_fintype_le
          (fun k => section9OverlapPatternEvent k L R Q₁ F₁ Q₃ F₃ A B e f))
    _ = _ := by
      simp_rw [overlap_pattern_sum_six]
      simp only [Finset.sum_add_distrib]

private theorem overlap_six_budget {C₁ C₂ C₃ C₄ C₅ C₆ x y z w : ℝ}
    (h₁ : 0 ≤ C₁) (h₂ : 0 ≤ C₂) (h₃ : 0 ≤ C₃)
    (h₄ : 0 ≤ C₄) (h₅ : 0 ≤ C₅) (h₆ : 0 ≤ C₆)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (hw : 0 ≤ w) :
    C₁*y+C₂*x+C₃*w+C₄*w+C₅*w+C₆*z ≤
      (C₁+C₂+C₃+C₄+C₅+C₆)*(x+(y+z)+w) := by
  let C := C₁+C₂+C₃+C₄+C₅+C₆
  have hCx : C₂ ≤ C := by dsimp [C]; linarith
  have hCy : C₁ ≤ C := by dsimp [C]; linarith
  have hCz : C₆ ≤ C := by dsimp [C]; linarith
  have hCw : C₃+C₄+C₅ ≤ C := by dsimp [C]; linarith
  calc
    _ = C₂*x+(C₁*y+C₆*z)+(C₃+C₄+C₅)*w := by ring
    _ ≤ C*x+(C*y+C*z)+C*w :=
      add_le_add (add_le_add (mul_le_mul_of_nonneg_right hCx hx)
        (add_le_add (mul_le_mul_of_nonneg_right hCy hy)
          (mul_le_mul_of_nonneg_right hCz hz)))
        (mul_le_mul_of_nonneg_right hCw hw)
    _ = _ := by dsimp [C]; ring

/-- The full original conditional overlap sum has the three source scales
obtained by assembling all six exact matching patterns. -/
theorem section9_conditioned_overlap_source_sum_bound {d : ℕ} (hd : 9 ≤ d)
    (asymptotics : TwoPointAsymptotics d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (i : Fin d) (n : ℕ), 0 < n →
      ∀ (L R Q₁ H₁ F₁ Q₃ H₃ F₃ A B : Finset (Vertex d)),
      H₁ ⊆ Q₁ → H₃ ⊆ Q₃ →
      percolation d (criticalPoint d) (section9RevealEvent Q₁ H₁ Q₃ H₃ F₁ F₃) ≠ 0 →
      Disjoint L Q₃ → Disjoint R Q₁ →
      L ⊆ centeredBox d (3*n) → R ⊆ centeredBox d (3*n) →
      A ⊆ section9FiniteEndCube i n 0 → B ⊆ section9FiniteEndCube i n (2*(n:ℝ)) →
      let ν := section9RevealedLaw (criticalPoint d) Q₁ H₁ Q₃ H₃ F₁ F₃
      let E := orientedLatticePairs (section9FiniteMiddle i n)
      (∑ e ∈ E, ∑ f ∈ E,
        ν.real (section9CovarianceOverlapEvent L R Q₁ F₁ Q₃ F₃ A B e f)) ≤
      C*((n : ℝ)^((4 : ℝ)-(d : ℝ))*(A.card : ℝ)*(B.card : ℝ) +
        (n : ℝ)^((10 : ℝ)-2*(d : ℝ))*
          ((A.card : ℝ)*(B.card : ℝ)^2+(A.card : ℝ)^2*(B.card : ℝ)) +
        (n : ℝ)^((16 : ℝ)-3*(d : ℝ))*(A.card : ℝ)^2*(B.card : ℝ)^2) := by
  obtain ⟨C₁,hC₁,bound₁⟩ := section9_single_left_pattern_source_sum_bound hd asymptotics
  obtain ⟨C₂,hC₂,bound₂⟩ := section9_parallel_overlap_source_sum_bound hd asymptotics
  obtain ⟨C₃,hC₃,bound₃⟩ := section9_left_right_pattern_source_sum_bound hd asymptotics
  obtain ⟨C₄,hC₄,bound₄⟩ := section9_cross_pattern_source_sum_bound hd asymptotics
  obtain ⟨C₅,hC₅,bound₅⟩ := section9_right_left_pattern_source_sum_bound hd asymptotics
  obtain ⟨C₆,hC₆,bound₆⟩ := section9_single_right_pattern_source_sum_bound hd asymptotics
  refine ⟨C₁+C₂+C₃+C₄+C₅+C₆,by linarith,?_⟩
  intro i n hn L R Q₁ H₁ F₁ Q₃ H₃ F₃ A B hH₁ hH₃ hpos hLQ₃ hRQ₁ hL hR hA hB ν E
  letI : IsProbabilityMeasure ν := section9RevealedLaw_isProbability (criticalPoint d)
    Q₁ H₁ Q₃ H₃ F₁ F₃ hpos
  let x : ℝ := (n : ℝ)^((4 : ℝ)-(d : ℝ))*(A.card : ℝ)*(B.card : ℝ)
  let y : ℝ := (n : ℝ)^((10 : ℝ)-2*(d : ℝ))*(A.card : ℝ)*(B.card : ℝ)^2
  let z : ℝ := (n : ℝ)^((10 : ℝ)-2*(d : ℝ))*(A.card : ℝ)^2*(B.card : ℝ)
  let w : ℝ := (n : ℝ)^((16 : ℝ)-3*(d : ℝ))*(A.card : ℝ)^2*(B.card : ℝ)^2
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have hy : 0 ≤ y := by dsimp [y]; positivity
  have hz : 0 ≤ z := by dsimp [z]; positivity
  have hw : 0 ≤ w := by dsimp [w]; positivity
  have hpow : (n : ℝ)^((14 : ℝ)-3*(d : ℝ)) ≤
      (n : ℝ)^((16 : ℝ)-3*(d : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) (by linarith)
  have hmono (C : ℝ) (hC : 0 ≤ C) :
      C*(n : ℝ)^((14 : ℝ)-3*(d : ℝ))*(A.card : ℝ)^2*(B.card : ℝ)^2 ≤ C*w := by
    have hh := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hC)
        (sq_nonneg (A.card : ℝ))) (sq_nonneg (B.card : ℝ))
    simpa only [w,mul_assoc] using hh
  have h₁ := bound₁ i n hn L R Q₁ H₁ F₁ Q₃ H₃ F₃ A B
    hH₁ hH₃ hpos hLQ₃ hRQ₁ hL hA hB
  have h₂ := bound₂ i n hn L R Q₁ H₁ F₁ Q₃ H₃ F₃ A B
    hH₁ hH₃ hpos hLQ₃ hRQ₁ hA hB
  have h₃ := (bound₃ i n hn L R Q₁ H₁ F₁ Q₃ H₃ F₃ A B
    hH₁ hH₃ hpos hLQ₃ hRQ₁ hL hR hA hB).trans (hmono C₃ hC₃)
  have h₄ := bound₄ i n hn L R Q₁ H₁ F₁ Q₃ H₃ F₃ A B
    hH₁ hH₃ hpos hLQ₃ hRQ₁ hL hR hA hB
  have h₅ := (bound₅ i n hn L R Q₁ H₁ F₁ Q₃ H₃ F₃ A B
    hH₁ hH₃ hpos hLQ₃ hRQ₁ hL hR hA hB).trans (hmono C₅ hC₅)
  have h₆ := bound₆ i n hn L R Q₁ H₁ F₁ Q₃ H₃ F₃ A B
    hH₁ hH₃ hpos hLQ₃ hRQ₁ hR hA hB
  have htotal := add_le_add (add_le_add (add_le_add (add_le_add (add_le_add h₁ h₂) h₃) h₄) h₅) h₆
  have hnormalized :
      (∑ e ∈ E, ∑ f ∈ E,
        ν.real (section9CovarianceOverlapEvent L R Q₁ F₁ Q₃ F₃ A B e f)) ≤
      C₁*y+C₂*x+C₃*w+C₄*w+C₅*w+C₆*z := by
    have hh := (section9_overlap_sum_le_six_pattern_sums ν E L R Q₁ F₁ Q₃ F₃ A B).trans htotal
    simpa only [x,y,z,w,mul_assoc] using hh
  calc
    _ ≤ C₁*y+C₂*x+C₃*w+C₄*w+C₅*w+C₆*z := hnormalized
    _ ≤ (C₁+C₂+C₃+C₄+C₅+C₆)*(x+(y+z)+w) :=
      overlap_six_budget hC₁ hC₂ hC₃ hC₄ hC₅ hC₆ hx hy hz hw
    _ = _ := by dsimp [x,y,z,w]; ring

end NearCritical
