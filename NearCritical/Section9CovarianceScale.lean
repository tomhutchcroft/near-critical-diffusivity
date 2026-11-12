module
public import NearCritical.Section9CollisionScale
public import NearCritical.Section9PivotalVariance

/-! Source-scale replacement estimates in the actual conditional pivot-count
variance. The original-overlap probability sum remains to be estimated. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory
open scoped Classical BigOperators

/-- The full replacement branch of the conditional pivotal variance has the
source same-side and mixed scales. The original-overlap double sum is kept
as its actual probability expression, not assumed quantitatively bounded. -/
theorem section9_conditioned_pivotal_variance_replacement_source_bound {d : ℕ} (hd : 9 ≤ d)
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
      (∑ e ∈ E, ∑ f ∈ E, ν.real (section9CovarianceOverlapEvent L R Q₁ F₁ Q₃ F₃ A B e f)) +
      C*(n : ℝ)^((8 : ℝ)-2*(d : ℝ)) *
        ((B.card : ℝ)^2 * (∑ x ∈ A, ∑ y ∈ A,
            (max 1 (latticeDistance x y))^((8 : ℝ)-(d : ℝ))) +
         (A.card : ℝ)^2 * (∑ x ∈ B, ∑ y ∈ B,
            (max 1 (latticeDistance x y))^((8 : ℝ)-(d : ℝ)))) +
      C*(n : ℝ)^((16 : ℝ)-3*(d : ℝ))*(A.card : ℝ)^2*(B.card : ℝ)^2 := by
  obtain ⟨Ks,hKs,hsame⟩ := section9_all_collision_products_source_bound hd asymptotics
  obtain ⟨Km,hKm,hmixed⟩ := section9_mixed_collision_products_source_bound hd asymptotics
  let C := Ks+2*Km
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro i n hn L R Q₁ H₁ F₁ Q₃ H₃ F₃ A B hH₁ hH₃ hpos hLQ₃ hRQ₁ hL hR hA hB ν E
  letI : IsProbabilityMeasure ν := section9RevealedLaw_isProbability (criticalPoint d)
    Q₁ H₁ Q₃ H₃ F₁ F₃ hpos
  let P := fun s t => section9CollisionProduct ν E L R Q₁ F₁ Q₃ F₃ A B (L ∪ R) s t
  let na := (n : ℝ)^((8 : ℝ)-2*(d : ℝ))
  let nb := (n : ℝ)^((16 : ℝ)-3*(d : ℝ))
  let SA := ∑ x ∈ A, ∑ y ∈ A, (max 1 (latticeDistance x y))^((8 : ℝ)-(d : ℝ))
  let SB := ∑ x ∈ B, ∑ y ∈ B, (max 1 (latticeDistance x y))^((8 : ℝ)-(d : ℝ))
  let X := na*((B.card : ℝ)^2*SA+(A.card : ℝ)^2*SB)
  let Y := nb*(A.card : ℝ)^2*(B.card : ℝ)^2
  have hSA : 0 ≤ SA := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    Real.rpow_nonneg (zero_le_one.trans (le_max_left _ _)) _
  have hSB : 0 ≤ SB := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    Real.rpow_nonneg (zero_le_one.trans (le_max_left _ _)) _
  have hX : 0 ≤ X := mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)
    (add_nonneg (mul_nonneg (sq_nonneg _) hSA) (mul_nonneg (sq_nonneg _) hSB))
  have hY : 0 ≤ Y := mul_nonneg
    (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _) (sq_nonneg _)) (sq_nonneg _)
  have hff : P false false ≤ Ks*na*(B.card : ℝ)*(B.card : ℝ)*SA := by
    simpa [P,na,SA] using hsame i n hn L R Q₁ H₁ F₁ Q₃ H₃ F₃ A B (L ∪ R)
      hH₁ hH₃ hpos hLQ₃ hRQ₁ hL hR hA hB false false
  have htt : P true true ≤ Ks*na*(A.card : ℝ)*(A.card : ℝ)*SB := by
    simpa [P,na,SB] using hsame i n hn L R Q₁ H₁ F₁ Q₃ H₃ F₃ A B (L ∪ R)
      hH₁ hH₃ hpos hLQ₃ hRQ₁ hL hR hA hB true true
  have hft : P false true ≤ Km*nb*(A.card : ℝ)^2*(B.card : ℝ)^2 := by
    simpa [P,nb] using hmixed i n hn L R Q₁ H₁ F₁ Q₃ H₃ F₃ A B (L ∪ R)
      hH₁ hH₃ hpos hLQ₃ hRQ₁ hL hR hA hB false
  have htf : P true false ≤ Km*nb*(A.card : ℝ)^2*(B.card : ℝ)^2 := by
    simpa [P,nb] using hmixed i n hn L R Q₁ H₁ F₁ Q₃ H₃ F₃ A B (L ∪ R)
      hH₁ hH₃ hpos hLQ₃ hRQ₁ hL hR hA hB true
  have hSame : P false false + P true true ≤ Ks*X := by
    calc
      _ ≤ Ks*na*(B.card : ℝ)*(B.card : ℝ)*SA +
          Ks*na*(A.card : ℝ)*(A.card : ℝ)*SB := add_le_add hff htt
      _ = _ := by dsimp [X]; ring
  have hMixed : P false true + P true false ≤ (2*Km)*Y := by
    calc
      _ ≤ Km*nb*(A.card : ℝ)^2*(B.card : ℝ)^2 +
          Km*nb*(A.card : ℝ)^2*(B.card : ℝ)^2 := add_le_add hft htf
      _ = _ := by dsimp [Y]; ring
  have hProducts : P false false + P false true + P true false + P true true ≤ C*X+C*Y := by
    calc
      _ = (P false false+P true true)+(P false true+P true false) := by ring
      _ ≤ Ks*X+(2*Km)*Y := add_le_add hSame hMixed
      _ ≤ C*X+C*Y := add_le_add
        (mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) hX)
        (mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) hY)
  have hcov := section9_conditioned_covariance_sum_four_products_le (criticalPoint d) E
    L R Q₁ H₁ F₁ Q₃ H₃ F₃ A B hH₁ hH₃ hpos hLQ₃ hRQ₁
  dsimp only at hcov
  calc
    _ = ∑ e ∈ E, ∑ f ∈ E, section9PivotalCovariance ν L R Q₁ F₁ Q₃ F₃ A B e f :=
      section9PivotalCount_covariance_identity ν E L R Q₁ F₁ Q₃ F₃ A B
    _ ≤ (∑ e ∈ E, ∑ f ∈ E, ν.real (section9CovarianceOverlapEvent L R Q₁ F₁ Q₃ F₃ A B e f)) +
        (P false false+P false true+P true false+P true true) := by
      simpa only [section9PivotalCovariance,section9PivotalJointProbability,
        section9PivotalProbability,P] using hcov
    _ ≤ (∑ e ∈ E, ∑ f ∈ E, ν.real (section9CovarianceOverlapEvent L R Q₁ F₁ Q₃ F₃ A B e f)) +
        (C*X+C*Y) := add_le_add le_rfl hProducts
    _ = _ := by dsimp [X,Y,na,nb,SA,SB]; ring

end NearCritical
