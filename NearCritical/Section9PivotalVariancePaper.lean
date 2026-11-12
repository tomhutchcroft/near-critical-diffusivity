module
public import NearCritical.Section9PivotalVarianceScale

/-! The literal four-group source bound for the conditioned pivotal variance. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory
open scoped Classical BigOperators

/-- Replace the truncated distance kernel by the paper's one-plus-distance
kernel, with one uniform dimensional factor. -/
theorem section9_max_kernel_le_one_add_kernel {d : ℕ} (hd : 9 ≤ d)
    (x y : Vertex d) :
    (max 1 (latticeDistance x y))^((8 : ℝ)-(d : ℝ)) ≤
      (2 : ℝ)^((d : ℝ)-8)*(1+latticeDistance x y)^((8 : ℝ)-(d : ℝ)) := by
  let m : ℝ := max 1 (latticeDistance x y)
  have hm : 0 ≤ m := zero_le_one.trans (le_max_left _ _)
  have hr : 0 ≤ latticeDistance x y := latticeDistance_nonneg x y
  have hdR : (9 : ℝ) ≤ d := by exact_mod_cast hd
  have hbase : 1+latticeDistance x y ≤ 2*m := by
    have h1 : 1 ≤ m := le_max_left _ _
    have h2 : latticeDistance x y ≤ m := le_max_right _ _
    linarith
  have hdecay : (2*m)^((8 : ℝ)-(d : ℝ)) ≤
      (1+latticeDistance x y)^((8 : ℝ)-(d : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos (by linarith) hbase (by linarith)
  have hfactor : (2 : ℝ)^((d : ℝ)-8)*(2 : ℝ)^((8 : ℝ)-(d : ℝ)) = 1 := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    have he : ((d : ℝ)-8)+(8-(d : ℝ)) = 0 := by ring
    rw [he,Real.rpow_zero]
  calc
    _ = (2 : ℝ)^((d : ℝ)-8)*(2*m)^((8 : ℝ)-(d : ℝ)) := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hm,← mul_assoc,hfactor,one_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left hdecay (Real.rpow_nonneg (by norm_num) _)

private theorem paper_variance_budget {C H O E T : ℝ}
    (hC : 0 ≤ C) (hH : 0 ≤ H) (hO : 0 ≤ O) (hE : 0 ≤ E) (hT : 0 ≤ T) :
    C*O+C*H*E ≤ (C*(1+H))*(O+E+T) := by
  have h₁ := mul_nonneg (mul_nonneg hC hH) hO
  have h₂ := mul_nonneg hC hE
  have h₃ := mul_nonneg (mul_nonneg hC (add_nonneg zero_le_one hH)) hT
  nlinarith only [h₁,h₂,h₃]

/-- Proposition var.pivAB in its literal four-group source form, for the
actual finite pivotal count under the revealed conditional law. -/
theorem section9_conditioned_pivotal_variance_paper_bound {d : ℕ} (hd : 9 ≤ d)
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
      (∫ ω, (section9PivotalCount E L R Q₁ F₁ Q₃ F₃ A B ω -
        section9PivotalMean ν E L R Q₁ F₁ Q₃ F₃ A B)^2 ∂ν) ≤
      C*((n : ℝ)^((10 : ℝ)-2*(d : ℝ))*
          ((A.card : ℝ)*(B.card : ℝ)^2+(A.card : ℝ)^2*(B.card : ℝ)) +
        ((n : ℝ)^((6 : ℝ)-2*(d : ℝ))+(n : ℝ)^((16 : ℝ)-3*(d : ℝ)))*
          (A.card : ℝ)^2*(B.card : ℝ)^2 +
        (A.card : ℝ)*(B.card : ℝ)*(n : ℝ)^((4 : ℝ)-(d : ℝ)) +
        (n : ℝ)^((8 : ℝ)-2*(d : ℝ))*
          ((B.card : ℝ)^2*(∑ x ∈ A, ∑ y ∈ A,
              (1+latticeDistance x y)^((8 : ℝ)-(d : ℝ))) +
           (A.card : ℝ)^2*(∑ x ∈ B, ∑ y ∈ B,
              (1+latticeDistance x y)^((8 : ℝ)-(d : ℝ))))) := by
  obtain ⟨C,hC,hbound⟩ := section9_conditioned_pivotal_variance_source_bound hd asymptotics
  let H : ℝ := (2 : ℝ)^((d : ℝ)-8)
  have hH : 0 ≤ H := Real.rpow_nonneg (by norm_num) _
  refine ⟨C*(1+H),mul_nonneg hC (add_nonneg zero_le_one hH),?_⟩
  intro i n hn L R Q₁ H₁ F₁ Q₃ H₃ F₃ A B hH₁ hH₃ hpos hLQ₃ hRQ₁ hL hR hA hB ν E
  let O : ℝ :=
    (n : ℝ)^((4 : ℝ)-(d : ℝ))*(A.card : ℝ)*(B.card : ℝ) +
    (n : ℝ)^((10 : ℝ)-2*(d : ℝ))*
      ((A.card : ℝ)*(B.card : ℝ)^2+(A.card : ℝ)^2*(B.card : ℝ)) +
    (n : ℝ)^((16 : ℝ)-3*(d : ℝ))*(A.card : ℝ)^2*(B.card : ℝ)^2
  let S := fun (D : Finset (Vertex d)) => ∑ x ∈ D, ∑ y ∈ D,
    (1+latticeDistance x y)^((8 : ℝ)-(d : ℝ))
  let P : ℝ := (n : ℝ)^((8 : ℝ)-2*(d : ℝ))*
    ((B.card : ℝ)^2*S A+(A.card : ℝ)^2*S B)
  let T : ℝ := (n : ℝ)^((6 : ℝ)-2*(d : ℝ))*(A.card : ℝ)^2*(B.card : ℝ)^2
  have hO : 0 ≤ O := by dsimp [O]; positivity
  have hS (D : Finset (Vertex d)) : 0 ≤ S D :=
    Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ =>
      Real.rpow_nonneg (by linarith [latticeDistance_nonneg x y]) _
  have hP : 0 ≤ P := mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)
    (add_nonneg (mul_nonneg (sq_nonneg _) (hS A)) (mul_nonneg (sq_nonneg _) (hS B)))
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hsum (D : Finset (Vertex d)) :
      (∑ x ∈ D, ∑ y ∈ D,
        (max 1 (latticeDistance x y))^((8 : ℝ)-(d : ℝ))) ≤ H*S D := by
    calc
      _ ≤ ∑ x ∈ D, ∑ y ∈ D,
          H*(1+latticeDistance x y)^((8 : ℝ)-(d : ℝ)) :=
        Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ =>
          section9_max_kernel_le_one_add_kernel hd x y
      _ = _ := by simp only [S,Finset.mul_sum]
  have hkernel :
      C*(n : ℝ)^((8 : ℝ)-2*(d : ℝ))*
        ((B.card : ℝ)^2*(∑ x ∈ A, ∑ y ∈ A,
            (max 1 (latticeDistance x y))^((8 : ℝ)-(d : ℝ))) +
         (A.card : ℝ)^2*(∑ x ∈ B, ∑ y ∈ B,
            (max 1 (latticeDistance x y))^((8 : ℝ)-(d : ℝ)))) ≤ C*H*P := by
    calc
      _ ≤ C*(n : ℝ)^((8 : ℝ)-2*(d : ℝ))*
          ((B.card : ℝ)^2*(H*S A)+(A.card : ℝ)^2*(H*S B)) :=
        mul_le_mul_of_nonneg_left
          (add_le_add (mul_le_mul_of_nonneg_left (hsum A) (sq_nonneg _))
            (mul_le_mul_of_nonneg_left (hsum B) (sq_nonneg _)))
          (mul_nonneg hC (Real.rpow_nonneg (Nat.cast_nonneg n) _))
      _ = _ := by dsimp [P]; ring
  have hb := hbound i n hn L R Q₁ H₁ F₁ Q₃ H₃ F₃ A B
    hH₁ hH₃ hpos hLQ₃ hRQ₁ hL hR hA hB
  calc
    _ ≤ C*O+C*H*P := hb.trans (add_le_add le_rfl hkernel)
    _ ≤ (C*(1+H))*(O+P+T) := paper_variance_budget hC hH hO hP hT
    _ = _ := by dsimp [O,P,T,S]; ring

end NearCritical
