module

public import NearCritical.Section9PivotalMeanUpper
public import NearCritical.Section9SeparatedTwoPoint
public import NearCritical.Section9CandidateCount
import Mathlib.Tactic.Positivity

/-! Explicit quantitative conditional mean envelope before power normalization. -/
@[expose] public section
noncomputable section
namespace NearCritical
open scoped Classical BigOperators

lemma section9FiniteMiddle_card_le {d : ℕ} (i : Fin d) (n : ℕ) :
    (section9FiniteMiddle i n).card ≤ (6*n+1)^d := by
  calc
    (section9FiniteMiddle i n).card ≤ (centeredBox d (3*n)).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    _ = (6*n+1)^d := by
      change (rectangularBox (fun _ : Fin d => 3*n)).card = _
      simp [card_rectangularBox, ← Nat.mul_assoc]

/-- Actual fixed-deletion conditional mean with uniform two-point bounds;
this helper is instantiated below from the existing asymptotics assumption. -/
theorem section9ConditionalMean_uniform_envelope {d : ℕ} (p : unitInterval)
    (S L R Q₁ H₁ F₁ Q₃ H₃ F₃ A B : Finset (Vertex d))
    (hH₁ : H₁ ⊆ Q₁) (hH₃ : H₃ ⊆ Q₃)
    (hLQ₃ : Disjoint L Q₃) (hRQ₁ : Disjoint R Q₁)
    (hpos : percolation d p (section9RevealEvent Q₁ H₁ Q₃ H₃ F₁ F₃) ≠ 0)
    (K : ℝ) (hK : 0 ≤ K)
    (hA : ∀ z ∈ S, ∀ x ∈ A, twoPoint d p z x ≤ K)
    (hB : ∀ z ∈ S, ∀ y ∈ B, twoPoint d p z y ≤ K) :
    section9PivotalMean (section9RevealedLaw p Q₁ H₁ Q₃ H₃ F₁ F₃)
      (orientedLatticePairs S) L R Q₁ F₁ Q₃ F₃ A B ≤
        ((2*(S.card*d):ℕ):ℝ) * (((A.card:ℝ)*K)*((B.card:ℝ)*K)) := by
  have hsum := section9ConditionalPivotalMean_le_twoPoint_sums p
    (orientedLatticePairs S) L R Q₁ H₁ F₁ Q₃ H₃ F₃ A B hH₁ hH₃ hLQ₃ hRQ₁ hpos
  have heach : ∀ e ∈ orientedLatticePairs S,
      (∑ x ∈ A, twoPoint d p e.1 x) * (∑ y ∈ B, twoPoint d p e.2 y) ≤
        ((A.card:ℝ)*K)*((B.card:ℝ)*K) := by
    intro e he
    obtain ⟨hl,hr,_⟩ := (mem_orientedLatticePairs S e.1 e.2).mp he
    have ha : (∑ x ∈ A, twoPoint d p e.1 x) ≤ (A.card:ℝ)*K := by
      simpa only [Finset.sum_const, nsmul_eq_mul] using
        Finset.sum_le_sum (fun x hx => hA e.1 hl x hx)
    have hb : (∑ y ∈ B, twoPoint d p e.2 y) ≤ (B.card:ℝ)*K := by
      simpa only [Finset.sum_const, nsmul_eq_mul] using
        Finset.sum_le_sum (fun y hy => hB e.2 hr y hy)
    exact mul_le_mul ha hb (Finset.sum_nonneg (fun _ _ => twoPoint_nonneg _ _ _))
      (mul_nonneg (Nat.cast_nonneg _) hK)
  have hbound := hsum.trans (Finset.sum_le_sum heach)
  have hcard : ((orientedLatticePairs S).card:ℝ) ≤ ((2*(S.card*d):ℕ):ℝ) := by
    exact_mod_cast orientedLatticePairs_card_le S
  have hbound' : section9PivotalMean (section9RevealedLaw p Q₁ H₁ Q₃ H₃ F₁ F₃)
      (orientedLatticePairs S) L R Q₁ F₁ Q₃ F₃ A B ≤
        ((orientedLatticePairs S).card:ℝ) * (((A.card:ℝ)*K)*((B.card:ℝ)*K)) := by
    simpa only [Finset.sum_const, nsmul_eq_mul] using hbound
  exact hbound'.trans (mul_le_mul_of_nonneg_right hcard (by positivity))

/-- One positive constant from source (A) gives an explicit scale envelope for
all actual finite source domains. No quantitative mean bound is a premise. -/
theorem section9ConditionalMean_source_envelope {d : ℕ} (hd : 2 ≤ d)
    (h : TwoPointAsymptotics d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (i : Fin d) (n : ℕ), 0 < n →
      ∀ (H₁ H₃ F₁ F₃ A B : Finset (Vertex d)),
      H₁ ⊆ section9FiniteEndCube i n 0 → H₃ ⊆ section9FiniteEndCube i n (2*(n:ℝ)) →
      A ⊆ section9FiniteEndCube i n 0 → B ⊆ section9FiniteEndCube i n (2*(n:ℝ)) →
      percolation d (criticalPoint d) (section9RevealEvent
        (section9FiniteEndCube i n 0) H₁ (section9FiniteEndCube i n (2*(n:ℝ))) H₃ F₁ F₃) ≠ 0 →
      let K := C * ((n:ℝ)/8)^((2:ℝ)-(d:ℝ))
      section9PivotalMean (section9RevealedLaw (criticalPoint d)
        (section9FiniteEndCube i n 0) H₁ (section9FiniteEndCube i n (2*(n:ℝ))) H₃ F₁ F₃)
        (orientedLatticePairs (section9FiniteMiddle i n))
        (section9FiniteTube i n (-(5:ℝ)/8) (3/8))
        (section9FiniteTube i n (-(3:ℝ)/8) (5/8))
        (section9FiniteEndCube i n 0) F₁ (section9FiniteEndCube i n (2*(n:ℝ))) F₃ A B ≤
        ((2*((6*n+1)^d*d):ℕ):ℝ) * (((A.card:ℝ)*K)*((B.card:ℝ)*K)) := by
  obtain ⟨C,hC,hb⟩ := section9TwoPoint_middle_end_bounds hd h
  refine ⟨C,hC,?_⟩
  intro i n hn H₁ H₃ F₁ F₃ A B hH₁ hH₃ hA hB hpos
  let K := C * ((n:ℝ)/8)^((2:ℝ)-(d:ℝ))
  have hK : 0 ≤ K := mul_nonneg hC.le (Real.rpow_nonneg (by positivity) _)
  have hu := section9ConditionalMean_uniform_envelope (criticalPoint d)
    (section9FiniteMiddle i n) _ _ _ H₁ F₁ _ H₃ F₃ A B hH₁ hH₃
    (section9FiniteLeftTube_disjoint_third i hn) (section9FiniteRightTube_disjoint_first i hn)
    hpos K hK
    (fun z hz x hx => hb i n hn z hz x (Or.inl (hA hx)))
    (fun z hz y hy => hb i n hn z hz y (Or.inr (hB hy)))
  have hc : 2*((section9FiniteMiddle i n).card*d) ≤ 2*((6*n+1)^d*d) :=
    Nat.mul_le_mul_left 2 (Nat.mul_le_mul_right d (section9FiniteMiddle_card_le i n))
  exact hu.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hc) (by positivity))

end NearCritical
