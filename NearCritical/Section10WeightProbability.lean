module

public import NearCritical.Section10FlowMean

/-! Section10 prop.nw.main: the second-moment deduction of P[W>=1/2]>=1/8.
The source random weight and its first/second moment estimates remain to construct. -/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open scoped Classical BigOperators
variable {X : Type*} [Fintype X]

/-- The literal Paley--Zygmund step used in Section10, for a finite probability
law. The event is defined by W itself, rather than supplied as a success premise. -/
theorem good_weight_probability_ge_one_eighth (μ W : X → ℝ)
    (hμ : ∀ x, 0 ≤ μ x) (hprob : ∑ x, μ x = 1)
    (hW : ∀ x, 0 ≤ W x) (hmean : ∑ x, μ x*W x = 1)
    (hsecond : (∑ x, μ x*(W x)^2) ≤ 2) :
    (1/8:ℝ) ≤ ∑ x, if (1/2:ℝ) ≤ W x then μ x else 0 := by
  let A : Set X := {x | (1/2:ℝ) ≤ W x}
  let m : ℝ := ∑ x, if x ∈ A then μ x*W x else 0
  let q : ℝ := ∑ x, if x ∈ A then μ x else 0
  have hq : 0 ≤ q := by
    apply Finset.sum_nonneg
    intro x _
    split_ifs
    · exact hμ x
    · exact le_rfl
  have hm : (1/2:ℝ) ≤ m := by
    have hp (x : X) : μ x*W x ≤ μ x*(1/2:ℝ)+(if x ∈ A then μ x*W x else 0) := by
      by_cases hx : x ∈ A
      · simp only [if_pos hx]
        linarith [mul_nonneg (hμ x) (by norm_num : (0:ℝ) ≤ 1/2)]
      · have hw : W x ≤ (1/2:ℝ) := le_of_lt (lt_of_not_ge hx)
        simpa only [if_neg hx,add_zero] using mul_le_mul_of_nonneg_left hw (hμ x)
    have hh := Finset.sum_le_sum (fun x (_ : x ∈ (Finset.univ : Finset X)) => hp x)
    rw [Finset.sum_add_distrib,← Finset.sum_mul,hprob,hmean] at hh
    change (1:ℝ) ≤ 1*(1/2:ℝ)+m at hh
    linarith
  let r : X → ℝ := fun x => if x ∈ A then μ x*W x else 0
  let f : X → ℝ := fun x => μ x*(W x)^2
  let g : X → ℝ := fun x => if x ∈ A then μ x else 0
  have hf (x : X) : 0 ≤ f x := mul_nonneg (hμ x) (sq_nonneg _)
  have hg (x : X) : 0 ≤ g x := by
    dsimp [g]
    split_ifs
    · exact hμ x
    · exact le_rfl
  have hp (x : X) : (r x)^2 ≤ f x*g x := by
    by_cases hx : x ∈ A
    · simp only [r,f,g,if_pos hx]
      nlinarith
    · simp [r,g,hx]
  have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    (fun x _ => hf x) (fun x _ => hg x) (fun x _ => hp x)
  change m^2 ≤ (∑ x, μ x*(W x)^2)*q at hcs
  have hb : m^2 ≤ 2*q := hcs.trans (mul_le_mul_of_nonneg_right hsecond hq)
  change (1/8:ℝ) ≤ q
  nlinarith [sq_nonneg (m-(1/2:ℝ))]

end NearCritical.Section10
