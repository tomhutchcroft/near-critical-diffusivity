module

public import NearCritical.Section9PivotalMoments
import Mathlib.Tactic.Linarith

/-! Section9, opening calculation of prop.var.pivAB. Actual pivot covariances
are computed from actual single and joint probabilities. This proves the
algebraic variance decomposition and diagonal bound, not the subsequent
conditional resampling/diagram estimates. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory
open scoped Classical BigOperators

/-- Actual one-pivot probability under the specified configuration law. -/
def section9PivotalProbability {d : ℕ} (μ : Measure (Configuration d))
    (L R Q₁ F₁ Q₃ F₃ A B : Finset (Vertex d)) (e : Vertex d × Vertex d) : ℝ :=
  μ.real {ω | sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ A B e}

/-- Actual joint pivot probability; no independence is inserted. -/
def section9PivotalJointProbability {d : ℕ} (μ : Measure (Configuration d))
    (L R Q₁ F₁ Q₃ F₃ A B : Finset (Vertex d)) (e f : Vertex d × Vertex d) : ℝ :=
  μ.real {ω | sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ A B e ∧
    sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ A B f}

/-- The covariance appearing in the source's ordered-pair sum. -/
def section9PivotalCovariance {d : ℕ} (μ : Measure (Configuration d))
    (L R Q₁ F₁ Q₃ F₃ A B : Finset (Vertex d)) (e f : Vertex d × Vertex d) : ℝ :=
  section9PivotalJointProbability μ L R Q₁ F₁ Q₃ F₃ A B e f -
    section9PivotalProbability μ L R Q₁ F₁ Q₃ F₃ A B e *
      section9PivotalProbability μ L R Q₁ F₁ Q₃ F₃ A B f

lemma section9PivotalCovariance_diagonal {d : ℕ} (μ : Measure (Configuration d))
    (L R Q₁ F₁ Q₃ F₃ A B : Finset (Vertex d)) (e : Vertex d × Vertex d) :
    section9PivotalCovariance μ L R Q₁ F₁ Q₃ F₃ A B e e =
      section9PivotalProbability μ L R Q₁ F₁ Q₃ F₃ A B e -
        (section9PivotalProbability μ L R Q₁ F₁ Q₃ F₃ A B e)^2 := by
  simp [section9PivotalCovariance, section9PivotalJointProbability,
    section9PivotalProbability, pow_two]

/-- The diagonal contribution is bounded by the actual one-edge probability,
not by the number of candidates. Off-diagonal covariance is retained exactly. -/
lemma section9PivotalCovariance_diagonal_split {d : ℕ} (μ : Measure (Configuration d))
    (L R Q₁ F₁ Q₃ F₃ A B : Finset (Vertex d)) (e f : Vertex d × Vertex d) :
    section9PivotalCovariance μ L R Q₁ F₁ Q₃ F₃ A B e f ≤
      (if e = f then section9PivotalProbability μ L R Q₁ F₁ Q₃ F₃ A B e else 0) +
      (if e = f then 0 else section9PivotalCovariance μ L R Q₁ F₁ Q₃ F₃ A B e f) := by
  by_cases hef : e = f
  · subst f
    rw [section9PivotalCovariance_diagonal]
    simp only [↓reduceIte, add_zero]
    nlinarith [sq_nonneg (section9PivotalProbability μ L R Q₁ F₁ Q₃ F₃ A B e)]
  · simp [hef]

/-- Exact variance decomposition for the actual pivot count under a probability
law. Every summand is the covariance of two actual canonical pivot events. -/
theorem section9PivotalCount_covariance_identity {d : ℕ} (μ : Measure (Configuration d))
    [IsProbabilityMeasure μ] (E : Finset (Vertex d × Vertex d))
    (L R Q₁ F₁ Q₃ F₃ A B : Finset (Vertex d)) :
    (∫ ω, (section9PivotalCount E L R Q₁ F₁ Q₃ F₃ A B ω -
      section9PivotalMean μ E L R Q₁ F₁ Q₃ F₃ A B)^2 ∂μ) =
      ∑ e ∈ E, ∑ f ∈ E, section9PivotalCovariance μ L R Q₁ F₁ Q₃ F₃ A B e f := by
  have hmean : section9PivotalMean μ E L R Q₁ F₁ Q₃ F₃ A B =
      ∑ e ∈ E, section9PivotalProbability μ L R Q₁ F₁ Q₃ F₃ A B e :=
    integral_section9PivotalCount μ E L R Q₁ F₁ Q₃ F₃ A B
  have hprod : (∑ e ∈ E, ∑ f ∈ E,
      section9PivotalProbability μ L R Q₁ F₁ Q₃ F₃ A B e *
        section9PivotalProbability μ L R Q₁ F₁ Q₃ F₃ A B f) =
      (∑ e ∈ E, section9PivotalProbability μ L R Q₁ F₁ Q₃ F₃ A B e)^2 := by
    rw [pow_two, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro e _
    rw [Finset.mul_sum]
  rw [section9PivotalCount_centered_identity, integral_section9PivotalCount_sq, hmean]
  simp only [section9PivotalCovariance, Finset.sum_sub_distrib]
  rw [hprod]
  simp only [section9PivotalJointProbability]

/-- Source opening bound Var(#piv) <= actual mean + ordered off-diagonal
covariances, derived without a supplied variance or covariance estimate. -/
theorem section9PivotalCount_variance_le {d : ℕ} (μ : Measure (Configuration d))
    [IsProbabilityMeasure μ] (E : Finset (Vertex d × Vertex d))
    (L R Q₁ F₁ Q₃ F₃ A B : Finset (Vertex d)) :
    (∫ ω, (section9PivotalCount E L R Q₁ F₁ Q₃ F₃ A B ω -
      section9PivotalMean μ E L R Q₁ F₁ Q₃ F₃ A B)^2 ∂μ) ≤
      section9PivotalMean μ E L R Q₁ F₁ Q₃ F₃ A B +
      ∑ e ∈ E, ∑ f ∈ E, if e = f then 0 else
        section9PivotalCovariance μ L R Q₁ F₁ Q₃ F₃ A B e f := by
  rw [section9PivotalCount_covariance_identity]
  have hsum : (∑ e ∈ E, ∑ f ∈ E, section9PivotalCovariance μ L R Q₁ F₁ Q₃ F₃ A B e f) ≤
      ∑ e ∈ E, ∑ f ∈ E,
        ((if e = f then section9PivotalProbability μ L R Q₁ F₁ Q₃ F₃ A B e else 0) +
          (if e = f then 0 else section9PivotalCovariance μ L R Q₁ F₁ Q₃ F₃ A B e f)) :=
    Finset.sum_le_sum (fun e _ => Finset.sum_le_sum
      (fun f _ => section9PivotalCovariance_diagonal_split μ L R Q₁ F₁ Q₃ F₃ A B e f))
  have hdiag : (∑ e ∈ E, ∑ f ∈ E,
      if e = f then section9PivotalProbability μ L R Q₁ F₁ Q₃ F₃ A B e else 0) =
      ∑ e ∈ E, section9PivotalProbability μ L R Q₁ F₁ Q₃ F₃ A B e := by
    apply Finset.sum_congr rfl
    intro e he
    simp [he]
  simp_rw [Finset.sum_add_distrib] at hsum
  rw [hdiag] at hsum
  have hmean : section9PivotalMean μ E L R Q₁ F₁ Q₃ F₃ A B =
      ∑ e ∈ E, section9PivotalProbability μ L R Q₁ F₁ Q₃ F₃ A B e :=
    integral_section9PivotalCount μ E L R Q₁ F₁ Q₃ F₃ A B
  rwa [← hmean] at hsum

end NearCritical
