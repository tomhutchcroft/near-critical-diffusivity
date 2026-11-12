module

public import NearCritical.Section9PivotalCount
import Mathlib.Tactic.Ring

/-! Section9 actual pivotal-count second moments. All pair probabilities refer
to the canonical pivot event; no independence or covariance bound is assumed.
The finite law remains explicit for later conditional-law instantiation. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory Set
open scoped Classical BigOperators

lemma section9PivotalIndicator_mul {d : ℕ} (L R Q₁ F₁ Q₃ F₃ A B : Finset (Vertex d))
    (e f : Vertex d × Vertex d) (ω : Configuration d) :
    section9PivotalIndicator L R Q₁ F₁ Q₃ F₃ A B e ω *
      section9PivotalIndicator L R Q₁ F₁ Q₃ F₃ A B f ω =
    if sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ A B e ∧
      sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ A B f then (1 : ℝ) else 0 := by
  by_cases he : sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ A B e <;>
    by_cases hf : sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ A B f <;>
      simp [section9PivotalIndicator, he, hf]

private lemma pivotalIndicator_mul_eq_indicator {d : ℕ}
    (L R Q₁ F₁ Q₃ F₃ A B : Finset (Vertex d)) (e f : Vertex d × Vertex d) :
    (fun ω => section9PivotalIndicator L R Q₁ F₁ Q₃ F₃ A B e ω *
      section9PivotalIndicator L R Q₁ F₁ Q₃ F₃ A B f ω) =
      ({ω | sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ A B e ∧
        sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ A B f} : Set (Configuration d)).indicator
        (fun _ => (1 : ℝ)) := by
  funext ω
  rw [section9PivotalIndicator_mul]
  by_cases h : sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ A B e ∧
      sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ A B f <;>
    simp [Set.indicator, h]

private lemma measurableSet_jointPivot {d : ℕ}
    (L R Q₁ F₁ Q₃ F₃ A B : Finset (Vertex d)) (e f : Vertex d × Vertex d) :
    MeasurableSet {ω | sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ A B e ∧
      sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ A B f} := by
  exact (measurableSet_sprinklingPivotalPair L R Q₁ F₁ Q₃ F₃ A B e).inter
    (measurableSet_sprinklingPivotalPair L R Q₁ F₁ Q₃ F₃ A B f)

lemma integrable_section9PivotalIndicator_mul {d : ℕ} (μ : Measure (Configuration d))
    [IsFiniteMeasure μ] (L R Q₁ F₁ Q₃ F₃ A B : Finset (Vertex d)) (e f : Vertex d × Vertex d) :
    Integrable (fun ω => section9PivotalIndicator L R Q₁ F₁ Q₃ F₃ A B e ω *
      section9PivotalIndicator L R Q₁ F₁ Q₃ F₃ A B f ω) μ := by
  rw [pivotalIndicator_mul_eq_indicator]
  exact (integrable_const (μ := μ) (1 : ℝ)).indicator
    (measurableSet_jointPivot L R Q₁ F₁ Q₃ F₃ A B e f)

lemma section9PivotalCount_sq_eq_pairs {d : ℕ} (E : Finset (Vertex d × Vertex d))
    (L R Q₁ F₁ Q₃ F₃ A B : Finset (Vertex d)) (ω : Configuration d) :
    (section9PivotalCount E L R Q₁ F₁ Q₃ F₃ A B ω)^2 =
      ∑ e ∈ E, ∑ f ∈ E, section9PivotalIndicator L R Q₁ F₁ Q₃ F₃ A B e ω *
        section9PivotalIndicator L R Q₁ F₁ Q₃ F₃ A B f ω := by
  simp only [section9PivotalCount_eq_sum, pow_two, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  apply Finset.sum_congr rfl
  intro f _
  exact mul_comm _ _

lemma integrable_section9PivotalCount_sq {d : ℕ} (μ : Measure (Configuration d))
    [IsFiniteMeasure μ] (E : Finset (Vertex d × Vertex d))
    (L R Q₁ F₁ Q₃ F₃ A B : Finset (Vertex d)) :
    Integrable (fun ω => (section9PivotalCount E L R Q₁ F₁ Q₃ F₃ A B ω)^2) μ := by
  simp_rw [section9PivotalCount_sq_eq_pairs]
  exact integrable_finsetSum E (fun e _ => integrable_finsetSum E
    (fun f _ => integrable_section9PivotalIndicator_mul μ L R Q₁ F₁ Q₃ F₃ A B e f))

/-- Exact second-moment expansion into actual JOINT pivotal probabilities. -/
theorem integral_section9PivotalCount_sq {d : ℕ} (μ : Measure (Configuration d))
    [IsFiniteMeasure μ] (E : Finset (Vertex d × Vertex d))
    (L R Q₁ F₁ Q₃ F₃ A B : Finset (Vertex d)) :
    (∫ ω, (section9PivotalCount E L R Q₁ F₁ Q₃ F₃ A B ω)^2 ∂μ) =
      ∑ e ∈ E, ∑ f ∈ E, μ.real {ω | sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ A B e ∧
        sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ A B f} := by
  simp_rw [section9PivotalCount_sq_eq_pairs]
  rw [integral_finsetSum E (fun e _ => integrable_finsetSum E
    (fun f _ => integrable_section9PivotalIndicator_mul μ L R Q₁ F₁ Q₃ F₃ A B e f))]
  apply Finset.sum_congr rfl
  intro e _
  rw [integral_finsetSum E (fun f _ => integrable_section9PivotalIndicator_mul μ L R Q₁ F₁ Q₃ F₃ A B e f)]
  apply Finset.sum_congr rfl
  intro f _
  rw [pivotalIndicator_mul_eq_indicator]
  have hOne : (∫ ω, ({ω | sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ A B e ∧
      sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ A B f} : Set (Configuration d)).indicator
        (fun _ => (1 : ℝ)) ω ∂μ) =
      μ.real {ω | sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ A B e ∧
        sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ A B f} := by
    exact integral_indicator_one (measurableSet_jointPivot L R Q₁ F₁ Q₃ F₃ A B e f)
  exact hOne

/-- Actual count mean under the specified law; conditional on revealed data
requires substituting the actual remaining-bond law, not a free scalar. -/
def section9PivotalMean {d : ℕ} (μ : Measure (Configuration d))
    (E : Finset (Vertex d × Vertex d)) (L R Q₁ F₁ Q₃ F₃ A B : Finset (Vertex d)) : ℝ :=
  ∫ ω, section9PivotalCount E L R Q₁ F₁ Q₃ F₃ A B ω ∂μ

/-- Probability-law centered moment equals actual second moment minus mean². -/
theorem section9PivotalCount_centered_identity {d : ℕ} (μ : Measure (Configuration d))
    [IsProbabilityMeasure μ] (E : Finset (Vertex d × Vertex d))
    (L R Q₁ F₁ Q₃ F₃ A B : Finset (Vertex d)) :
    (∫ ω, (section9PivotalCount E L R Q₁ F₁ Q₃ F₃ A B ω -
      section9PivotalMean μ E L R Q₁ F₁ Q₃ F₃ A B)^2 ∂μ) =
      (∫ ω, (section9PivotalCount E L R Q₁ F₁ Q₃ F₃ A B ω)^2 ∂μ) -
        (section9PivotalMean μ E L R Q₁ F₁ Q₃ F₃ A B)^2 := by
  let Y := section9PivotalCount E L R Q₁ F₁ Q₃ F₃ A B
  let m := section9PivotalMean μ E L R Q₁ F₁ Q₃ F₃ A B
  change (∫ ω, (Y ω-m)^2 ∂μ) = (∫ ω, (Y ω)^2 ∂μ)-m^2
  have hY : Integrable Y μ := integrable_section9PivotalCount μ E L R Q₁ F₁ Q₃ F₃ A B
  have hY2 : Integrable (fun ω => (Y ω)^2) μ :=
    integrable_section9PivotalCount_sq μ E L R Q₁ F₁ Q₃ F₃ A B
  have hM := hY.const_mul (2*m)
  have hp (ω : Configuration d) : (Y ω-m)^2 = (Y ω)^2-(2*m)*Y ω+m^2 := by ring
  simp_rw [hp]
  have hadd := integral_add (hY2.sub hM) (integrable_const (μ := μ) (m^2))
  have hsub := integral_sub hY2 hM
  dsimp only [Pi.sub_apply, Pi.add_apply] at hadd hsub
  rw [hadd, hsub, integral_const_mul]
  have hc : (∫ _ω : Configuration d, m^2 ∂μ) = m^2 := by simp
  rw [hc]
  change (∫ ω, (Y ω)^2 ∂μ)-(2*m)*m+m^2 = _
  ring

end NearCritical
