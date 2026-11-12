module

public import NearCritical.Bernoulli
public import NearCritical.FiniteExpectation
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-! The bridge between finite Bernoulli sums and the actual product probability
measure. In particular cylinder observables of the lattice model are covered. -/
@[expose] public section
namespace NearCritical
open MeasureTheory ProbabilityTheory
open scoped ENNReal

lemma finite_bernoulli_singleton_real {E : Type*} [Fintype E]
    (p : unitInterval) (ω : E → Bool) :
    (Measure.pi (fun _ : E ↦ bernoulliMeasure true false p)).real {ω} =
      ∏ e : E, if ω e then (p : ℝ) else 1 - (p : ℝ) := by
  classical
  rw [measureReal_def, Measure.pi_singleton, ENNReal.toReal_prod]
  apply Finset.prod_congr rfl
  intro e _
  cases ω e <;> simp [bernoulliMeasure_def]

/-- Finite-product expectations equal their explicit Bernoulli sums. -/
theorem integral_finite_bernoulli {E : Type*} [Fintype E]
    (p : unitInterval) (f : (E → Bool) → ℝ) :
    ∫ ω, f ω ∂(Measure.pi (fun _ : E ↦ bernoulliMeasure true false p)) =
      finiteExpectation (p : ℝ) f := by
  classical
  rw [integral_fintype (Integrable.of_finite : Integrable f _)]
  simp only [finiteExpectation, finite_bernoulli_singleton_real, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro ω _
  exact mul_comm _ _

/-- Expectations of finite-edge observables in the full infinite lattice model.
No new finite-volume probability measure is substituted for the source model. -/
theorem percolation_cylinder_expectation (d : ℕ) (p : unitInterval)
    (s : Finset (Bond d)) (f : ((e : s) → Bool) → ℝ) :
    ∫ ω, f (s.restrict ω) ∂percolation d p = finiteExpectation (p : ℝ) f := by
  classical
  unfold percolation
  rw [integral_restrict_infinitePi (μ := fun _ : Bond d ↦ bernoulliMeasure true false p)
    (s := s) (f := f)
    (Integrable.of_finite : Integrable f (Measure.pi
      (fun _ : s ↦ bernoulliMeasure true false p))).aestronglyMeasurable]
  exact integral_finite_bernoulli p f

end NearCritical
