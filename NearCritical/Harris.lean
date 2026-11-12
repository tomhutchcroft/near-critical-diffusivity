module

public import NearCritical.CylinderBK

/-! Harris positive association for finite Bernoulli products and lattice
cylinders. Infinite-cluster events require a separate limit argument. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Set MeasureTheory ProbabilityTheory
open scoped Classical
namespace BK

/-- Positive association for increasing events at every Bernoulli parameter. -/
def Harris (E : Type*) [Fintype E] : Prop :=
  ∀ (p : ℝ), 0 ≤ p → p ≤ 1 → ∀ A B : Set (E → Bool),
    Increasing A → Increasing B →
      eventProbability p A * eventProbability p B ≤ eventProbability p (A ∩ B)

lemma harris_step_arithmetic {p a₀ a₁ b₀ b₁ : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (ha : a₀ ≤ a₁) (hb : b₀ ≤ b₁) :
    ((1 - p) * a₀ + p * a₁) * ((1 - p) * b₀ + p * b₁) ≤
      (1 - p) * (a₀ * b₀) + p * (a₁ * b₁) := by
  have hnon := mul_nonneg (mul_nonneg hp (sub_nonneg.mpr hp1))
    (mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hb))
  nlinarith

lemma harris_option {E : Type*} [Fintype E] (hH : Harris E) : Harris (Option E) := by
  intro p hp hp1 A B hA hB
  have h₀ := hH p hp hp1 (sectionEvent A false) (sectionEvent B false)
    (increasing_section hA false) (increasing_section hB false)
  have h₁ := hH p hp hp1 (sectionEvent A true) (sectionEvent B true)
    (increasing_section hA true) (increasing_section hB true)
  have ha := eventProbability_mono hp hp1 (section_false_subset_true hA)
  have hb := eventProbability_mono hp hp1 (section_false_subset_true hB)
  have hweighted := add_le_add
    (mul_le_mul_of_nonneg_left h₀ (sub_nonneg.mpr hp1))
    (mul_le_mul_of_nonneg_left h₁ hp)
  rw [eventProbability_option p A, eventProbability_option p B,
    eventProbability_option p (A ∩ B)]
  exact (harris_step_arithmetic hp hp1 ha hb).trans hweighted

lemma harris_equiv {E F : Type*} [Fintype E] [Fintype F]
    (e : E ≃ F) (hH : Harris E) : Harris F := by
  intro p hp hp1 A B hA hB
  have h := hH p hp hp1 (pullEvent e A) (pullEvent e B)
    (increasing_pullEvent e hA) (increasing_pullEvent e hB)
  have hinter : pullEvent e (A ∩ B) = pullEvent e A ∩ pullEvent e B := rfl
  rw [← hinter, eventProbability_pullEvent, eventProbability_pullEvent,
    eventProbability_pullEvent] at h
  exact h

lemma harris_empty : Harris PEmpty := by
  intro p hp hp1 A B hA hB
  let η : PEmpty → Bool := fun e ↦ nomatch e
  have hprob (C : Set (PEmpty → Bool)) : eventProbability p C = if η ∈ C then 1 else 0 := by
    unfold eventProbability finiteExpectation
    rw [Finset.sum_eq_single η]
    · simp
    · intro θ _ hθη
      exact False.elim (hθη (by funext e; exact PEmpty.elim e))
    · intro hn
      exact False.elim (hn (by
        apply Finset.mem_singleton.mpr
        funext e
        exact PEmpty.elim e))
  rw [hprob, hprob, hprob]
  by_cases ha : η ∈ A <;> by_cases hb : η ∈ B <;> simp [ha, hb]

/-- Harris inequality in explicit finite Bernoulli sums, all 0<=p<=1. -/
theorem harris_eventProbability {E : Type*} [Fintype E] : Harris E := by
  refine Fintype.induction_empty_option (P := fun α [h : Fintype α] ↦ @Harris α h)
    ?_ harris_empty ?_ E
  · intro α β hβ e hH
    let : Fintype α := Fintype.ofEquiv β e.symm
    exact harris_equiv e hH
  · intro α hα hH
    exact harris_option hH

/-- Harris under the actual finite Bernoulli product probability measure. -/
theorem finite_bernoulli_harris {E : Type*} [Fintype E] (p : unitInterval)
    (A B : Set (E → Bool)) (hA : Increasing A) (hB : Increasing B) :
    (Measure.pi fun _ : E ↦ bernoulliMeasure true false p).real A *
      (Measure.pi fun _ : E ↦ bernoulliMeasure true false p).real B ≤
      (Measure.pi fun _ : E ↦ bernoulliMeasure true false p).real (A ∩ B) := by
  simpa only [eventProbability_eq_measureReal] using
    (harris_eventProbability (E := E) (p : ℝ) p.2.1 p.2.2 A B hA hB)

end BK

/-- Positive association for increasing finite-coordinate events in the actual
infinite lattice law. The intersection is ordinary simultaneous occurrence. -/
theorem percolation_cylinder_harris (d : ℕ) (p : unitInterval) (s : Finset (Bond d))
    (A B : Set ((e : s) → Bool)) (hA : BK.Increasing A) (hB : BK.Increasing B) :
    (percolation d p).real (s.restrict ⁻¹' A) *
      (percolation d p).real (s.restrict ⁻¹' B) ≤
      (percolation d p).real ((s.restrict ⁻¹' A) ∩ (s.restrict ⁻¹' B)) := by
  have h := BK.harris_eventProbability (E := s) (p : ℝ) p.2.1 p.2.2 A B hA hB
  rw [eventProbability_cylinder d p s, eventProbability_cylinder d p s,
    eventProbability_cylinder d p s] at h
  exact h

end NearCritical
