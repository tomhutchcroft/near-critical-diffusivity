module
public import NearCritical.Section9PivotalConcentration
import Mathlib.Tactic.Linarith

/-! Chebyshev for the actual pivotal variance integral, without an envelope. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory

/-- Deviation is controlled by the actual centered-square integral. This can
consume the proved source variance bound directly, in the correct direction. -/
theorem section9_actual_pivotal_deviation {d : ℕ} (μ : Measure (Configuration d))
    [IsProbabilityMeasure μ] (E : Finset (Vertex d × Vertex d))
    (L R Q₁ F₁ Q₃ F₃ A B : Finset (Vertex d)) {t : ℝ} (ht : 0 < t) :
    μ.real {ω | t ≤ |section9PivotalCount E L R Q₁ F₁ Q₃ F₃ A B ω -
      section9PivotalMean μ E L R Q₁ F₁ Q₃ F₃ A B|} ≤
      (∫ ω, (section9PivotalCount E L R Q₁ F₁ Q₃ F₃ A B ω -
        section9PivotalMean μ E L R Q₁ F₁ Q₃ F₃ A B)^2 ∂μ)/t^2 := by
  let Y := section9PivotalCount E L R Q₁ F₁ Q₃ F₃ A B
  let m := section9PivotalMean μ E L R Q₁ F₁ Q₃ F₃ A B
  let g := fun ω : Configuration d => (Y ω-m)^2
  have hi : Integrable g μ := integrable_section9PivotalCount_centered_sq μ E L R Q₁ F₁ Q₃ F₃ A B
  have hn : 0 ≤ᵐ[μ] g := Filter.Eventually.of_forall (fun ω => sq_nonneg _)
  have hs : {ω : Configuration d | t ≤ |Y ω-m|} ⊆ {ω | t^2 ≤ g ω} := by
    intro ω hω
    have hh := (sq_le_sq₀ ht.le (abs_nonneg (Y ω-m))).mpr hω
    change t^2 ≤ (Y ω-m)^2
    simpa only [g,sq_abs] using hh
  have hmarkov := mul_meas_ge_le_integral_of_nonneg hn hi (t^2)
  have hb : μ.real {ω | t^2 ≤ g ω} ≤ (∫ ω, g ω ∂μ)/t^2 := by
    apply (le_div_iff₀ (sq_pos_of_pos ht)).mpr
    simpa only [mul_comm] using hmarkov
  exact (measureReal_mono hs).trans hb

/-- The relative interval bound uses the actual variance integral, with no
assumption that a separately defined variance envelope has been estimated. -/
theorem section9_actual_pivotal_relative_interval {d : ℕ} (μ : Measure (Configuration d))
    [IsProbabilityMeasure μ] (E : Finset (Vertex d × Vertex d))
    (L R Q₁ F₁ Q₃ F₃ A B : Finset (Vertex d))
    (hm : 0 < section9PivotalMean μ E L R Q₁ F₁ Q₃ F₃ A B) :
    let m := section9PivotalMean μ E L R Q₁ F₁ Q₃ F₃ A B
    1-(∫ ω, (section9PivotalCount E L R Q₁ F₁ Q₃ F₃ A B ω-m)^2 ∂μ)/(m/2)^2 ≤
      μ.real {ω | m/2 ≤ section9PivotalCount E L R Q₁ F₁ Q₃ F₃ A B ω ∧
        section9PivotalCount E L R Q₁ F₁ Q₃ F₃ A B ω ≤ 3*m/2} := by
  intro m
  let Y := section9PivotalCount E L R Q₁ F₁ Q₃ F₃ A B
  have ht : 0 < m/2 := div_pos hm (by norm_num)
  have hb := section9_actual_pivotal_deviation μ E L R Q₁ F₁ Q₃ F₃ A B (t := m/2) ht
  have hcover : (Set.univ : Set (Configuration d)) ⊆
      {ω | m/2 ≤ |Y ω-m|} ∪ {ω | m/2 ≤ Y ω ∧ Y ω ≤ 3*m/2} := by
    intro ω _
    by_cases hω : m/2 ≤ |Y ω-m|
    · exact Or.inl hω
    · have hsmall := abs_lt.mp (lt_of_not_ge hω)
      exact Or.inr ⟨by linarith,by linarith⟩
  have hc := (measureReal_mono (μ := μ) hcover).trans (measureReal_union_le _ _)
  have hone : μ.real (Set.univ : Set (Configuration d)) = 1 := by simp
  rw [hone] at hc
  change 1-_ ≤ μ.real {ω | m/2 ≤ Y ω ∧ Y ω ≤ 3*m/2}
  linarith

end NearCritical
