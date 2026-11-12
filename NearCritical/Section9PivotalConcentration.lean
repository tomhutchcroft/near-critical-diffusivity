module

public import NearCritical.Section9PivotalVariance
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! Section9 relative concentration reduction for the ACTUAL pivot count.
The envelope is computed from actual mean and covariances, not supplied as an
assumed variance bound. The quantitative estimates of these terms and the
actual revealed-cluster conditional-law identification remain obligations. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory
open scoped Classical

/-- Computed source variance envelope, before the Section9 diagram estimates. -/
def section9PivotalVarianceEnvelope {d : ℕ} (μ : Measure (Configuration d))
    (E : Finset (Vertex d × Vertex d)) (L R Q₁ F₁ Q₃ F₃ A B : Finset (Vertex d)) : ℝ :=
  section9PivotalMean μ E L R Q₁ F₁ Q₃ F₃ A B +
    ∑ e ∈ E, ∑ f ∈ E, if e = f then 0 else
      section9PivotalCovariance μ L R Q₁ F₁ Q₃ F₃ A B e f

lemma integrable_section9PivotalCount_centered_sq {d : ℕ} (μ : Measure (Configuration d))
    [IsFiniteMeasure μ] (E : Finset (Vertex d × Vertex d))
    (L R Q₁ F₁ Q₃ F₃ A B : Finset (Vertex d)) :
    Integrable (fun ω => (section9PivotalCount E L R Q₁ F₁ Q₃ F₃ A B ω -
      section9PivotalMean μ E L R Q₁ F₁ Q₃ F₃ A B)^2) μ := by
  let Y := section9PivotalCount E L R Q₁ F₁ Q₃ F₃ A B
  let m := section9PivotalMean μ E L R Q₁ F₁ Q₃ F₃ A B
  have hY : Integrable Y μ := integrable_section9PivotalCount μ E L R Q₁ F₁ Q₃ F₃ A B
  have hY2 : Integrable (fun ω => (Y ω)^2) μ :=
    integrable_section9PivotalCount_sq μ E L R Q₁ F₁ Q₃ F₃ A B
  have hp (ω : Configuration d) : (Y ω-m)^2 = (Y ω)^2-(2*m)*Y ω+m^2 := by ring
  change Integrable (fun ω => (Y ω-m)^2) μ
  simp_rw [hp]
  exact (hY2.sub (hY.const_mul (2*m))).add (integrable_const (m^2))

lemma section9PivotalVarianceEnvelope_nonneg {d : ℕ} (μ : Measure (Configuration d))
    [IsProbabilityMeasure μ] (E : Finset (Vertex d × Vertex d))
    (L R Q₁ F₁ Q₃ F₃ A B : Finset (Vertex d)) :
    0 ≤ section9PivotalVarianceEnvelope μ E L R Q₁ F₁ Q₃ F₃ A B :=
  le_trans (integral_nonneg (fun ω => sq_nonneg _))
    (section9PivotalCount_variance_le μ E L R Q₁ F₁ Q₃ F₃ A B)

/-- Genuine two-sided Chebyshev bound with the computed source covariance sum. -/
theorem section9PivotalCount_deviation {d : ℕ} (μ : Measure (Configuration d))
    [IsProbabilityMeasure μ] (E : Finset (Vertex d × Vertex d))
    (L R Q₁ F₁ Q₃ F₃ A B : Finset (Vertex d)) {t : ℝ} (ht : 0 < t) :
    μ.real {ω | t ≤ |section9PivotalCount E L R Q₁ F₁ Q₃ F₃ A B ω -
      section9PivotalMean μ E L R Q₁ F₁ Q₃ F₃ A B|} ≤
      section9PivotalVarianceEnvelope μ E L R Q₁ F₁ Q₃ F₃ A B / t^2 := by
  let Y := section9PivotalCount E L R Q₁ F₁ Q₃ F₃ A B
  let m := section9PivotalMean μ E L R Q₁ F₁ Q₃ F₃ A B
  let g := fun ω : Configuration d => (Y ω-m)^2
  have hi : Integrable g μ := integrable_section9PivotalCount_centered_sq μ E L R Q₁ F₁ Q₃ F₃ A B
  have hn : 0 ≤ᵐ[μ] g := Filter.Eventually.of_forall (fun ω => sq_nonneg _)
  have hs : {ω : Configuration d | t ≤ |Y ω-m|} ⊆ {ω | t^2 ≤ g ω} := by
    intro ω hω
    have hsq := (sq_le_sq₀ ht.le (abs_nonneg (Y ω-m))).mpr hω
    change t^2 ≤ (Y ω-m)^2
    simpa only [sq_abs] using hsq
  have hm := mul_meas_ge_le_integral_of_nonneg hn hi (t^2)
  have ht2 : 0 < t^2 := sq_pos_of_pos ht
  have hb : μ.real {ω | t^2 ≤ g ω} ≤
      section9PivotalVarianceEnvelope μ E L R Q₁ F₁ Q₃ F₃ A B / t^2 := by
    apply (le_div_iff₀ ht2).mpr
    calc
      _ = t^2 * μ.real {ω | t^2 ≤ g ω} := mul_comm _ _
      _ ≤ ∫ ω, g ω ∂μ := hm
      _ ≤ _ := section9PivotalCount_variance_le μ E L R Q₁ F₁ Q₃ F₃ A B
  exact (measureReal_mono hs).trans hb

/-- The exact source interval has large probability once its computed
covariance envelope is small relative to the square of its actual mean. -/
theorem section9PivotalCount_relative_interval {d : ℕ} (μ : Measure (Configuration d))
    [IsProbabilityMeasure μ] (E : Finset (Vertex d × Vertex d))
    (L R Q₁ F₁ Q₃ F₃ A B : Finset (Vertex d))
    (hm : 0 < section9PivotalMean μ E L R Q₁ F₁ Q₃ F₃ A B) :
    let m := section9PivotalMean μ E L R Q₁ F₁ Q₃ F₃ A B
    1 - section9PivotalVarianceEnvelope μ E L R Q₁ F₁ Q₃ F₃ A B / (m/2)^2 ≤
      μ.real {ω | m/2 ≤ section9PivotalCount E L R Q₁ F₁ Q₃ F₃ A B ω ∧
        section9PivotalCount E L R Q₁ F₁ Q₃ F₃ A B ω ≤ 3*m/2} := by
  let Y := section9PivotalCount E L R Q₁ F₁ Q₃ F₃ A B
  let m := section9PivotalMean μ E L R Q₁ F₁ Q₃ F₃ A B
  have ht : 0 < m/2 := div_pos hm (by norm_num)
  have hb := section9PivotalCount_deviation μ E L R Q₁ F₁ Q₃ F₃ A B (t := m/2) ht
  have hcover : (Set.univ : Set (Configuration d)) ⊆
      {ω | m/2 ≤ |Y ω-m|} ∪ {ω | m/2 ≤ Y ω ∧ Y ω ≤ 3*m/2} := by
    intro ω _
    by_cases hω : m/2 ≤ |Y ω-m|
    · exact Or.inl hω
    · have hsmall := abs_lt.mp (lt_of_not_ge hω)
      exact Or.inr ⟨by linarith, by linarith⟩
  have hc := (measureReal_mono (μ := μ) hcover).trans (measureReal_union_le _ _)
  have hone : μ.real (Set.univ : Set (Configuration d)) = 1 := by simp
  rw [hone] at hc
  change 1 - _ ≤ μ.real {ω | m/2 ≤ Y ω ∧ Y ω ≤ 3*m/2}
  linarith

/-- Numerical covariance-sum control yields the source 1-epsilon concentration.
The remaining estimate is of the COMPUTED mean-plus-covariance expression,
not an assumed variance or final probability bound. -/
theorem section9PivotalCount_concentration_of_covariance_sum {d : ℕ}
    (μ : Measure (Configuration d)) [IsProbabilityMeasure μ]
    (E : Finset (Vertex d × Vertex d)) (L R Q₁ F₁ Q₃ F₃ A B : Finset (Vertex d))
    (hm : 0 < section9PivotalMean μ E L R Q₁ F₁ Q₃ F₃ A B) {ε : ℝ}
    (hcov : section9PivotalVarianceEnvelope μ E L R Q₁ F₁ Q₃ F₃ A B ≤
      ε * (section9PivotalMean μ E L R Q₁ F₁ Q₃ F₃ A B / 2)^2) :
    let m := section9PivotalMean μ E L R Q₁ F₁ Q₃ F₃ A B
    1-ε ≤ μ.real {ω | m/2 ≤ section9PivotalCount E L R Q₁ F₁ Q₃ F₃ A B ω ∧
      section9PivotalCount E L R Q₁ F₁ Q₃ F₃ A B ω ≤ 3*m/2} := by
  have hden : 0 < (section9PivotalMean μ E L R Q₁ F₁ Q₃ F₃ A B / 2)^2 :=
    sq_pos_of_pos (div_pos hm (by norm_num))
  have hr := (div_le_iff₀ hden).mpr hcov
  have hi := section9PivotalCount_relative_interval μ E L R Q₁ F₁ Q₃ F₃ A B hm
  linarith

end NearCritical
