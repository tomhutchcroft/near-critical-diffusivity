module
public import NearCritical.Bernoulli
public import Mathlib.MeasureTheory.Integral.Prod

/-! Actual outer-reveal/fresh-law probability integration. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory

/-- An outer good event and uniform fresh-section probability bound give
an actual product-law bound, with both failure probabilities charged. -/
theorem section9_two_stage_probability_lower {d : ℕ}
    (μ ν : Measure (Configuration d)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (G : Set (Configuration d)) (S : Set (Configuration d × Configuration d))
    (hG : MeasurableSet G) (hS : MeasurableSet S) (η ζ : ℝ) (hζ : 0 ≤ ζ)
    (houter : 1-η ≤ μ.real G)
    (hsection : ∀ ω ∈ G, 1-ζ ≤ ν.real ((Prod.mk ω) ⁻¹' S)) :
    1-η-ζ ≤ (μ.prod ν).real S := by
  let H := S.indicator (1 : Configuration d × Configuration d → ℝ)
  let f := fun ω : Configuration d => ∫ θ, H (ω,θ) ∂ν
  have hiH : Integrable H (μ.prod ν) := (integrable_const (1 : ℝ)).indicator hS
  have hiG : Integrable (G.indicator (1 : Configuration d → ℝ)) μ :=
    (integrable_const (1 : ℝ)).indicator hG
  have hf (ω : Configuration d) : f ω = ν.real ((Prod.mk ω) ⁻¹' S) := by
    have hs : MeasurableSet ((Prod.mk ω) ⁻¹' S) :=
      hS.preimage (measurable_const.prodMk measurable_id)
    have heq : (fun θ => H (ω, θ)) =
        (Prod.mk ω ⁻¹' S).indicator (1 : Configuration d → ℝ) := by
      funext θ
      by_cases h : (ω, θ) ∈ S <;> simp [H, Set.indicator_apply, h]
    change (∫ θ, H (ω, θ) ∂ν) = _
    rw [heq, integral_indicator_one hs]
  have hpoint (ω : Configuration d) : G.indicator (1 : Configuration d → ℝ) ω-ζ ≤ f ω := by
    rw [hf]
    by_cases hω : ω ∈ G
    · simpa only [Set.indicator_of_mem hω,Pi.one_apply] using hsection ω hω
    · simp only [Set.indicator_of_notMem hω]
      have hn : 0 ≤ ν.real ((Prod.mk ω) ⁻¹' S) := measureReal_nonneg
      linarith
  have htotal : (∫ ω, f ω ∂μ) = (μ.prod ν).real S := by
    exact (integral_prod H hiH).symm.trans (integral_indicator_one hS)
  have hlower : (∫ ω, G.indicator (1 : Configuration d → ℝ) ω-ζ ∂μ) = μ.real G-ζ := by
    rw [integral_sub hiG (integrable_const ζ),integral_indicator_one hG]
    simp
  have hint := integral_mono (hiG.sub (integrable_const ζ)) hiH.integral_prod_left hpoint
  change (∫ ω, G.indicator (1 : Configuration d → ℝ) ω-ζ ∂μ) ≤ (∫ ω, f ω ∂μ) at hint
  rw [hlower,htotal] at hint
  linarith only [houter,hint]

end NearCritical
