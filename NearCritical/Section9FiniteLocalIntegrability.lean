module
public import NearCritical.Bernoulli
public import NearCritical.CylinderDisjointOccurrence
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! Real observables on finitely many bond coordinates are integrable under
any finite measure, including the actual positive heart-conditioned law. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory
open scoped Classical

/-- Every real finite-coordinate observable is integrable under an arbitrary
finite configuration measure, with no separate measurability assumption. -/
theorem section9_finite_cylinder_integrable {d : ℕ}
    (μ : Measure (Configuration d)) [IsFiniteMeasure μ]
    (U : Finset (Bond d)) (g : (U → Bool) → ℝ) :
    Integrable (fun ω : Configuration d => g (U.restrict ω)) μ := by
  have hm : Measurable (U.restrict : Configuration d → (U → Bool)) :=
    Finset.measurable_restrict U
  have hg : Integrable g (μ.map (U.restrict : Configuration d → (U → Bool))) :=
    Integrable.of_finite
  exact hg.comp_measurable hm

/-- Agreement on a fixed finite bond set is enough for integrability of an
arbitrary real observable under any finite configuration measure. -/
theorem section9_finite_local_integrable {d : ℕ}
    (μ : Measure (Configuration d)) [IsFiniteMeasure μ]
    (U : Finset (Bond d)) (f : Configuration d → ℝ)
    (hlocal : ∀ ω η : Configuration d, (∀ b ∈ U, ω b = η b) → f ω = f η) :
    Integrable f μ := by
  let g := fun ξ : U → Bool => f (extendConfiguration U (fun _ => false) ξ)
  have he (ω : Configuration d) : g (U.restrict ω) = f ω := by
    apply (hlocal ω _ ?_).symm
    intro b hb
    simp [extendConfiguration,hb,Finset.restrict]
  have hi := section9_finite_cylinder_integrable μ U g
  exact hi.congr (Filter.Eventually.of_forall he)

/-- Integrating a second argument preserves finite-coordinate locality in
the first argument. The second measure need not be finite, and no additional
measurability or integrability premise is required for its defined integral. -/
theorem section9_finite_local_integral_integrable {d : ℕ}
    (μ : Measure (Configuration d)) [IsFiniteMeasure μ]
    (ρ : Measure (Configuration d)) (U : Finset (Bond d))
    (F : Configuration d → Configuration d → ℝ)
    (hlocal : ∀ ω η : Configuration d, (∀ b ∈ U, ω b = η b) →
      ∀ ζ, F ω ζ = F η ζ) :
    Integrable (fun ω => ∫ ζ, F ω ζ ∂ρ) μ := by
  apply section9_finite_local_integrable μ U
  intro ω η hagree
  exact integral_congr_ae (Filter.Eventually.of_forall (hlocal ω η hagree))

end NearCritical
