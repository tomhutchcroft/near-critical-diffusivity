module

public import NearCritical.Section9ConditionalLaw

@[expose] public section
namespace NearCritical
open MeasureTheory
open scoped Classical

/-- Every measurable event determined by a finite fresh bond block has the
same probability under the actual reveal law and the original law. -/
theorem section9RevealedLaw_fresh_probability {d : ℕ} (p : unitInterval)
    (Q₁ H₁ Q₃ H₃ F₁ F₃ : Finset (Vertex d)) (hH₁ : H₁ ⊆ Q₁) (hH₃ : H₃ ⊆ Q₃)
    (hpos : percolation d p (section9RevealEvent Q₁ H₁ Q₃ H₃ F₁ F₃) ≠ 0)
    (T : Finset (Bond d))
    (hd : Disjoint (clusterRevealBonds Q₁ F₁ ∪ clusterRevealBonds Q₃ F₃) T)
    (A : Set (Configuration d)) (hA : MeasurableSet A)
    (hlocal : ∀ ω θ : Configuration d, (∀ b ∈ T, ω b = θ b) → (ω ∈ A ↔ θ ∈ A)) :
    (section9RevealedLaw p Q₁ H₁ Q₃ H₃ F₁ F₃).real A = (percolation d p).real A := by
  let g : (T → Bool) → ℝ := fun ξ =>
    A.indicator (fun _ => (1 : ℝ)) (extendConfiguration T (fun _ => false) ξ)
  have hg (ω : Configuration d) :
      g (T.restrict ω) = A.indicator (fun _ => (1 : ℝ)) ω := by
    have hEq := hlocal ω (extendConfiguration T (fun _ => false) (T.restrict ω)) (by
      intro b hb
      simp [extendConfiguration, hb, Finset.restrict])
    simp only [g, Set.indicator_apply, ← hEq]
  have h := section9RevealedLaw_fresh_expectation p Q₁ H₁ Q₃ H₃ F₁ F₃ hH₁ hH₃ hpos T hd g
  simp_rw [hg] at h
  have hi (μ : Measure (Configuration d)) :
      (∫ ω, A.indicator (fun _ => (1 : ℝ)) ω ∂μ) = μ.real A :=
    integral_indicator_one hA
  rwa [hi, hi] at h

end NearCritical
