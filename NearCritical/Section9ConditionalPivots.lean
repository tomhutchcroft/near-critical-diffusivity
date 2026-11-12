module

public import NearCritical.Section9ConditionalLaw
public import NearCritical.Section9PivotalSupport

/-! Actual conditional pivot probabilities transported to fixed-deletion
Bernoulli events. Numerical diagram bounds are separate obligations. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory
open scoped Classical BigOperators

/-- Full pivot events, including disjointness of the two full components,
retain their probability after conditioning on the two actual heart unions.
The prescribed F1/F3 remain fixed in both events. -/
theorem section9RevealedLaw_pivotalProbability {d : ℕ} (p : unitInterval)
    (L R Q₁ H₁ F₁ Q₃ H₃ F₃ A B : Finset (Vertex d))
    (hH₁ : H₁ ⊆ Q₁) (hH₃ : H₃ ⊆ Q₃)
    (hLQ₃ : Disjoint L Q₃) (hRQ₁ : Disjoint R Q₁)
    (hpos : percolation d p (section9RevealEvent Q₁ H₁ Q₃ H₃ F₁ F₃) ≠ 0)
    (e : Vertex d × Vertex d) :
    (section9RevealedLaw p Q₁ H₁ Q₃ H₃ F₁ F₃).real
      {ω | sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ A B e} =
    (percolation d p).real {ω | sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ A B e} := by
  let S := sprinklingAvailableBonds L Q₁ F₁ ∪ sprinklingAvailableBonds R Q₃ F₃
  let g : (S → Bool) → ℝ := fun ξ => section9PivotalIndicator L R Q₁ F₁ Q₃ F₃ A B e
    (extendConfiguration S (fun _ => false) ξ)
  have hd : Disjoint (clusterRevealBonds Q₁ F₁ ∪ clusterRevealBonds Q₃ F₃) S :=
    sprinklingAvailableBonds_disjoint_reveals L R Q₁ F₁ Q₃ F₃ hLQ₃ hRQ₁
  have hg (ω : Configuration d) : g (S.restrict ω) =
      section9PivotalIndicator L R Q₁ F₁ Q₃ F₃ A B e ω := by
    have hL : ∀ b ∈ sprinklingAvailableBonds L Q₁ F₁,
        ω b = extendConfiguration S (fun _ => false) (S.restrict ω) b := by
      intro b hb
      have hbS : b ∈ S := Finset.mem_union.mpr (Or.inl hb)
      simp [extendConfiguration, hbS, Finset.restrict]
    have hR : ∀ b ∈ sprinklingAvailableBonds R Q₃ F₃,
        ω b = extendConfiguration S (fun _ => false) (S.restrict ω) b := by
      intro b hb
      have hbS : b ∈ S := Finset.mem_union.mpr (Or.inr hb)
      simp [extendConfiguration, hbS, Finset.restrict]
    have he := sprinklingPivotalPair_iff_of_available_agree L R Q₁ F₁ Q₃ F₃ A B ω
      (extendConfiguration S (fun _ => false) (S.restrict ω)) hL hR e
    dsimp only [g, section9PivotalIndicator]
    rw [← he]
  have hf := section9RevealedLaw_fresh_expectation p Q₁ H₁ Q₃ H₃ F₁ F₃
    hH₁ hH₃ hpos S hd g
  simp_rw [hg] at hf
  have hi (μ : Measure (Configuration d)) :
      (∫ ω, section9PivotalIndicator L R Q₁ F₁ Q₃ F₃ A B e ω ∂μ) =
        μ.real {ω | sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ A B e} := by
    have heq : section9PivotalIndicator L R Q₁ F₁ Q₃ F₃ A B e =
        ({ω | sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ A B e} : Set (Configuration d)).indicator
          (fun _ => (1 : ℝ)) := by
      funext ω
      by_cases hω : sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ A B e <;>
        simp [section9PivotalIndicator, Set.indicator, hω]
    rw [heq]
    have hOne : (∫ ω, ({ω | sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ A B e} :
        Set (Configuration d)).indicator (fun _ => (1 : ℝ)) ω ∂μ) =
        μ.real {ω | sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ A B e} := by
      exact integral_indicator_one (measurableSet_sprinklingPivotalPair L R Q₁ F₁ Q₃ F₃ A B e)
    exact hOne
  rwa [hi, hi] at hf

/-- The source conditional first moment equals the actual unconditional mean
of the fixed-deletion pivot count. This is not its quantitative estimate. -/
theorem section9RevealedLaw_pivotalMean {d : ℕ} (p : unitInterval)
    (E : Finset (Vertex d × Vertex d)) (L R Q₁ H₁ F₁ Q₃ H₃ F₃ A B : Finset (Vertex d))
    (hH₁ : H₁ ⊆ Q₁) (hH₃ : H₃ ⊆ Q₃)
    (hLQ₃ : Disjoint L Q₃) (hRQ₁ : Disjoint R Q₁)
    (hpos : percolation d p (section9RevealEvent Q₁ H₁ Q₃ H₃ F₁ F₃) ≠ 0) :
    section9PivotalMean (section9RevealedLaw p Q₁ H₁ Q₃ H₃ F₁ F₃) E L R Q₁ F₁ Q₃ F₃ A B =
      section9PivotalMean (percolation d p) E L R Q₁ F₁ Q₃ F₃ A B := by
  rw [section9ConditionalPivotalMean_eq_sum p E L R Q₁ H₁ F₁ Q₃ H₃ F₃ A B hpos]
  unfold section9PivotalMean
  rw [integral_section9PivotalCount]
  apply Finset.sum_congr rfl
  intro e _
  exact section9RevealedLaw_pivotalProbability p L R Q₁ H₁ F₁ Q₃ H₃ F₃ A B
    hH₁ hH₃ hLQ₃ hRQ₁ hpos e

end NearCritical
