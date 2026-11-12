module

public import NearCritical.Section9FreshEvent

/-! Two-layer transfer from the revealed (conditional) law to the product law.

`section9_revealed_prod_eq`: for a measurable event of the pair (critical
configuration, sprinkle) whose dependence on the critical configuration is
through a finite bond block `T` disjoint from the explored bonds of the two
revealed clusters,

  `(revealedLaw x P_q)(B) = (P_p x P_q)(B)`.

This replaces the broken tail of `Section9OpenedTargetSupport.lean` and is the
bridge from the conditional Section 9 theorems to the product-law success
probability of a lattice step.
-/
@[expose] public section
namespace NearCritical
open MeasureTheory
open scoped Classical

lemma prod_real_eq_integral_section {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {B : Set (α × β)} (hB : MeasurableSet B) :
    (μ.prod ν).real B = ∫ x, ν.real (Prod.mk x ⁻¹' B) ∂μ := by
  unfold Measure.real
  rw [Measure.prod_apply hB]
  exact (integral_toReal (measurable_measure_prodMk_left hB).aemeasurable
    (Filter.Eventually.of_forall (fun x => measure_lt_top ν _))).symm

theorem section9_revealed_prod_eq {d : ℕ} (p q : unitInterval)
    (Q₁ H₁ Q₃ H₃ F₁ F₃ : Finset (Vertex d)) (hH₁ : H₁ ⊆ Q₁) (hH₃ : H₃ ⊆ Q₃)
    (hpos : percolation d p (section9RevealEvent Q₁ H₁ Q₃ H₃ F₁ F₃) ≠ 0)
    (T : Finset (Bond d))
    (hd : Disjoint (clusterRevealBonds Q₁ F₁ ∪ clusterRevealBonds Q₃ F₃) T)
    (B : Set (Configuration d × Configuration d)) (hB : MeasurableSet B)
    (hlocal : ∀ ω θ : Configuration d, (∀ b ∈ T, ω b = θ b) →
      ∀ η : Configuration d, ((ω, η) ∈ B ↔ (θ, η) ∈ B)) :
    ((section9RevealedLaw p Q₁ H₁ Q₃ H₃ F₁ F₃).prod (percolation d q)).real B =
      ((percolation d p).prod (percolation d q)).real B := by
  letI := section9RevealedLaw_isProbability p Q₁ H₁ Q₃ H₃ F₁ F₃ hpos
  rw [prod_real_eq_integral_section _ _ hB, prod_real_eq_integral_section _ _ hB]
  let g : (T → Bool) → ℝ := fun ξ =>
    (percolation d q).real (Prod.mk (extendConfiguration T (fun _ => false) ξ) ⁻¹' B)
  have hg : ∀ ω : Configuration d,
      g (T.restrict ω) = (percolation d q).real (Prod.mk ω ⁻¹' B) := by
    intro ω
    have hsec : Prod.mk (extendConfiguration T (fun _ => false) (T.restrict ω)) ⁻¹' B =
        Prod.mk ω ⁻¹' B := by
      ext η
      exact (hlocal ω (extendConfiguration T (fun _ => false) (T.restrict ω)) (by
        intro b hb
        simp [extendConfiguration, hb, Finset.restrict]) η).symm
    show (percolation d q).real _ = _
    rw [hsec]
  have h := section9RevealedLaw_fresh_expectation p Q₁ H₁ Q₃ H₃ F₁ F₃ hH₁ hH₃ hpos T hd g
  simp_rw [hg] at h
  exact h

end NearCritical
