module

public import LatticeProb.Prob.AkcogluKrengelAE
public import NearCritical.Bernoulli

/-!
Almost-sure multiparameter subadditive convergence imported from
Lattice-Probability, commit9d44b4d4670df393bb86ac5a4e042f215001cddf.
Original Apache license and exact source hashes are retained under third_party.

This candidate keeps the additive shift-composition hypothesis, absent from
the separate mean-limit theorem, and concludes a potentially RANDOM limit.
No actual percolation-energy instance, ergodic determinism, centered/triadic
normalization, chemical shape theorem, or Einstein relation is asserted.
The new import and wrapper are not yet compiled under project Lean4.35.
-/
@[expose] public section
namespace NearCritical.External
open MeasureTheory Filter Topology

/-- Existing almost-sure box-subadditive theorem on the project's lattice type. -/
theorem stationary_box_ae_limit {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (d : ℕ) (hd : 1 ≤ d)
    (τ : Vertex d → Ω → Ω) (hτ : ∀ z, MeasurePreserving (τ z) μ μ)
    (hτadd : ∀ z w ω, τ (z + w) ω = τ z (τ w ω))
    (f : Finset (Vertex d) → Ω → ℝ) (hmeas : ∀ A, Measurable (f A))
    (hstat : ∀ (A : Finset (Vertex d)) (z : Vertex d) (ω : Ω),
      f (A.map (Equiv.addRight z).toEmbedding) ω = f A (τ z ω))
    (hbd : ∃ C, ∀ A ω, 0 ≤ f A ω ∧ f A ω ≤ C * A.card)
    (hsub : ∀ B B₁ B₂ ω,
      LatticeProb.IsBoxSplit B B₁ B₂ → f B ω ≤ f B₁ ω + f B₂ ω) :
    ∃ L : Ω → ℝ, ∀ᵐ ω ∂μ,
      Tendsto (fun n : ℕ => f (LatticeProb.latticeCube d n) ω / (n : ℝ) ^ d)
        atTop (𝓝 (L ω)) :=
  LatticeProb.akcoglu_krengel μ d hd τ hτ hτadd f hmeas hstat hbd hsub

end NearCritical.External
