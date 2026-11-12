module

public import LatticeProb.Prob.AkcogluKrengel
public import NearCritical.Bernoulli

/-!
Imported multiparameter subadditive mean convergence from Lattice-Probability,
commit 9d44b4d4670df393bb86ac5a4e042f215001cddf (Apache-2.0).

Candidate interface for the source's standard finite-energy mean-limit step.
The actual energy field, split geometry, translation stationarity and bound
must be supplied by the project. No conductivity/diffusivity identification,
almost-sure multidimensional homogenization, or main theorem is asserted.
This new import is not yet compiled under Lean4.35; see third_party metadata.
-/
@[expose] public section
namespace NearCritical.External
open MeasureTheory Filter Topology

/-- Existing general mean-limit theorem, with the project's lattice vertex type. -/
theorem stationary_box_mean_limit {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (d : ℕ) (hd : 1 ≤ d)
    (τ : Vertex d → Ω → Ω) (hτ : ∀ z, MeasurePreserving (τ z) μ μ)
    (f : Finset (Vertex d) → Ω → ℝ) (hmeas : ∀ A, Measurable (f A))
    (hstat : ∀ (A : Finset (Vertex d)) (z : Vertex d) (ω : Ω),
      f (A.map (Equiv.addRight z).toEmbedding) ω = f A (τ z ω))
    (hbd : ∃ C, ∀ A ω, 0 ≤ f A ω ∧ f A ω ≤ C * A.card)
    (hsub : ∀ B B₁ B₂ ω,
      LatticeProb.IsBoxSplit B B₁ B₂ → f B ω ≤ f B₁ ω + f B₂ ω) :
    ∃ L : ℝ, Tendsto
      (fun n : ℕ => (∫ ω, f (LatticeProb.latticeCube d n) ω ∂μ) / (n : ℝ) ^ d)
      atTop (𝓝 L) :=
  LatticeProb.akcoglu_krengel_mean μ d hd τ hτ f hmeas hstat hbd hsub

end NearCritical.External
