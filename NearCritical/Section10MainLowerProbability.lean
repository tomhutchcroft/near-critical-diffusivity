module

public import NearCritical.Section10WeightSecondMoment
public import NearCritical.Section10WeightProbability

/-! Section10 `prop.nw.main`, first conclusion: `ℙ[A_L] ≥ c_A` with `c_A = 1/8`.

This assembles the paper's lower-bound probability from the already-proved
analytic engine:
* `exponential_count_moment_le_two` (the `E_{μ⊗μ}[Λ₀^N] ≤ 2` second-moment
  bound driven by the source-form EIT tail `sourceRoute_conditioned_EIT`), and
* `good_weight_probability_ge_one_eighth` (Paley–Zygmund).

The two ACTUAL-OBJECT inputs are kept as explicit hypotheses, matching the
paper:
* `hmean : ∑ μ·W = 1` — this is `lem.nw.mean` (`Eb[W] = 1`), owned by the
  `NestChainWeights`/`NestCubeWeights`/`NestFreshTube` bridge.
* `hpair : ∑ μ·W² ≤ ∑ ν·Λ₀^N` — the first display of `prop.nw.main`,
  `E[W²] = Σ μ(Γ)μ(Γ') Eb[ω_Γ ω_Γ' Ψ_fin] ≤ E_{μ⊗μ}[Λ₀^N]`, i.e.
  `eq.nw.pair.mass` together with the cube-indicator independence
  `Eb[ω_Γ ω_Γ'] ≤ (1-ε₀/4)^{-2N}` (bundled into `Λ₀`); owned by the
  `Section10PairMass` bridge.

Everything else — the EIT tail, the `Λ₀ q₀ < 1` corrected threshold, and the
Paley–Zygmund step — is discharged here from compiled results. -/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open scoped Classical BigOperators

/-- `prop.nw.main`, first conclusion. For the route law `μ` with weight `W` of
mean one, pair law `ν` with overlap count `N` satisfying the EIT tail and the
`eq.nw.pair.mass` second-moment relation, the good-weight event has probability
at least `c_A = 1/8`, uniformly in the truncation `H` and for every `Mpow`
exceeding the corrected threshold `C Λ₀/(1-Λ₀ q₀)`. -/
theorem good_event_probability_ge_one_eighth
    {X Y : Type*} [Fintype X] [Fintype Y]
    (μ W : X → ℝ) (ν : Y → ℝ) (N : Y → ℕ)
    (hμ : ∀ x, 0 ≤ μ x) (hprob : ∑ x, μ x = 1)
    (hW : ∀ x, 0 ≤ W x) (hmean : ∑ x, μ x * W x = 1)
    (hνnn : ∀ y, 0 ≤ ν y) (hνprob : ∑ y, ν y = 1)
    (H : ℕ) (hN : ∀ y, N y ≤ H)
    {Λ C q Mpow : ℝ} (hΛ : 0 ≤ Λ) (hC : 0 ≤ C) (hq : 0 ≤ q)
    (hΛq : Λ * q < 1) (hMpow : 0 < Mpow)
    (htail : ∀ k, (∑ y, if k + 1 ≤ N y then ν y else 0) ≤ (C / Mpow) * q ^ k)
    (hlarge : C * Λ / (1 - Λ * q) ≤ Mpow)
    (hpair : (∑ x, μ x * (W x) ^ 2) ≤ ∑ y, ν y * Λ ^ (N y)) :
    (1 / 8 : ℝ) ≤ ∑ x, if (1 / 2 : ℝ) ≤ W x then μ x else 0 := by
  have hsecond : (∑ x, μ x * (W x) ^ 2) ≤ 2 :=
    hpair.trans
      (exponential_count_moment_le_two ν N hνnn hνprob H hN hΛ hC hq hΛq hMpow htail hlarge)
  exact good_weight_probability_ge_one_eighth μ W hμ hprob hW hmean hsecond

end NearCritical.Section10
