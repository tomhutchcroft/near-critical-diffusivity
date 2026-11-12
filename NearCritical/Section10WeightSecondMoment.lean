module

public import NearCritical.Section10EITMoments

/-! Section10 prop.nw.main, second moment of W: from a source-form EIT tail
`A*q^k` with `A = C/M^(D-1)` and corrected `Λ*q < 1`, the exponential count
moment is at most 2 for all large M, uniformly in the truncation H.
Draft, not compiled. Deterministic; no probabilistic premise beyond the tail. -/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open scoped Classical BigOperators
variable {X : Type*} [Fintype X]

/-- Finite geometric sums are bounded by the infinite one. -/
theorem geom_partial_le_inv {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (H : ℕ) :
    (∑ k ∈ Finset.range H, r^k) ≤ 1/(1-r) := by
  have h1 : 0 < 1-r := by linarith
  rw [le_div_iff₀ h1, geom_sum_mul_neg]
  linarith [pow_nonneg hr0 H]

/-- Explicit threshold: once `C*Λ/(1-Λq) ≤ M^(D-1)` the moment is at most 2. -/
theorem exponential_count_moment_le_two (μ : X → ℝ) (N : X → ℕ)
    (hμ : ∀ x, 0 ≤ μ x) (hprob : ∑ x, μ x = 1)
    (H : ℕ) (hN : ∀ x, N x ≤ H) {Λ C q Mpow : ℝ}
    (hΛ : 0 ≤ Λ) (hC : 0 ≤ C) (hq : 0 ≤ q) (hΛq : Λ*q < 1) (hM : 0 < Mpow)
    (htail : ∀ k, (∑ x, if k+1 ≤ N x then μ x else 0) ≤ (C/Mpow)*q^k)
    (hlarge : C*Λ/(1-Λ*q) ≤ Mpow) :
    (∑ x, μ x*Λ^(N x)) ≤ 2 := by
  have hA : 0 ≤ C/Mpow := div_nonneg hC hM.le
  have hb := exponential_count_moment_of_tail μ N hμ hprob H hN hΛ hA hq htail
  have hg := geom_partial_le_inv (mul_nonneg hΛ hq) hΛq H
  have h1 : 0 < 1-Λ*q := by linarith
  have hAΛ : 0 ≤ C/Mpow*Λ := mul_nonneg hA hΛ
  have hstep : C/Mpow*Λ*(∑ k ∈ Finset.range H, (Λ*q)^k) ≤ C/Mpow*Λ*(1/(1-Λ*q)) :=
    mul_le_mul_of_nonneg_left hg hAΛ
  have hval : C/Mpow*Λ*(1/(1-Λ*q)) = (C*Λ/(1-Λ*q))/Mpow := by
    field_simp [hM.ne', h1.ne'] <;> ring_nf
  have hle1 : (C*Λ/(1-Λ*q))/Mpow ≤ 1 := (div_le_one hM).mpr hlarge
  linarith

/-- Uniform-in-M form: with Mpow = M^(D-1), D ≥ 2, there is one M₁. -/
theorem exists_threshold_moment_le_two {Λ C q : ℝ} (D : ℕ) (hD : 2 ≤ D)
    (hΛq : Λ*q < 1) :
    ∃ M₁ : ℕ, ∀ M ≥ M₁, C*Λ/(1-Λ*q) ≤ (M:ℝ)^(D-1) := by
  obtain ⟨M₁, hM₁⟩ := exists_nat_ge (C*Λ/(1-Λ*q))
  refine ⟨max M₁ 1, fun M hM => ?_⟩
  have hM1 : (1:ℝ) ≤ M := by exact_mod_cast (le_max_right _ _).trans hM
  have hMM : (M₁:ℝ) ≤ M := by exact_mod_cast (le_max_left _ _).trans hM
  calc C*Λ/(1-Λ*q) ≤ M := hM₁.trans hMM
    _ = (M:ℝ)^1 := (pow_one _).symm
    _ ≤ (M:ℝ)^(D-1) := pow_le_pow_right₀ hM1 (by omega)

end NearCritical.Section10
