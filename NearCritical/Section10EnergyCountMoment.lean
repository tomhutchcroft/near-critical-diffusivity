module

public import NearCritical.Section10WeightSecondMoment

/-! Section10 `prop.nw.main`, energy side: the arithmetico-geometric count moment
`E_{μ⊗μ}[(1+N) Λ₀^N 𝟙_{N≥1}]` is bounded by `(const) · M^{2-d}`.

This supplies the energy analogue of `exponential_count_moment_le_two`. The
arithmetico-geometric partial-sum bounds are proved elementarily (one telescoping
induction) so the module keeps the narrow `Section10WeightSecondMoment` import and
needs no analysis-library dependency; `geom_partial_le_inv` and
`positive_count_energy_moment_of_tail` are reused from there / `Section10EITMoments`.
 -/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open scoped BigOperators

/-- Telescoping identity for the arithmetico-geometric partial sum. -/
theorem arith_geom_telescope {r : ℝ} (H : ℕ) :
    (1 - r) * ∑ k ∈ Finset.range H, ((k : ℝ) + 1) * r ^ k
      = (∑ k ∈ Finset.range H, r ^ k) - (H : ℝ) * r ^ H := by
  induction H with
  | zero => simp
  | succ H ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, mul_add, ih]
    push_cast
    ring

/-- Degree-one arithmetico-geometric partial sum bound: `∑ (k+1) r^k ≤ 1/(1-r)²`. -/
theorem arith_geom_partial_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (H : ℕ) :
    (∑ k ∈ Finset.range H, ((k : ℝ) + 1) * r ^ k) ≤ 1 / (1 - r) ^ 2 := by
  have h1 : (0 : ℝ) < 1 - r := by linarith
  have hge : (1 - r) * (∑ k ∈ Finset.range H, ((k : ℝ) + 1) * r ^ k) ≤ 1 / (1 - r) := by
    rw [arith_geom_telescope H]
    have hgp := geom_partial_le_inv hr0 hr1 H
    have hnn : (0 : ℝ) ≤ (H : ℝ) * r ^ H := mul_nonneg (Nat.cast_nonneg H) (pow_nonneg hr0 H)
    linarith
  have hS' : (1 - r) * ((1 - r) * (∑ k ∈ Finset.range H, ((k : ℝ) + 1) * r ^ k)) ≤ 1 := by
    have h := mul_le_mul_of_nonneg_left hge h1.le
    rwa [mul_one_div_cancel h1.ne'] at h
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < (1 - r) ^ 2)]
  have he : (∑ k ∈ Finset.range H, ((k : ℝ) + 1) * r ^ k) * (1 - r) ^ 2
      = (1 - r) * ((1 - r) * (∑ k ∈ Finset.range H, ((k : ℝ) + 1) * r ^ k)) := by ring
  rw [he]; exact hS'

/-- Degree-"plus-two" arithmetico-geometric partial sum bound, as produced by
`positive_count_energy_moment_of_tail`: `∑ (k+2) r^k ≤ 2/(1-r)²`. -/
theorem arith_geom_partial_le_two {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (H : ℕ) :
    (∑ k ∈ Finset.range H, ((k : ℝ) + 2) * r ^ k) ≤ 2 / (1 - r) ^ 2 := by
  have h1 : (0 : ℝ) < 1 - r := by linarith
  have hsplit : (∑ k ∈ Finset.range H, ((k : ℝ) + 2) * r ^ k)
      = (∑ k ∈ Finset.range H, ((k : ℝ) + 1) * r ^ k) + ∑ k ∈ Finset.range H, r ^ k := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun k _ => by ring)
  rw [hsplit]
  have h2 := arith_geom_partial_le hr0 hr1 H
  have h3 := geom_partial_le_inv hr0 hr1 H
  have h4 : 1 / (1 - r) ≤ 1 / (1 - r) ^ 2 := by
    rw [div_le_div_iff₀ h1 (by positivity)]
    nlinarith [mul_nonneg hr0 h1.le]
  have hrw : (2 : ℝ) / (1 - r) ^ 2 = 1 / (1 - r) ^ 2 + 1 / (1 - r) ^ 2 := by ring
  rw [hrw]
  linarith

/-- Energy count-moment bound (energy analogue of `exponential_count_moment_le_two`):
with the source-form EIT tail `(C/Mpow) q^k` and the corrected `Λ q < 1`, the
positive-count energy moment is at most `(C/Mpow) · Λ · 2/(1-Λq)²`, i.e. of order
`M^{2-d}` once `Mpow = M^{d-2}`. No probabilistic premise beyond the tail. -/
theorem energy_count_moment_le {Y : Type*} [Fintype Y] (ν : Y → ℝ) (N : Y → ℕ)
    (hν : ∀ y, 0 ≤ ν y) (H : ℕ) (hN : ∀ y, N y ≤ H)
    {Λ C q Mpow : ℝ} (hΛ : 0 ≤ Λ) (hC : 0 ≤ C) (hq : 0 ≤ q)
    (hΛq : Λ * q < 1) (hMpow : 0 < Mpow)
    (htail : ∀ k, (∑ y, if k + 1 ≤ N y then ν y else 0) ≤ (C / Mpow) * q ^ k) :
    (∑ y, ν y * (if 1 ≤ N y then (1 + (N y : ℝ)) * Λ ^ (N y) else 0))
      ≤ (C / Mpow) * Λ * (2 / (1 - Λ * q) ^ 2) := by
  have hA : 0 ≤ C / Mpow := div_nonneg hC hMpow.le
  have hb := positive_count_energy_moment_of_tail ν N hν H hN hΛ hA hq htail
  refine hb.trans ?_
  exact mul_le_mul_of_nonneg_left
    (arith_geom_partial_le_two (mul_nonneg hΛ hq) hΛq H) (mul_nonneg hA hΛ)

end NearCritical.Section10
