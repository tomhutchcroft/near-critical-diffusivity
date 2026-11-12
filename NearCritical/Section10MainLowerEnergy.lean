module

public import NearCritical.Section10EnergyCountMoment

/-! Section10 `prop.nw.main`, second conclusion: the energy bound
`Eb[𝓔_*(B_L,a,θ) 𝟙_{A_L}] ≤ C L^{2-d} ℓ₀⁶`, reduced to its two actual-object
inputs plus the already-proved energy count moment.

The source chain is
  `Eb[𝓔_* 𝟙_{A_L}] ≤ 4 · E_{μ⊗μ}[Ψ_fin |γ∩γ'|]`           (henergy)
  `               ≤ B · E_{μ⊗μ}[(1+N) Λ₀^N 𝟙_{N≥1}]`        (hoverlap)
  `               ≤ B · (const) · M^{2-d} ≤ C L^{2-d} ℓ₀⁶`   (energy_count_moment_le)
where `B = C ℓ₀² ℓ₀^{6-d}` collects the per-overlap length budget of
`lem.nw.overlap` and the one-tube factor of `eq.nw.pair.overlap`.

Only the last step is analytic and is discharged here from
`energy_count_moment_le`. The two inputs are kept explicit, matching the paper:
* `henergy` — `Eb[𝓔_* 𝟙_{A_L}] ≤ 4 · overlapExp`; this is
  `normalized_path_flow_energy_le_four_overlaps` evaluated at the actual flow `θ`
  and taken in `μ⊗μ`-expectation.
* `hoverlap` — `overlapExp ≤ B · E_{μ⊗μ}[(1+N) Λ₀^N 𝟙_{N≥1}]`; this is
  `lem.nw.overlap` (`route_pieces_overlap_le_entanglements`) together with
  `eq.nw.pair.overlap`, both owned by the route-piece / pair-mass bridges.
 -/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open scoped BigOperators

/-- `prop.nw.main`, energy conclusion, reduced to the flow-energy and overlap
inputs. For the pair law `ν` with overlap count `N` satisfying the EIT tail, the
expected energy on the good event is at most `4 · B · (C/Mpow) · Λ₀ · 2/(1-Λ₀q₀)²`,
which is of order `M^{2-d}` (hence `L^{2-d}ℓ₀⁶`). -/
theorem energy_on_good_event_le {Y : Type*} [Fintype Y] (ν : Y → ℝ) (N : Y → ℕ)
    (hν : ∀ y, 0 ≤ ν y) (H : ℕ) (hN : ∀ y, N y ≤ H)
    {Λ C q Mpow Eexp overlapExp B : ℝ}
    (hΛ : 0 ≤ Λ) (hC : 0 ≤ C) (hq : 0 ≤ q) (hΛq : Λ * q < 1) (hMpow : 0 < Mpow)
    (hB : 0 ≤ B)
    (htail : ∀ k, (∑ y, if k + 1 ≤ N y then ν y else 0) ≤ (C / Mpow) * q ^ k)
    (henergy : Eexp ≤ 4 * overlapExp)
    (hoverlap : overlapExp ≤
      B * (∑ y, ν y * (if 1 ≤ N y then (1 + (N y : ℝ)) * Λ ^ (N y) else 0))) :
    Eexp ≤ 4 * B * ((C / Mpow) * Λ * (2 / (1 - Λ * q) ^ 2)) := by
  have hcm := energy_count_moment_le ν N hν H hN hΛ hC hq hΛq hMpow htail
  calc
    Eexp ≤ 4 * overlapExp := henergy
    _ ≤ 4 * (B * (∑ y, ν y * (if 1 ≤ N y then (1 + (N y : ℝ)) * Λ ^ (N y) else 0))) :=
        mul_le_mul_of_nonneg_left hoverlap (by norm_num)
    _ ≤ 4 * (B * ((C / Mpow) * Λ * (2 / (1 - Λ * q) ^ 2))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hcm hB) (by norm_num)
    _ = 4 * B * ((C / Mpow) * Λ * (2 / (1 - Λ * q) ^ 2)) := by ring

end NearCritical.Section10
