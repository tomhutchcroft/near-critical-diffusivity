module

public import NearCritical.Section10EnergyRoutes
public import NearCritical.Section10RouteLaw

/-! `prop.nw.main`, energy conclusion, with the actual route law.

`sourceRoute_energy_le`: for the survival-conditioned route law, any `En >= 0`
bounded pointwise by the weighted marked pair values (the energy of the flow on
`{W >= 1/2}`), under the one-step estimates on every reveal atom and a per-pair
bound `E[omega omega' * entanglementBound] <= Bc (1 + N) Lambda^N 1{N >= 1}`,

  `E[En] <= 4 Pb Bc * 2 (C / M^(D-1)) Lambda / (1 - Lambda q0)^2`.

With `Pb ~ l0^2`, `Bc ~ l0^(6-d)` and `M ~ L / l0` this is the source bound
`C L^(2-d) l0^6`. The exponential intersection tail is the proved `routeLaw_tail`.

Still hypotheses: the flows and `lem.nw.overlap` (through `hEn`), the one-step
estimates of `lem.nw.H`, and the per-pair bound (step counts for actual routes
and the cube-pair factor).
-/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open MeasureTheory
open scoped Classical BigOperators

theorem sourceRoute_energy_le {D : ℕ} (hD : 3 ≤ D) :
    ∃ (q0 C : ℝ) (M₀ : ℕ), 0 < q0 ∧ q0 < 1 ∧ 0 ≤ C ∧ ∀ M ≥ M₀,
    ∀ {d : ℕ} {X Φ : Type*} [Fintype X] [Fintype Φ] (p q : unitInterval)
      (ρr : Configuration d × Configuration d → Φ) (Sx : Φ → Finset (LBond d))
      (_hρr : ∀ F, IsLocal (Sx F) (fun z => if ρr z = F then (1:ℝ) else 0))
      (w : SourceRoute D M → Φ → ℝ) (_hw : ∀ γ F, 0 ≤ w γ F)
      (B : SourceRoute D M → SourceRoute D M → Φ → ℕ → Finset (LBond d))
      (_hB : ∀ γ γ' F i j, i ≠ j → Disjoint (B γ γ' F i) (B γ γ' F j))
      (_hSB : ∀ γ γ' F j, Disjoint (Sx F) (B γ γ' F j))
      (k : SourceRoute D M → Φ → ℕ → X → X → Configuration d × Configuration d → ℝ)
      (_hk0 : ∀ γ F t x y z, 0 ≤ k γ F t x y z)
      (_hK : ∀ γ γ' F t x y, IsLocal (B γ γ' F t) (pairKernel (k γ F) (k γ' F) t x y))
      (τ σ : SourceRoute D M → SourceRoute D M → Φ → ℕ → X × X → X × X →
        Configuration d × Configuration d → ℝ)
      (_hτ : ∀ γ γ' F t x y, IsLocal (B γ γ' F t) (τ γ γ' F t x y))
      (_hσ : ∀ γ γ' F t x y, IsLocal (B γ γ' F t) (σ γ γ' F t x y))
      (_hτ01 : ∀ γ γ' F t x y z, 0 ≤ τ γ γ' F t x y z ∧ τ γ γ' F t x y z ≤ 1)
      (_hσ0 : ∀ γ γ' F t x y z, 0 ≤ σ γ γ' F t x y z)
      (ρ δ : SourceRoute D M → SourceRoute D M → Φ → ℕ → ℝ)
      (_hρ : ∀ γ γ' F t, 1 ≤ ρ γ γ' F t) (_hδ : ∀ γ γ' F t, 0 ≤ δ γ γ' F t) {θ : ℝ}
      (_hθ0 : 0 ≤ θ) (_hθ1 : θ < 1)
      (_hrow : ∀ γ γ' F t x, ∑ y, (∫ z, pairKernel (k γ F) (k γ' F) t x y z
        ∂((percolation d p).prod (percolation d q))) ≤ ρ γ γ' F t)
      (φ : SourceRoute D M → SourceRoute D M → Φ → ℕ → X × X → ℝ)
      (_hφ0 : ∀ γ γ' F t x, 0 ≤ φ γ γ' F t x)
      (_hpersist : ∀ γ γ' F t x, ∑ y, (∫ z, pairKernel (k γ F) (k γ' F) t x y z *
        τ γ γ' F t x y z ∂((percolation d p).prod (percolation d q))) * φ γ γ' F (t+1) y ≤
        θ * ∑ y, ∫ z, pairKernel (k γ F) (k γ' F) t x y z * τ γ γ' F t x y z ∂((percolation d p).prod (percolation d q)))
      (_henter : ∀ γ γ' F t x, ∑ y, (∫ z, pairKernel (k γ F) (k γ' F) t x y z *
          (1 - τ γ γ' F t x y z) ∂((percolation d p).prod (percolation d q))) * φ γ γ' F (t+1) y ≤
        φ γ γ' F t x - (∑ y, ∫ z, pairKernel (k γ F) (k γ' F) t x y z *
          τ γ γ' F t x y z ∂((percolation d p).prod (percolation d q))) + δ γ γ' F t)
      (_hsite : ∀ γ γ' F t x, ∑ y, (∫ z, pairKernel (k γ F) (k γ' F) t x y z *
        (1 - τ γ γ' F t x y z) * σ γ γ' F t x y z
        ∂((percolation d p).prod (percolation d q))) ≤ δ γ γ' F t)
      (m : ℕ) (x₀ : SourceRoute D M → Φ → X) {Pb Bc Λ : ℝ} (_hPb : 0 ≤ Pb) (_hBc : 0 ≤ Bc)
      (_hΛ : 0 ≤ Λ) (_hΛq : Λ * q0 < 1)
      (En : Configuration d × Configuration d → ℝ) (_hEn0 : ∀ z, 0 ≤ En z)
      (_hEn : ∀ z, En z ≤ 4 * (Pb * ∑ γ, ∑ γ', (routeLaw D M γ * routeLaw D M γ') *
        ((w γ (ρr z) * w γ' (ρr z)) *
        markedValue (pairKernel (k γ (ρr z)) (k γ' (ρr z)))
          (fun t x y z' => pairKernel (k γ (ρr z)) (k γ' (ρr z)) t x y z' *
            (2 * τ γ γ' (ρr z) t x y z' +
              (1 - τ γ γ' (ρr z) t x y z') * σ γ γ' (ρr z) t x y z')) m 0
          (x₀ γ (ρr z), x₀ γ' (ρr z)) z)))
      (_hper : ∀ γ γ', (∫ z, (w γ (ρr z) * w γ' (ρr z)) *
          entanglementBound (ρ γ γ' (ρr z)) (δ γ γ' (ρr z)) θ
            (φ γ γ' (ρr z) 0 (x₀ γ (ρr z), x₀ γ' (ρr z))) m
          ∂((percolation d p).prod (percolation d q))) ≤
        Bc * (if 1 ≤ routeCommonLevels D M (γ, γ') then
          (1 + (routeCommonLevels D M (γ, γ') : ℝ)) * Λ ^ routeCommonLevels D M (γ, γ')
          else 0)),
      (∫ z, En z ∂((percolation d p).prod (percolation d q))) ≤
        4 * (Pb * (Bc * (2 * (C / (M:ℝ) ^ (D-1)) * Λ / (1 - Λ * q0) ^ 2))) := by
  obtain ⟨q0, C, M₀, hq0, hq1, hC, hlaw⟩ := routeLaw_tail hD
  refine ⟨q0, C, max M₀ 1, hq0, hq1, hC, ?_⟩
  intro M hM d X Φ _ _ p q ρr Sx hρr w hw B hB hSB k hk0 hK τ σ hτ hσ hτ01 hσ0 ρ δ hρ hδ θ
    hθ0 hθ1 hrow φ hφ0 hpersist henter hsite m x₀ Pb Bc Λ hPb hBc hΛ hΛq En hEn0 hEn hper
  obtain ⟨hμ0, _, htail⟩ := hlaw M ((le_max_left _ _).trans hM)
  have hM1 : 1 ≤ M := (le_max_right _ _).trans hM
  have hMpow : (0:ℝ) < (M:ℝ) ^ (D-1) := pow_pos (by exact_mod_cast hM1) _
  have h1 := energy_expectation_le p q ρr Sx hρr (routeLaw D M) hμ0 w hw B hB hSB k hk0 hK τ σ
    hτ hσ hτ01 hσ0 ρ δ hρ hδ hθ0 hθ1 hrow φ hφ0 hpersist henter hsite m x₀ hPb En hEn0 hEn
  refine h1.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hPb) (by norm_num))
  exact route_pair_sum_le (routeLaw D M) hμ0 (routeCommonLevels D M) M
    (routeCommonLevels_le D M) hΛ (div_nonneg hC hMpow.le) hq0.le hΛq hBc htail _ hper

end NearCritical.Section10
