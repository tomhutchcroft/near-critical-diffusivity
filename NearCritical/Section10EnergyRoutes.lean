module

public import NearCritical.Section10EnergyExpectation
public import NearCritical.Section10EITGeometric

/-! Sum over route pairs in the energy bound of `prop.nw.main`.

* `stepProd_eq_prod`, `stepSum_eq_sum`: the step products and sums of the pair
  estimate as ordinary finite products and sums.
* `route_pair_sum_le`: if each pair term is at most
  `Bc * (1 + N) Lambda^N 1{N >= 1}` and the common-level count `N` has the
  exponential tail `A q^k` under `mu x mu`, then

  `sum_{γ,γ'} mu mu' I(γ,γ') <= Bc * 2 A Lambda / (1 - Lambda q)^2`.

With `A = C / M^(D-1)` from `routeLaw_tail` this is the last display of the
proof of `prop.nw.main` (5789--5791).
-/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open scoped Classical BigOperators

lemma stepProd_eq_prod (ρ : ℕ → ℝ) : ∀ m t, stepProd ρ m t = ∏ j ∈ Finset.range m, ρ (t + j) := by
  intro m
  induction m with
  | zero => intro t; simp [stepProd]
  | succ m ih =>
    intro t
    rw [stepProd, ih (t+1), Finset.prod_range_succ']
    simp only [Nat.add_zero]
    rw [mul_comm]
    congr 1
    exact Finset.prod_congr rfl (fun j _ => by rw [Nat.add_assoc, Nat.add_comm 1 j])

lemma stepSum_eq_sum (δ : ℕ → ℝ) : ∀ m t, stepSum δ m t = ∑ j ∈ Finset.range m, δ (t + j) := by
  intro m
  induction m with
  | zero => intro t; simp [stepSum]
  | succ m ih =>
    intro t
    rw [stepSum, ih (t+1), Finset.sum_range_succ']
    simp only [Nat.add_zero]
    rw [add_comm]
    congr 1
    exact Finset.sum_congr rfl (fun j _ => by rw [Nat.add_assoc, Nat.add_comm 1 j])

theorem route_pair_sum_le {Γ : Type*} [Fintype Γ] (μ : Γ → ℝ) (hμ : ∀ γ, 0 ≤ μ γ)
    (N : Γ × Γ → ℕ) (H : ℕ) (hN : ∀ y, N y ≤ H) {Λ A q Bc : ℝ} (hΛ : 0 ≤ Λ) (hA : 0 ≤ A)
    (hq : 0 ≤ q) (hsmall : Λ * q < 1) (hBc : 0 ≤ Bc)
    (htail : ∀ k, (∑ y : Γ × Γ, if k + 1 ≤ N y then μ y.1 * μ y.2 else 0) ≤ A * q ^ k)
    (I : Γ → Γ → ℝ)
    (hI : ∀ γ γ', I γ γ' ≤ Bc * (if 1 ≤ N (γ, γ') then
      (1 + (N (γ, γ') : ℝ)) * Λ ^ N (γ, γ') else 0)) :
    (∑ γ, ∑ γ', (μ γ * μ γ') * I γ γ') ≤ Bc * (2 * A * Λ / (1 - Λ * q) ^ 2) := by
  have hmom := positive_count_energy_moment_closed (fun y : Γ × Γ => μ y.1 * μ y.2) N
    (fun y => mul_nonneg (hμ y.1) (hμ y.2)) H hN hΛ hA hq hsmall htail
  rw [Fintype.sum_prod_type] at hmom
  calc (∑ γ, ∑ γ', (μ γ * μ γ') * I γ γ')
      ≤ ∑ γ, ∑ γ', (μ γ * μ γ') * (Bc * (if 1 ≤ N (γ, γ') then
          (1 + (N (γ, γ') : ℝ)) * Λ ^ N (γ, γ') else 0)) :=
        Finset.sum_le_sum (fun γ _ => Finset.sum_le_sum (fun γ' _ =>
          mul_le_mul_of_nonneg_left (hI γ γ') (mul_nonneg (hμ γ) (hμ γ'))))
    _ = Bc * ∑ γ, ∑ γ', (μ γ * μ γ') * (if 1 ≤ N (γ, γ') then
          (1 + (N (γ, γ') : ℝ)) * Λ ^ N (γ, γ') else 0) := by
        simp only [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun γ _ => Finset.sum_congr rfl (fun γ' _ => by ring))
    _ ≤ Bc * (2 * A * Λ / (1 - Λ * q) ^ 2) := mul_le_mul_of_nonneg_left hmom hBc

end NearCritical.Section10
