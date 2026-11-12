module

public import NearCritical.Section10PairSteps
public import NearCritical.Section10RevealedOverlap

/-! Meeting times of two routes and the closed form of the entanglement bound.

* `routeLab_meet_card_le`: two routes are at the same site at no more than
  `2 N` of the `2M` step times (`N` = number of common levels).
* `stepSum_indicator`: a step cost `delta0` charged at the times in a set costs
  `delta0 * #times` in total.
* `entanglementBound_le`: if the product of step bounds is at most `Lam^N`, the
  total step cost at most `delta0 * c * N` and there is no entanglement risk at
  the start, then

  `entanglementBound <= (2/(1-theta) + 1) c delta0 * (1 + N) Lam^N 1{N >= 1}`.

This is the shape `C l0^(6-d) (1 + N) rho^(2N) 1{N >= 1}` of
`eq.nw.pair.overlap`.
-/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open scoped Classical BigOperators

theorem routeLab_meet_card_le {D M : ℕ} (X X' : ℕ → Fin D → ℤ) :
    ((Finset.range (2 * M)).filter
      (fun t => (routeLab M X t).site = (routeLab M X' t).site)).card ≤
      2 * (commonRouteLevels M X X').card := by
  have hcard : ((commonRouteLevels M X X') ×ˢ (Finset.range 2)).card =
      2 * (commonRouteLevels M X X').card := by
    rw [Finset.card_product, Finset.card_range, mul_comm]
  rw [← hcard]
  refine Finset.card_le_card_of_injOn (fun t : ℕ => (t / 2, t % 2)) ?_ ?_
  · intro t ht
    have ht' := Finset.mem_filter.mp (Finset.mem_coe.mp ht)
    have hlt : t < 2 * M := Finset.mem_range.mp ht'.1
    have h1 := routeLab_site (M := M) X hlt
    have h2 := routeLab_site (M := M) X' hlt
    rw [← ht'.2] at h2
    refine Finset.mem_coe.mpr (Finset.mem_product.mpr ⟨?_, ?_⟩)
    · show t / 2 ∈ commonRouteLevels M X X'
      rw [← h1.2]
      unfold commonRouteLevels
      simp only [Finset.mem_image, Finset.mem_inter]
      exact ⟨_, ⟨h1.1, h2.1⟩, rfl⟩
    · exact Finset.mem_range.mpr (Nat.mod_lt _ (by norm_num))
  · intro t _ t' _ h
    simp only [Prod.mk.injEq] at h
    omega

theorem stepSum_indicator (P : ℕ → Prop) (δ₀ : ℝ) (m : ℕ) :
    stepSum (fun t => if P t then δ₀ else 0) m 0 =
      δ₀ * (((Finset.range m).filter P).card : ℝ) := by
  rw [stepSum_eq_sum]
  simp only [Nat.zero_add]
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero, nsmul_eq_mul, mul_comm]

theorem entanglementBound_le {ρ δ : ℕ → ℝ} {θ Lam δ₀ c : ℝ} {m N : ℕ} (hθ0 : 0 ≤ θ)
    (hθ1 : θ < 1) (hLam : 1 ≤ Lam) (hδ₀ : 0 ≤ δ₀) (hc : 0 ≤ c)
    (hP0 : 0 ≤ stepProd ρ m 0) (hP : stepProd ρ m 0 ≤ Lam ^ N)
    (hS0 : 0 ≤ stepSum δ m 0) (hS : stepSum δ m 0 ≤ δ₀ * (c * (N : ℝ))) :
    entanglementBound ρ δ θ 0 m ≤
      ((2 * (1 - θ)⁻¹ + 1) * (c * δ₀)) *
        (if 1 ≤ N then (1 + (N : ℝ)) * Lam ^ N else 0) := by
  have hlam : 0 < (1 - θ)⁻¹ := inv_pos.mpr (by linarith)
  have hk : 0 ≤ 2 * (1 - θ)⁻¹ + 1 := by positivity
  have hLamN : 0 ≤ Lam ^ N := pow_nonneg (zero_le_one.trans hLam) N
  have heq : entanglementBound ρ δ θ 0 m =
      stepProd ρ m 0 * ((2 * (1 - θ)⁻¹ + 1) * stepSum δ m 0) := by
    unfold entanglementBound
    ring
  rw [heq]
  by_cases hN : 1 ≤ N
  · rw [if_pos hN]
    have hNR : (0:ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    have h1 : (2 * (1 - θ)⁻¹ + 1) * stepSum δ m 0 ≤
        (2 * (1 - θ)⁻¹ + 1) * (δ₀ * (c * (N : ℝ))) := mul_le_mul_of_nonneg_left hS hk
    have h2 : stepProd ρ m 0 * ((2 * (1 - θ)⁻¹ + 1) * stepSum δ m 0) ≤
        Lam ^ N * ((2 * (1 - θ)⁻¹ + 1) * (δ₀ * (c * (N : ℝ)))) :=
      mul_le_mul hP h1 (mul_nonneg hk hS0) hLamN
    refine h2.trans ?_
    have h3 : (2 * (1 - θ)⁻¹ + 1) * (δ₀ * (c * (N : ℝ))) ≤
        (2 * (1 - θ)⁻¹ + 1) * (c * δ₀) * (1 + (N : ℝ)) := by
      have : δ₀ * (c * (N : ℝ)) ≤ (c * δ₀) * (1 + (N : ℝ)) := by
        nlinarith [mul_nonneg hc hδ₀]
      calc (2 * (1 - θ)⁻¹ + 1) * (δ₀ * (c * (N : ℝ)))
          ≤ (2 * (1 - θ)⁻¹ + 1) * ((c * δ₀) * (1 + (N : ℝ))) :=
            mul_le_mul_of_nonneg_left this hk
        _ = _ := by ring
    calc Lam ^ N * ((2 * (1 - θ)⁻¹ + 1) * (δ₀ * (c * (N : ℝ))))
        ≤ Lam ^ N * ((2 * (1 - θ)⁻¹ + 1) * (c * δ₀) * (1 + (N : ℝ))) :=
          mul_le_mul_of_nonneg_left h3 hLamN
      _ = _ := by ring
  · rw [if_neg hN, mul_zero]
    have hN0 : N = 0 := by omega
    rw [hN0] at hS
    simp only [Nat.cast_zero, mul_zero] at hS
    have hSz : stepSum δ m 0 = 0 := le_antisymm hS hS0
    rw [hSz]
    simp

end NearCritical.Section10
