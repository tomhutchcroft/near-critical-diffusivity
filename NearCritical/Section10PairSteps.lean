module

public import NearCritical.Section10RouteLabels
public import NearCritical.Section10EnergyRoutes

/-! Shared steps of two actual routes.

`routeLab_shared_prod_le`: with step bound `rho` at the times where two routes
make the same step and `1` elsewhere, the product over the `2M` steps is at most
`rho ^ (2 N)`, `N` the number of common levels. This is the factor
`rho^{2N}` of `eq.nw.pair.mass` for actual routes, in the form used by
`entanglementBound`.
-/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open scoped Classical BigOperators

theorem routeLab_shared_card_le {D M : ℕ} (hM : 1 ≤ M) (X X' : ℕ → Fin D → ℤ) :
    ((Finset.range (2 * M)).filter (fun t => routeLab M X t = routeLab M X' t)).card ≤
      2 * (commonRouteLevels M X X').card := by
  refine le_trans ?_ (routeLab_common_le hM X X')
  unfold commonLabelCount
  refine Finset.card_le_card_of_injOn (routeLab M X) ?_ ?_
  · intro t ht
    have ht' := Finset.mem_filter.mp (Finset.mem_coe.mp ht)
    have hlt : t < 2 * M := Finset.mem_range.mp ht'.1
    refine Finset.mem_coe.mpr (Finset.mem_inter.mpr ⟨?_, ?_⟩)
    · exact Finset.mem_image.mpr ⟨t, by rw [Finset.mem_Ico]; omega, rfl⟩
    · exact Finset.mem_image.mpr ⟨t, by rw [Finset.mem_Ico]; omega, ht'.2.symm⟩
  · intro t _ t' _ h
    have := congrArg RouteLabel.rank h
    rwa [rank_routeLab hM, rank_routeLab hM] at this

theorem routeLab_shared_prod_le {D M : ℕ} (hM : 1 ≤ M) (X X' : ℕ → Fin D → ℤ) {ϱ : ℝ}
    (hϱ : 1 ≤ ϱ) :
    stepProd (fun t => if routeLab M X t = routeLab M X' t then ϱ else 1) (2 * M) 0 ≤
      ϱ ^ (2 * (commonRouteLevels M X X').card) := by
  rw [stepProd_eq_prod]
  simp only [Nat.zero_add]
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]
  exact pow_le_pow_right₀ hϱ (routeLab_shared_card_le hM X X')

end NearCritical.Section10
