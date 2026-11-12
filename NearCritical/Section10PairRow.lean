module

public import NearCritical.Section10Survivor
public import NearCritical.Section10PairOverlap

/-! Mass of one synchronous pair step of a nest rule (`eq.nw.pair.mass`, Step 1).

`NestRule.pair_row_le`: for two routes at time `t`, the mean total weight of the
pair kernel is at most `rho` if the two routes make the same step (a shared
step: `E[iota iota'] <= 1/s'`), and at most `1` otherwise (different steps read
disjoint blocks, so the weights are independent with mean one).

This is hypothesis `_hrow` of `sourceRoute_energy_le` for any `NestRule`, with
`rho t = rho` at shared times and `1` elsewhere.
-/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open MeasureTheory
open scoped Classical BigOperators

theorem NestRule.pair_row_le {D M d : ℕ} {p q : unitInterval} {ϱ κ : ℝ} {X Φ : Type}
    [Fintype X] [Fintype Φ] (R : NestRule D M d p q ϱ κ X Φ) (hϱ : 1 ≤ ϱ)
    (γ γ' : SourceRoute D M) (F : Φ) (t : ℕ) (x : X × X) :
    (∑ y : X × X, ∫ z, pairKernel (R.kernel γ F) (R.kernel γ' F) t x y z
      ∂((percolation d p).prod (percolation d q))) ≤
      (if routeLab M γ.position t = routeLab M γ'.position t then ϱ else 1) := by
  have hϱ0 : 0 < ϱ := lt_of_lt_of_le one_pos hϱ
  have hspos : ∀ (γ : SourceRoute D M) (x : X), 0 <
      localSuccessProbability p q (R.Bl F (routeLab M γ.position t)) (R.a γ F t x) :=
    fun γ x => lt_of_lt_of_le (inv_pos.mpr hϱ0) (R.hs γ F t x)
  have hloc1 : ∀ y : X, IsLocal (R.Bl F (routeLab M γ.position t)) (R.kernel γ F t x.1 y) :=
    fun y => stepKernel_isLocal _ _ _ _ y
  have hloc2 : ∀ y : X, IsLocal (R.Bl F (routeLab M γ'.position t)) (R.kernel γ' F t x.2 y) :=
    fun y => stepKernel_isLocal _ _ _ _ y
  have hint : ∀ y : X × X, Integrable (pairKernel (R.kernel γ F) (R.kernel γ' F) t x y)
      ((percolation d p).prod (percolation d q)) :=
    fun y => ((hloc1 y.1).mul_union (hloc2 y.2)).integrable p q
  by_cases hl : routeLab M γ.position t = routeLab M γ'.position t
  · rw [if_pos hl, ← integral_finsetSum _ (fun y _ => hint y)]
    have h := stepKernel_pair_integral_le p q (R.Bl F (routeLab M γ.position t))
      (R.Bl F (routeLab M γ'.position t)) (R.a γ F t x.1) (R.a γ' F t x.2)
      (R.o γ F t x.1) (R.o γ' F t x.2) (R.ho γ F t x.1) (R.ho γ' F t x.2)
      (hspos γ x.1) (hspos γ' x.2)
    exact h.trans ((inv_le_comm₀ (hspos γ' x.2) hϱ0).mpr (R.hs γ' F t x.2))
  · rw [if_neg hl]
    have hd : Disjoint (R.Bl F (routeLab M γ.position t))
        (R.Bl F (routeLab M γ'.position t)) := R.hBl F _ _ hl
    have hprod : ∀ y : X × X, (∫ z, pairKernel (R.kernel γ F) (R.kernel γ' F) t x y z
        ∂((percolation d p).prod (percolation d q))) =
        (∫ z, R.kernel γ F t x.1 y.1 z ∂((percolation d p).prod (percolation d q))) *
          ∫ z, R.kernel γ' F t x.2 y.2 z ∂((percolation d p).prod (percolation d q)) :=
      fun y => IsLocal.integral_mul p q hd (hloc1 y.1) (hloc2 y.2)
    rw [Finset.sum_congr rfl (fun y _ => hprod y), Fintype.sum_prod_type]
    simp only []
    rw [← Fintype.sum_mul_sum,
      ← integral_finsetSum _ (fun y _ => (hloc1 y).integrable p q),
      ← integral_finsetSum _ (fun y _ => (hloc2 y).integrable p q)]
    have h1 := stepKernel_integral_eq_one p q (R.Bl F (routeLab M γ.position t))
      (R.a γ F t x.1) (R.o γ F t x.1) (R.ho γ F t x.1) (hspos γ x.1)
    have h2 := stepKernel_integral_eq_one p q (R.Bl F (routeLab M γ'.position t))
      (R.a γ' F t x.2) (R.o γ' F t x.2) (R.ho γ' F t x.2) (hspos γ' x.2)
    have h1' : (∫ z, ∑ y, R.kernel γ F t x.1 y z
        ∂((percolation d p).prod (percolation d q))) = 1 := h1
    have h2' : (∫ z, ∑ y, R.kernel γ' F t x.2 y z
        ∂((percolation d p).prod (percolation d q))) = 1 := h2
    rw [h1', h2', mul_one]

end NearCritical.Section10
