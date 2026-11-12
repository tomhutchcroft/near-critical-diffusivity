module

public import NearCritical.Section10CoupledWeight
public import NearCritical.Section10MergeSchedule

/-! `P[W >= 1/2] >= 1/8` on the actual coupled law, for chains whose steps read
labelled blocks (tubes, start and exit sites).

Compared with `coupled_good_weight_probability`, the joint schedules, their
freshness, the step counts and the pairwise disjointness of a chain's own blocks
are no longer hypotheses: they follow from
* blocks of distinct labels are disjoint and avoid the explored bonds,
* a rank on labels increases strictly along every route.
The cube-pair hypothesis is stated with the number of common labels.
-/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open MeasureTheory
open scoped Classical BigOperators

/-- Number of labels common to the first `n`, `n'` steps of two label sequences. -/
def commonLabelCount {E : Type*} (lab lab' : ℕ → E) (n n' : ℕ) : ℕ :=
  ((Finset.Ico 0 (0+n)).image lab ∩ (Finset.Ico 0 (0+n')).image lab').card

theorem labelled_good_weight_probability {d : ℕ} {X Φ Γ E : Type*}
    [Fintype X] [Fintype Φ] [Fintype Γ] (p q : unitInterval)
    (ρ : Configuration d × Configuration d → Φ) (S : Φ → Finset (LBond d))
    (hρ : ∀ F, IsLocal (S F) (fun z => if ρ z = F then (1:ℝ) else 0))
    (μ : Γ → ℝ) (hμ0 : ∀ γ, 0 ≤ μ γ) (hμ1 : ∑ γ, μ γ = 1)
    (rank : E → ℕ) (Bl : Φ → E → Finset (LBond d))
    (hBl : ∀ F a b, a ≠ b → Disjoint (Bl F a) (Bl F b))
    (hS : ∀ F a, Disjoint (S F) (Bl F a))
    (lab : Γ → ℕ → E) (hlab : ∀ γ, StrictMono (fun t => rank (lab γ t))) (n : Γ → ℕ)
    (k : Γ → Φ → ℕ → X → X → Configuration d × Configuration d → ℝ)
    (hk : ∀ γ F t x y, IsLocal (Bl F (lab γ t)) (k γ F t x y))
    (hk0 : ∀ γ F t x y z, 0 ≤ k γ F t x y z)
    (hnorm : ∀ γ F t x,
      (∫ z, ∑ y, k γ F t x y z ∂((percolation d p).prod (percolation d q))) = 1)
    {ϱ : ℝ} (hϱ : 1 ≤ ϱ)
    (hBoth : ∀ γ γ' F t t' x x', (∫ z, ∑ yy : X × X, k γ F t x yy.1 z * k γ' F t' x' yy.2 z
      ∂((percolation d p).prod (percolation d q))) ≤ ϱ)
    (w : Γ → Φ → ℝ) (hw0 : ∀ γ F, 0 ≤ w γ F)
    (hwmean : ∀ γ, (∫ z, w γ (ρ z) ∂((percolation d p).prod (percolation d q))) = 1)
    (x₀ : Γ → Φ → X)
    (N : Γ × Γ → ℕ) (H : ℕ) (hN : ∀ y, N y ≤ H) {Λ C q₀ Mpow : ℝ}
    (hΛ : 0 ≤ Λ) (hC : 0 ≤ C) (hq₀ : 0 ≤ q₀) (hΛq : Λ * q₀ < 1) (hMpow : 0 < Mpow)
    (htail : ∀ j, (∑ y : Γ × Γ, if j + 1 ≤ N y then μ y.1 * μ y.2 else 0) ≤
      (C / Mpow) * q₀ ^ j)
    (hlarge : C * Λ / (1 - Λ * q₀) ≤ Mpow)
    (hcube : ∀ γ γ', ϱ ^ commonLabelCount (lab γ) (lab γ') (n γ) (n γ') *
      (∫ z, w γ (ρ z) * w γ' (ρ z) ∂((percolation d p).prod (percolation d q))) ≤
        Λ ^ N (γ, γ')) :
    (1/8 : ℝ) ≤ ∫ z, (if (1/2:ℝ) ≤ routeWeightSum μ ρ w k (fun γ _ => n γ) x₀ z
      then (1:ℝ) else 0) ∂((percolation d p).prod (percolation d q)) := by
  have hne : ∀ γ i j, i ≠ j → lab γ i ≠ lab γ j := by
    intro γ i j hij h
    exact hij ((hlab γ).injective (by simp only [h]))
  refine coupled_good_weight_probability p q ρ S hρ μ hμ0 hμ1
    (fun γ F t => Bl F (lab γ t))
    (fun γ F i j hij => hBl F _ _ (hne γ i j hij))
    (fun γ F j => hS F _) k hk hk0 hnorm
    (fun γ γ' _ => mergeSched rank (lab γ) (lab γ') (n γ) (n γ') 0 0) (fun γ _ => n γ)
    (fun γ γ' _ => mergeSched_leftCount rank (lab γ) (lab γ') _ (n γ) (n γ') 0 0 le_rfl)
    (fun γ γ' _ => mergeSched_rightCount rank (lab γ) (lab γ') _ (n γ) (n γ') 0 0 le_rfl)
    (fun γ γ' F => mergeSched_fresh rank (lab γ) (lab γ') (Bl F) (hBl F) (hlab γ) (hlab γ')
      _ (n γ) (n γ') 0 0 (S F) le_rfl (fun s _ _ => hS F _) (fun s _ _ => hS F _))
    (zero_le_one.trans hϱ) hBoth w hw0 hwmean x₀ N H hN hΛ hC hq₀ hΛq hMpow htail hlarge ?_
  intro γ γ'
  have hnn : 0 ≤ ∫ z, w γ (ρ z) * w γ' (ρ z) ∂((percolation d p).prod (percolation d q)) :=
    integral_nonneg (fun z => mul_nonneg (hw0 γ _) (hw0 γ' _))
  have hpow : ϱ ^ sharedCount (mergeSched rank (lab γ) (lab γ') (n γ) (n γ') 0 0) ≤
      ϱ ^ commonLabelCount (lab γ) (lab γ') (n γ) (n γ') :=
    pow_le_pow_right₀ hϱ (mergeSched_sharedCount_le rank (lab γ) (lab γ') (hlab γ) (hlab γ')
      _ (n γ) (n γ') 0 0 le_rfl)
  rw [integral_mul_const]
  calc (∫ z, w γ (ρ z) * w γ' (ρ z) ∂((percolation d p).prod (percolation d q))) *
        ϱ ^ sharedCount (mergeSched rank (lab γ) (lab γ') (n γ) (n γ') 0 0)
      ≤ (∫ z, w γ (ρ z) * w γ' (ρ z) ∂((percolation d p).prod (percolation d q))) *
        ϱ ^ commonLabelCount (lab γ) (lab γ') (n γ) (n γ') :=
        mul_le_mul_of_nonneg_left hpow hnn
    _ = ϱ ^ commonLabelCount (lab γ) (lab γ') (n γ) (n γ') *
        ∫ z, w γ (ρ z) * w γ' (ρ z) ∂((percolation d p).prod (percolation d q)) :=
        mul_comm _ _
    _ ≤ Λ ^ N (γ, γ') := hcube γ γ'

end NearCritical.Section10
