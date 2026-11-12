module

public import NearCritical.Section10LabelledWeight

/-! `P[W >= 1/2] >= 1/8` for chains driven by the SOURCE step kernel
`iota_t * (uniform choice among offspring)`.

The kernel hypotheses of `labelled_good_weight_probability` (locality,
nonnegativity, mean one, shared-step bound) are proved for `stepKernel`. What is
left about a step is exactly the source's uniform lower bound on the conditional
success probability, `1/rho <= s_t` (in the source `s_t >= 1 - eps0/4`, from
`prop.proba.k-nest`), and that offspring sets are nonempty on success.
-/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open MeasureTheory
open scoped Classical BigOperators

lemma stepKernel_nonneg {d : ℕ} {X : Type*} (T : Finset (LBond d))
    (a : Set ((T → Bool))) (o : (T → Bool) → Finset X)
    {s : ℝ} (hs : 0 ≤ s) (y : X) (z : Configuration d × Configuration d) :
    0 ≤ stepKernel T a o s y z := by
  unfold stepKernel
  split_ifs
  · exact inv_nonneg.mpr (mul_nonneg hs (Nat.cast_nonneg _))
  · exact le_refl _

/-- The source kernel of route `γ` at step `t` in state `x`, on the reveal atom `F`. -/
def sourceKernel {d : ℕ} {X Φ Γ E : Type*} (p q : unitInterval)
    (Bl : Φ → E → Finset (LBond d)) (lab : Γ → ℕ → E)
    (a : ∀ (γ : Γ) (F : Φ) (t : ℕ), X →
      Set ((Bl F (lab γ t) → Bool)))
    (o : ∀ (γ : Γ) (F : Φ) (t : ℕ), X →
      (Bl F (lab γ t) → Bool) → Finset X)
    (γ : Γ) (F : Φ) (t : ℕ) (x y : X) : Configuration d × Configuration d → ℝ :=
  stepKernel (Bl F (lab γ t)) (a γ F t x) (o γ F t x)
    (localSuccessProbability p q (Bl F (lab γ t)) (a γ F t x)) y

theorem sourceRule_good_weight_probability {d : ℕ} {X Φ Γ E : Type*}
    [Fintype X] [Fintype Φ] [Fintype Γ] (p q : unitInterval)
    (ρ : Configuration d × Configuration d → Φ) (S : Φ → Finset (LBond d))
    (hρ : ∀ F, IsLocal (S F) (fun z => if ρ z = F then (1:ℝ) else 0))
    (μ : Γ → ℝ) (hμ0 : ∀ γ, 0 ≤ μ γ) (hμ1 : ∑ γ, μ γ = 1)
    (rank : E → ℕ) (Bl : Φ → E → Finset (LBond d))
    (hBl : ∀ F a b, a ≠ b → Disjoint (Bl F a) (Bl F b))
    (hS : ∀ F a, Disjoint (S F) (Bl F a))
    (lab : Γ → ℕ → E) (hlab : ∀ γ, StrictMono (fun t => rank (lab γ t))) (n : Γ → ℕ)
    (a : ∀ (γ : Γ) (F : Φ) (t : ℕ), X →
      Set ((Bl F (lab γ t) → Bool)))
    (o : ∀ (γ : Γ) (F : Φ) (t : ℕ), X →
      (Bl F (lab γ t) → Bool) → Finset X)
    (ho : ∀ γ F t x, ∀ b ∈ a γ F t x, (o γ F t x b).Nonempty)
    {ϱ : ℝ} (hϱ : 1 ≤ ϱ)
    (hs : ∀ γ F t x, ϱ⁻¹ ≤ localSuccessProbability p q (Bl F (lab γ t)) (a γ F t x))
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
    (1/8 : ℝ) ≤ ∫ z, (if (1/2:ℝ) ≤
        routeWeightSum μ ρ w (sourceKernel p q Bl lab a o) (fun γ _ => n γ) x₀ z
      then (1:ℝ) else 0) ∂((percolation d p).prod (percolation d q)) := by
  have hϱ0 : 0 < ϱ := lt_of_lt_of_le one_pos hϱ
  have hspos : ∀ γ F t x, 0 < localSuccessProbability p q (Bl F (lab γ t)) (a γ F t x) :=
    fun γ F t x => lt_of_lt_of_le (inv_pos.mpr hϱ0) (hs γ F t x)
  refine labelled_good_weight_probability p q ρ S hρ μ hμ0 hμ1 rank Bl hBl hS lab hlab n
    (sourceKernel p q Bl lab a o)
    (fun γ F t x y => stepKernel_isLocal _ _ _ _ y)
    (fun γ F t x y z => stepKernel_nonneg _ _ _ (hspos γ F t x).le y z)
    (fun γ F t x => stepKernel_integral_eq_one p q _ _ _ (ho γ F t x) (hspos γ F t x))
    hϱ ?_ w hw0 hwmean x₀ N H hN hΛ hC hq₀ hΛq hMpow htail hlarge hcube
  intro γ γ' F t t' x x'
  refine (stepKernel_pair_integral_le p q _ _ _ _ _ _ (ho γ F t x) (ho γ' F t' x')
    (hspos γ F t x) (hspos γ' F t' x')).trans ?_
  exact (inv_le_comm₀ (hspos γ' F t' x') hϱ0).mpr (hs γ' F t' x')

end NearCritical.Section10
