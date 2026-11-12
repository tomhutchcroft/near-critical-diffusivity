import NearCritical.Section10TrajectoryLocal
import NearCritical.Section10BudgetFromLocalFlows

/-! A bound on the actual weighted overlap gives the finite translated
cube budget for the conductivity lower bound. -/

noncomputable section
namespace NearCritical.Section10

open MeasureTheory
open scoped Classical

/-- The actual issued paths supply the budget once the good-event
probability and expected weighted overlap are bounded. -/
theorem actualLayout_translatedBudget_of_charge {D M : ℕ}
    [LinearOrder (Finset (Vertex (D+1)))] (hD : 0 < D) (hM : 1 ≤ M)
    (typ : TypicalParameters) (t : ℕ) (ht : 9 ≤ t) (k : ℕ) (hk : 0 < k)
    (MOff Mcoal Kdiam : ℕ) (p q : unitInterval) (ρ κ : ℝ) (hκ : 0 < κ)
    (m : ℕ) (hm : m+2 = 2*M) (A a C : ℝ)
    (hmass : 0 ≤ sourceRouteSurvivalMass D M) (hρ : 0 < ρ) (hA : 0 ≤ A)
    (hAbound : 2 * (typ.diameterUpper * (2*(t:ℝ))^2) ≤ A)
    (hcount : (k:ℝ) ≤ typ.countLower * (2*(t:ℝ))^((D+1)-6)) :
    let Λ := actualLayout D typ t ht k hk MOff Mcoal Kdiam M
    let aC := boxCenter (D+1) t M
    let r := boxRadius t M
    let μ := (percolation (D+1) p).prod (percolation (D+1) q)
    ∀ (hs : ∀ (γ : SourceRoute D M) (G : Λ.Φ) (j : ℕ) (x : Λ.X), ρ⁻¹ ≤
        localSuccessProbability p q (Λ.Bl₀ G.1 (routeLab M γ.position j))
          (bitSet G.2 (fun z => Λ.succσ G (routeLab M γ.position j) x
            (Λ.view G.1 (routeLab M γ.position j) z))))
      (hsite : ∀ s, κ⁻¹ ≤ coupledProb p q (Λ.siteEvent s)),
    let R := (Λ.ruleFirstGood M p q ρ κ hκ hs hsite).toNestRule
    let W := routeWeightSum (routeLaw D M) R.ρ R.w R.kernel (fun _ _ => m+1+1) R.x₀
    let E := fun z => 4 * Λ.trajectoryChargeSum R (m+1+1) z A Kdiam
    (a ≤ ∫ z, (if (1/2:ℝ) ≤ W z then (1:ℝ) else 0) ∂μ) →
    (∫ z, E z ∂μ) ≤ C * cubeFlowNormalization (D+1) r *
      (chemicalCorrelationScale (D+1) (orParameter p q) : ℝ)^6 →
    translatedCoupledCubeFlowBudget p q aC Λ.i₀ r a C := by
  intro Λ aC r μ hs hsite R W E hprob henergy
  let U := translateSites aC (centeredBox (D+1) r)
  obtain ⟨O,hO,hW,hE⟩ := firstGood_trajectory_observables_local Λ (by omega : 2*M ≤ m+1+1)
    U p q ρ κ A Kdiam R (fun _ => rfl) (fun _ _ => rfl)
  have hE₀ (z : Configuration (D+1) × Configuration (D+1)) : 0 ≤ E z := by
    apply mul_nonneg (by norm_num : (0:ℝ) ≤ 4)
    unfold NestLayout.trajectoryChargeSum
    dsimp only
    apply Finset.sum_nonneg
    intro j _
    apply Finset.sum_nonneg
    intro l _
    have hw (j : SourceRoute D M × (Fin (m+1+1) → Λ.X)) :
        0 ≤ R.trajectoryWeight (m+1+1) z j := by
      apply mul_nonneg (routeLaw_nonneg hmass j.1)
      apply mul_nonneg (R.hw0 j.1 _)
      apply trajWeight_nonneg
      intro s u v ω
      exact stepKernel_nonneg _ _ _ ((inv_nonneg.mpr hρ.le).trans (R.hs j.1 (R.ρ z) s u)) v ω
    refine mul_nonneg (mul_nonneg (hw j) (hw l)) ?_
    exact add_nonneg (mul_nonneg (by linarith) (Nat.cast_nonneg _))
      (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  refine translatedCoupledCubeFlowBudget_of_local_flows p q aC Λ.i₀ a C O W E hW
    ((isLocal_const O 4).mul hE) hE₀ hO hprob henergy ?_
  intro z hz
  obtain ⟨θ,hflow,hsupp,hen⟩ := actualLayout_issuedFlow_of_half_mass hD hM typ t ht k hk
    MOff Mcoal Kdiam p q ρ κ hκ z m hm A hmass hρ hA hAbound hcount hs hsite hz
  exact ⟨θ,hsupp,hflow,hen⟩

end NearCritical.Section10
