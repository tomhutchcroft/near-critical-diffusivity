import NearCritical.Section10ChargeExpectation
import NearCritical.Section10ActualSiteMassBound
import NearCritical.Section10TubeMarkCount
import NearCritical.Section10ActualRoute

noncomputable section

namespace NearCritical.Section10

open MeasureTheory
open scoped Classical

/-- The expected trajectory charge of the actual layout, with the
common-level exponential tail already summed. The microscopic lengths
`A` and `B` are explicit so the same estimate serves every admissible
choice of the two path length bounds. -/
theorem actualLayout_charge_expectation_le {D : ℕ} [LinearOrder (Finset (Vertex (D+1)))]
    (hd : 7 ≤ D+1) (asymp : TwoPointAsymptotics (D+1)) (q₀ : ℝ)
    (hp₀ : 0 < (criticalPoint (D+1) : ℝ)) (hp₁ : (criticalPoint (D+1) : ℝ) < 1)
    {qTail Ctail : ℝ} (hqTail : 0 ≤ qTail) (hCtail : 0 ≤ Ctail) (M₀ : ℕ)
    (hTail : ∀ M ≥ M₀,
      (∀ γ : SourceRoute D M, 0 ≤ routeLaw D M γ) ∧
      ∀ j : ℕ, (∑ y : SourceRoute D M × SourceRoute D M,
        if j+1 ≤ routeCommonLevels D M y then routeLaw D M y.1 * routeLaw D M y.2 else 0) ≤
          (Ctail / (M:ℝ)^(D-1))*qTail^j)
    (typ : TypicalParameters) (hr : 1 ≤ typ.regularRadius) (hb : 0 ≤ typ.boundaryUpper)
    (hl : 0 < typ.countLower) (hu : 0 ≤ typ.countUpper) (k : ℕ) (hk : 0 < k) :
    ∃ (Cs Ct : ℝ) (T : ℕ), 0 ≤ Cs ∧ 0 ≤ Ct ∧
     ∀ (t : ℕ) (ht : 9 ≤ t), T ≤ t →
    ∀ (MOff Mcoal Kdiam M : ℕ), 1 ≤ M → M₀ ≤ M →
    let Λ := actualLayout D typ t ht k hk MOff Mcoal Kdiam M
    let p := criticalPoint (D+1)
    ∀ (q : unitInterval), (q : ℝ) ≤ q₀ * (t:ℝ)^(-2:ℝ) →
    ∀ (ρ κ : ℝ) (hκ : 0 < κ), 1 ≤ ρ → ρ ≤ 9/8 → 1 ≤ κ →
    ∀ (hs : ∀ (γ : SourceRoute D M) (G : Λ.Φ) (j : ℕ) (x : Λ.X), ρ⁻¹ ≤
      localSuccessProbability p q (Λ.Bl₀ G.1 (routeLab M γ.position j))
        (bitSet G.2 (fun z => Λ.succσ G (routeLab M γ.position j) x
          (Λ.view G.1 (routeLab M γ.position j) z))))
      (hsite : ∀ s, κ⁻¹ ≤ coupledProb p q (Λ.siteEvent s)),
    (k:ℝ) ≤ typ.countLower * (2*(t:ℝ))^(D+1-6) →
    ∀ (A B amp : ℝ), 0 ≤ A → 0 ≤ B → ρ^2*κ^2 ≤ amp → amp*qTail < 1 →
    let R := (Λ.ruleFirstGood M p q ρ κ hκ hs hsite).toNestRule
    (∫ z, Λ.trajectoryChargeSum R (2*M) z A B ∂((percolation (D+1) p).prod (percolation (D+1) q))) ≤
      (2*((2*A+1)*Cs+B*Ct) * (t:ℝ)^(6-((D+1:ℕ):ℝ))) *
        ((Ctail / (M:ℝ)^(D-1)) * amp * (2/(1-amp*qTail)^2)) := by
  obtain ⟨Cs,hCs,Ts,hS⟩ := actualLayout_terminal_site_mass_le hd asymp q₀ hp₀ hp₁ typ hr hb hl hu k hk
  obtain ⟨Ct,hCt,Tt,hT⟩ := actualLayout_shared_tube_mass_le hd asymp q₀ hp₀ hp₁ typ hr hb hl hu k hk
  refine ⟨Cs,Ct,max Ts Tt,hCs,hCt,?_⟩
  intro t ht htT MOff Mcoal Kdiam M hM hlarge Λ p q hq ρ κ hκ hρ hρ' hκ' hs hsite hcount
    A B amp hA hB hamp hampq R
  obtain ⟨hLaw,htail⟩ := hTail M hlarge
  let μ := (percolation (D+1) p).prod (percolation (D+1) q)
  let Y := SourceRoute D M × SourceRoute D M
  let ν (y : Y) := routeLaw D M y.1 * routeLaw D M y.2
  let N := routeCommonLevels D M
  let u := (t:ℝ)^(6-((D+1:ℕ):ℝ))
  let Eₛ := Cs*u
  let Eₜ := Ct*u
  let B₀ := 2*((2*A+1)*Eₛ+B*Eₜ)
  have hu₀ : 0 ≤ u := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hEs : 0 ≤ Eₛ := mul_nonneg hCs hu₀
  have hEt : 0 ≤ Eₜ := mul_nonneg hCt hu₀
  have hρ₀ := zero_lt_one.trans_le hρ
  have hν (y : Y) : 0 ≤ ν y := mul_nonneg (hLaw y.1) (hLaw y.2)
  have hB₀ : 0 ≤ B₀ := mul_nonneg (by norm_num)
    (add_nonneg (mul_nonneg (by linarith) hEs) (mul_nonneg hB hEt))
  refine (Λ.trajectoryCharge_integral_le_of_terminal_counts R hM hρ hκ'
    (fun _ => rfl) (fun _ _ => rfl) hLaw A B Eₛ Eₜ hA hB hEs hEt ?_).trans ?_
  · intro y hy G hreal hw hw'
    obtain ⟨z,rfl⟩ := hreal
    let G := refineReveal Λ.ρ₀ Λ.S₀ z
    let x := R.x₀ y.1 G
    let x' := R.x₀ y.2 G
    have hsurv (γ : SourceRoute D M) (h : routeLaw D M γ ≠ 0) :
        lazyRouteSurvives γ.1.1 γ.2 := by
      by_contra hn
      exact h (if_neg hn)
    have h₁ := hsurv y.1 (left_ne_zero_of_mul hy.ne')
    have h₂ := hsurv y.2 (right_ne_zero_of_mul hy.ne')
    have hbox (δ : SourceRoute D M) (hδ : δ ∈ ({y.1,y.2} : Finset (SourceRoute D M)))
        (j : ℕ) (hj : j < 2*M) : (routeLab M δ.position j).site ∈ Λ.siteBox := by
      rcases Finset.mem_insert.mp hδ with h | h
      · subst δ
        exact routeLab_site_mem_box y.1 h₁ hj
      · have he := Finset.mem_singleton.mp h
        subst δ
        exact routeLab_site_mem_box y.2 h₂ hj
    have hpre (δ : SourceRoute D M) (hδ : δ ∈ ({y.1,y.2} : Finset (SourceRoute D M)))
        (j : ℕ) (hj : j < 2*M) : IsPreGoodCube Λ.typ Λ.t (Λ.center (routeLab M δ.position j).site) z.1 := by
      have hb := hbox δ hδ j hj
      have hm := (routeLab_site δ.position hj).1
      rcases Finset.mem_insert.mp hδ with h | h
      · subst δ
        exact (Λ.ruleFirstGood M p q ρ κ hκ hs hsite).weight_pos y.1 z hw _ hm hb
      · have he := Finset.mem_singleton.mp h
        subst δ
        exact (Λ.ruleFirstGood M p q ρ κ hκ hs hsite).weight_pos y.2 z hw' _ hm hb
    have hsiteMark := hS t ht ((le_max_left _ _).trans htT) MOff Mcoal Kdiam M hM q hq
      ρ κ hκ hρ hρ' hs hsite y.1 y.2 z x x' hbox hpre hcount
    have htubeMark := hT t ht ((le_max_right _ _).trans htT) MOff Mcoal Kdiam M hM q hq
      ρ κ hκ hρ hρ' hs hsite y.1 y.2 z x x' hbox hpre hcount
    refine ⟨?_,?_⟩
    · exact Λ.firstGood_terminal_site_count_mass_le p q ρ κ hκ hs hsite y.1 y.2 G (x,x') hEs hsiteMark
    · exact Λ.firstGood_terminal_tube_count_mass_le p q ρ κ hκ hρ₀ hM hs hsite y.1 y.2 G
        (x,x') hEt htubeMark
  · have hbase : 0 ≤ ρ^2*κ^2 := mul_nonneg (sq_nonneg _) (sq_nonneg _)
    have hMpow : 0 < (M:ℝ)^(D-1) := pow_pos (by exact_mod_cast (show 0 < M by omega)) _
    have hmoment := energy_count_moment_le ν N hν M (fun y => routeCommonLevels_le D M y)
      (hbase.trans hamp) hCtail hqTail hampq hMpow htail
    have hsum :
        (∑ y : Y, ν y * ((N y:ℝ) * (ρ^2*κ^2)^(N y))) ≤
        ∑ y : Y, ν y * (if 1 ≤ N y then (1 + (N y:ℝ))*amp^(N y) else 0) := by
      refine Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left ?_ (hν y)
      by_cases hy : 1 ≤ N y
      · rw [if_pos hy]
        refine mul_le_mul ?_ (pow_le_pow_left₀ hbase hamp _) (pow_nonneg hbase _) (by positivity)
        linarith
      · have hz : N y = 0 := by omega
        norm_num [hz]
    calc
      _ ≤ B₀ * ((Ctail / (M:ℝ)^(D-1)) * amp * (2/(1-amp*qTail)^2)) :=
        mul_le_mul_of_nonneg_left (hsum.trans hmoment) hB₀
      _ = _ := by dsimp only [B₀,Eₛ,Eₜ,u]; ring

end NearCritical.Section10
