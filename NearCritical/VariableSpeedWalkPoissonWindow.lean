module

public import NearCritical.VariableSpeedWalkMarginalLaw
public import Mathlib.MeasureTheory.Constructions.Pi

@[expose] public section
noncomputable section

namespace NearCritical

open Filter MeasureTheory ProbabilityTheory Set
open scoped Classical ENNReal NNReal

/-- The first `n` waits finish by `t`, and the next wait finishes after
`t`. The event reads only the first `n+1` waiting times. -/
def waitingCountWindow (n : ℕ) (t : ℝ) : Set (Fin (n+1) → ℝ) :=
  {s | (∀ j, 0 < s j) ∧ (∑ j : Fin n, s j.castSucc) ≤ t ∧
    t < ∑ j : Fin (n+1), s j}

theorem measurableSet_waitingCountWindow (n : ℕ) (t : ℝ) :
    MeasurableSet (waitingCountWindow n t) := by
  have hp : {s : Fin (n+1) → ℝ | ∀ j, 0 < s j} = ⋂ j : Fin (n+1), {s | 0 < s j} := by
    ext s
    simp
  have hm₁ : Measurable (fun s : Fin (n+1) → ℝ => ∑ j : Fin n, s j.castSucc) :=
    Finset.univ.measurable_fun_sum (fun j _ => measurable_pi_apply j.castSucc)
  have hm₂ : Measurable (fun s : Fin (n+1) → ℝ => ∑ j : Fin (n+1), s j) :=
    Finset.univ.measurable_fun_sum (fun j _ => measurable_pi_apply j)
  have hp' : MeasurableSet {s : Fin (n+1) → ℝ | ∀ j, 0 < s j} := by
    rw [hp]
    exact MeasurableSet.iInter fun j => measurableSet_lt measurable_const (measurable_pi_apply j)
  exact hp'.inter ((measurableSet_le hm₁ measurable_const).inter (measurableSet_lt measurable_const hm₂))

theorem waitingCountWindow_neg {n : ℕ} {t : ℝ} (ht : t < 0) :
    waitingCountWindow n t = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro s hs
  have h : 0 ≤ ∑ j : Fin n, s j.castSucc := Finset.sum_nonneg fun j _ => (hs.1 j.castSucc).le
  exact (not_le_of_gt ht) (h.trans hs.2.1)

theorem waitingCountWindow_succ_iff {n : ℕ} {t : ℝ} {s : Fin (n+2) → ℝ} :
    s ∈ waitingCountWindow (n+1) t ↔
      0 < s 0 ∧ (fun j : Fin (n+1) => s j.succ) ∈ waitingCountWindow n (t - s 0) := by
  have h₁ : (∑ j : Fin (n+1), s j.castSucc) = s 0 + ∑ j : Fin n, s j.castSucc.succ := by
    rw [Fin.sum_univ_succ]
    simp only [Fin.castSucc_zero, Fin.castSucc_succ]
  have h₂ := Fin.sum_univ_succ s
  change ((∀ j, 0 < s j) ∧ (∑ j : Fin (n+1), s j.castSucc) ≤ t ∧
    t < ∑ j : Fin (n+2), s j) ↔ _
  rw [h₁,h₂,Fin.forall_fin_succ]
  constructor
  · rintro ⟨⟨h0,hpos⟩,hlo,hhi⟩
    exact ⟨h0,hpos,by linarith,by linarith⟩
  · rintro ⟨h0,hpos,hlo,hhi⟩
    exact ⟨⟨h0,hpos⟩,by linarith,by linarith⟩

/-- The finite product law on the first `n` exponential waiting times. -/
def waitingPrefixLaw (r : ℝ) (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi fun _ : Fin n => expMeasure r

/-- Integrating over the first waiting time gives the renewal recursion
for the finite-window probabilities. -/
theorem waitingCountWindow_succ_measure {r : ℝ} (hr : 0 < r) (n : ℕ) (t : ℝ) :
    waitingPrefixLaw r (n+2) (waitingCountWindow (n+1) t) =
      ∫⁻ s in Ioc 0 t, waitingPrefixLaw r (n+1) (waitingCountWindow n (t-s)) ∂expMeasure r := by
  let μ := expMeasure r
  let ν := waitingPrefixLaw r (n+1)
  letI : IsProbabilityMeasure μ := isProbabilityMeasure_expMeasure hr
  letI : IsProbabilityMeasure ν := by unfold ν waitingPrefixLaw; infer_instance
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+2) => ℝ) 0
  let A := waitingCountWindow (n+1) t
  let E : Set (ℝ × (Fin (n+1) → ℝ)) := e.symm ⁻¹' A
  have hm : MeasurableSet E := (measurableSet_waitingCountWindow (n+1) t).preimage e.symm.measurable
  have hmap : (waitingPrefixLaw r (n+2)).map e = μ.prod ν :=
    (measurePreserving_piFinSuccAbove (fun _ : Fin (n+2) => μ) 0).map_eq
  have he (u : Fin (n+2) → ℝ) : e u = (u 0, fun j => u j.succ) := by
    change (u 0, fun j => u ((0 : Fin (n+2)).succAbove j)) = _
    simp only [Fin.succAbove_zero]
  have hE (s : ℝ) (u : Fin (n+1) → ℝ) :
      (s,u) ∈ E ↔ 0 < s ∧ u ∈ waitingCountWindow n (t-s) := by
    have hpair := e.apply_symm_apply (s,u)
    rw [he, Prod.mk.injEq] at hpair
    change e.symm (s,u) ∈ waitingCountWindow (n+1) t ↔ _
    rw [waitingCountWindow_succ_iff,hpair.1,hpair.2]
  have hmass : waitingPrefixLaw r (n+2) A = (μ.prod ν) E := by
    rw [← hmap,Measure.map_apply e.measurable hm]
    have hpre : e ⁻¹' E = A := by
      ext s
      simp [E]
    rw [hpre]
  change waitingPrefixLaw r (n+2) A = _
  rw [hmass,Measure.prod_apply hm,← lintegral_indicator measurableSet_Ioc]
  apply lintegral_congr
  intro s
  by_cases hs : s ∈ Ioc (0:ℝ) t
  · rw [indicator_of_mem hs]
    congr 1
    ext u
    exact (hE s u).trans (and_iff_right hs.1)
  · rw [indicator_of_notMem hs]
    have hempty : Prod.mk s ⁻¹' E = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro u hu
      obtain ⟨hpos,hwin⟩ := (hE s u).mp hu
      have hst : t < s := lt_of_not_ge (fun hle => hs ⟨hpos,hle⟩)
      rw [waitingCountWindow_neg (sub_neg.mpr hst)] at hwin
      exact hwin
    rw [hempty,measure_empty]

theorem waitingCountWindow_zero_measure {r t : ℝ} (hr : 0 < r) (ht : 0 ≤ t) :
    waitingPrefixLaw r 1 (waitingCountWindow 0 t) = ENNReal.ofReal (Real.exp (-(r*t))) := by
  let μ := expMeasure r
  letI : IsProbabilityMeasure μ := isProbabilityMeasure_expMeasure hr
  have he : waitingCountWindow 0 t = (fun s : Fin 1 → ℝ => s 0) ⁻¹' Ioi t := by
    ext s
    change ((∀ j, 0 < s j) ∧ (∑ j : Fin 0, s j.castSucc) ≤ t ∧
      t < ∑ j : Fin 1, s j) ↔ t < s 0
    simp only [Fintype.sum_empty,Fin.sum_univ_one,ht,true_and]
    exact ⟨fun h => h.2,fun h => ⟨fun j => by
      have hj : j = 0 := Fin.eq_zero j
      rw [hj]
      exact ht.trans_lt h,h⟩⟩
  have hmap : (waitingPrefixLaw r 1).map (fun s => s 0) = μ :=
    (measurePreserving_eval (fun _ : Fin 1 => μ) 0).map_eq
  rw [he,← Measure.map_apply (measurable_pi_apply 0) measurableSet_Ioi,hmap]
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top μ _) ENNReal.ofReal_ne_top).mp
  rw [ENNReal.toReal_ofReal (Real.exp_nonneg _)]
  change (expMeasure r).real (Ioi t) = _
  rw [← compl_Iic,probReal_compl_eq_one_sub measurableSet_Iic,← cdf_eq_real,cdf_expMeasure_eq hr]
  simp [ht]

/-- The finite exponential prefix is the restriction of the actual
infinite product waiting-time law. -/
theorem waitingPrefixLaw_eq_map {r : ℝ} (hr : 0 < r) (n : ℕ) :
    (variableSpeedWaitingLaw r).map (fun s (j : Fin n) => s j.val) = waitingPrefixLaw r n := by
  let μ := expMeasure r
  letI : IsProbabilityMeasure μ := isProbabilityMeasure_expMeasure hr
  let I := Finset.range n
  let e : I ≃ Fin n :=
    { toFun := fun j => ⟨j.val,Finset.mem_range.mp j.property⟩
      invFun := fun j => ⟨j.val,Finset.mem_range.mpr j.isLt⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let T := MeasurableEquiv.piCongrLeft (fun _ : Fin n => ℝ) e
  have he : (fun (s : ℕ → ℝ) (j : Fin n) => s j.val) =
      T ∘ (I.restrict : (ℕ → ℝ) → (I → ℝ)) := by
    funext s j
    rfl
  have hm : Measurable (I.restrict : (ℕ → ℝ) → (I → ℝ)) := measurable_pi_iff.mpr fun j => measurable_pi_apply j.val
  rw [he,← Measure.map_map T.measurable hm,variableSpeedWaitingLaw,Measure.infinitePi_map_restrict]
  exact Measure.pi_map_piCongrLeft e (fun _ : Fin n => μ)

/-- The point mass of the actual waiting count equals the finite
renewal-window probability. -/
theorem waitingCount_singleton_eq_window {r t : ℝ} (hr : 0 < r) (ht : 0 ≤ t) (n : ℕ) :
    ((variableSpeedWaitingLaw r).map (variableSpeedWaitingCount t)) {n} =
      waitingPrefixLaw r (n+1) (waitingCountWindow n t) := by
  let P := variableSpeedWaitingLaw r
  let f (s : ℕ → ℝ) (j : Fin (n+1)) := s j.val
  have hm : Measurable f := measurable_pi_iff.mpr fun j => measurable_pi_apply j.val
  rw [Measure.map_apply (measurable_variableSpeedWaitingCount t) (measurableSet_singleton n),
    ← waitingPrefixLaw_eq_map hr (n+1),Measure.map_apply hm (measurableSet_waitingCountWindow n t)]
  apply measure_congr
  filter_upwards [variableSpeedWaitingLaw_ae_nonexplosive hr] with s hs
  have hs' : variableSpeedWaitingTimesValid s := hs
  let c := VariableSpeedJumpClock.ofWaitingTimes s hs.1 hs.2
  have he : variableSpeedWaitingCount t s = c.count t := by
    unfold variableSpeedWaitingCount
    split
    · rfl
    · contradiction
  have hc : c.count t = n ↔ c.arrival n ≤ t ∧ t < c.arrival (n+1) := by
    constructor
    · intro h
      have hnext := c.count_lt_next t
      rw [h] at hnext
      refine ⟨?_,hnext⟩
      by_cases hn : n = 0
      · rw [hn,c.start]
        exact ht
      · by_contra! hprev
        have hn' : n-1+1 = n := by omega
        have hle := c.count_le_iff_lt_next.mpr (show t < c.arrival (n-1+1) by simpa only [hn'] using hprev)
        omega
    · intro h
      exact c.count_eq_of_window (Or.inr h.1) h.2
  apply propext
  change variableSpeedWaitingCount t s = n ↔ f s ∈ waitingCountWindow n t
  rw [he,hc]
  change (∑ j ∈ Finset.range n, s j) ≤ t ∧ t < ∑ j ∈ Finset.range (n+1), s j ↔
    ((∀ j : Fin (n+1), 0 < s j.val) ∧ (∑ j : Fin n, s j.val) ≤ t ∧ t < ∑ j : Fin (n+1), s j.val)
  rw [Fin.sum_univ_eq_sum_range,Fin.sum_univ_eq_sum_range]
  exact ⟨fun h => ⟨fun j => hs.1 j.val,h⟩, fun h => h.2⟩

end NearCritical
