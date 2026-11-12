module

public import NearCritical.VariableSpeedWalkPath
public import Mathlib.Probability.Distributions.Exponential
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Probability.StrongLaw
public import Mathlib.Probability.UniformOn

@[expose] public section
noncomputable section

namespace NearCritical

open Filter MeasureTheory ProbabilityTheory Set
open scoped Topology Classical ENNReal

/-- Independent exponential waiting times for a rate-`r` proposal clock. -/
def variableSpeedWaitingLaw (r : ℝ) : Measure (ℕ → ℝ) :=
  Measure.infinitePi fun _ : ℕ => expMeasure r

/-- The exponential proposal clock is nonexplosive almost surely.
The proof uses the positive frequency of waits longer than one. -/
theorem variableSpeedWaitingLaw_ae_nonexplosive {r : ℝ} (hr : 0 < r) :
    ∀ᵐ s ∂variableSpeedWaitingLaw r, (∀ n, 0 < s n) ∧
      Tendsto (fun n => ∑ j ∈ Finset.range n, s j) atTop atTop := by
  let μ := expMeasure r
  let P := variableSpeedWaitingLaw r
  letI : IsProbabilityMeasure μ := isProbabilityMeasure_expMeasure hr
  letI : IsProbabilityMeasure P := by
    change IsProbabilityMeasure (Measure.infinitePi (fun _ : ℕ => μ))
    infer_instance
  have hmap (i : ℕ) : P.map (fun s => s i) = μ := Measure.infinitePi_map_eval _ i
  have hprob (i : ℕ) (A : Set ℝ) (hA : MeasurableSet A) :
      P ((fun s => s i) ⁻¹' A) = μ A := by
    rw [← Measure.map_apply (measurable_pi_apply i) hA, hmap]
  have hz : μ (Iic 0) = 0 := by
    apply (measureReal_eq_zero_iff (measure_ne_top μ _)).mp
    change (expMeasure r).real (Iic 0) = 0
    rw [← cdf_eq_real, cdf_expMeasure_eq hr]
    simp
  have hp : ∀ᵐ s ∂P, ∀ i, 0 < s i := by
    rw [ae_all_iff]
    intro i
    have h := measure_eq_zero_iff_ae_notMem.mp ((hprob i (Iic 0) measurableSet_Iic).trans hz)
    simpa only [mem_preimage,mem_Iic,not_le] using h
  let J : ℝ → ℝ := (Ioi 1).indicator (fun _ => 1)
  let X (i : ℕ) (s : ℕ → ℝ) := J (s i)
  have hJ : Measurable J := measurable_const.indicator measurableSet_Ioi
  have hX (i : ℕ) : Measurable (X i) := hJ.comp (measurable_pi_apply i)
  have hint : Integrable (X 0) P := by
    change Integrable (((fun s : ℕ → ℝ => s 0) ⁻¹' Ioi 1).indicator (fun _ => (1:ℝ))) P
    exact (integrable_const 1).indicator (measurableSet_Ioi.preimage (measurable_pi_apply 0))
  have hind := iIndepFun_infinitePi (P := fun _ : ℕ => μ) (X := fun _ => J) (fun _ => hJ)
  have hXmap (i : ℕ) : P.map (X i) = μ.map J := by
    change P.map (J ∘ (fun s => s i)) = _
    rw [← Measure.map_map hJ (measurable_pi_apply i), hmap]
  have hident (i : ℕ) : IdentDistrib (X i) (X 0) P P :=
    ⟨(hX i).aemeasurable,(hX 0).aemeasurable,(hXmap i).trans (hXmap 0).symm⟩
  let m := ∫ s, X 0 s ∂P
  have hmean : 0 < m := by
    have hm : m = μ.real (Ioi 1) := by
      change (∫ s, ((fun u : ℕ → ℝ => u 0) ⁻¹' Ioi 1).indicator (fun _ => (1:ℝ)) s ∂P) = _
      have hA : MeasurableSet ((fun u : ℕ → ℝ => u 0) ⁻¹' Ioi (1:ℝ)) :=
        measurableSet_Ioi.preimage (measurable_pi_apply 0)
      rw [integral_indicator_const (μ := P) (1:ℝ) hA,smul_eq_mul,mul_one]
      exact congrArg ENNReal.toReal (hprob 0 (Ioi 1) measurableSet_Ioi)
    rw [hm, ← compl_Iic, probReal_compl_eq_one_sub measurableSet_Iic]
    change 0 < 1 - (expMeasure r).real (Iic 1)
    rw [← cdf_eq_real, cdf_expMeasure_eq hr]
    simpa using Real.exp_pos (-r)
  have hLLN := strong_law_ae_real X hint (fun _ _ hij => hind.indepFun hij) hident
  change ∀ᵐ s ∂P, _
  filter_upwards [hp,hLLN] with s hs hlim
  refine ⟨hs, tendsto_atTop.2 ?_⟩
  intro a
  obtain ⟨N,hN⟩ := exists_nat_gt (a/(m/2))
  have hm : 0 < m/2 := half_pos hmean
  have hlow : ∀ᶠ n : ℕ in atTop, m/2 ≤ (∑ j ∈ Finset.range n, X j s)/(n:ℝ) :=
    hlim.eventually_const_le (half_lt_self hmean)
  filter_upwards [hlow,eventually_ge_atTop (max N 1)] with n hn hsize
  have hnpos : 0 < (n:ℝ) := by
    exact_mod_cast (Nat.zero_lt_one.trans_le ((le_max_right N 1).trans hsize))
  have ha : a ≤ (m/2)*(n:ℝ) := by
    have hNn : (N:ℝ) ≤ (n:ℝ) := by exact_mod_cast (le_max_left N 1).trans hsize
    calc
      a ≤ (n:ℝ)*(m/2) := ((div_lt_iff₀ hm).mp (hN.trans_le hNn)).le
      _ = _ := mul_comm _ _
  calc
    _ ≤ (m/2)*(n:ℝ) := ha
    _ ≤ ∑ j ∈ Finset.range n, X j s := (le_div_iff₀ hnpos).mp hn
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro j _
      by_cases h : s j ∈ Ioi (1:ℝ)
      · have h' : 1 < s j := h
        simpa only [X,J,indicator_of_mem h] using h'.le
      · simpa only [X,J,indicator_of_notMem h] using (hs j).le

/-- Independent exponential waits and independent uniform directed
proposals for the variable-speed walk. -/
def variableSpeedSampleLaw (d : ℕ) : Measure ((ℕ → ℝ) × (ℕ → Fin d × Bool)) :=
  (variableSpeedWaitingLaw (2*d:ℝ)).prod
    (Measure.infinitePi fun _ : ℕ => uniformOn (Set.univ : Set (Fin d × Bool)))

/-- The waiting sequences that give a nonexplosive positive clock. -/
def variableSpeedWaitingTimesValid (s : ℕ → ℝ) : Prop :=
  (∀ n, 0 < s n) ∧ Tendsto (fun n => ∑ j ∈ Finset.range n, s j) atTop atTop

private theorem measurable_waitingPartialSum (n : ℕ) :
    Measurable (fun s : ℕ → ℝ => ∑ j ∈ Finset.range n, s j) :=
  (Finset.range n).measurable_fun_sum (fun j _ => measurable_pi_apply j)

theorem measurableSet_variableSpeedWaitingTimesValid :
    MeasurableSet {s | variableSpeedWaitingTimesValid s} := by
  let A : Set (ℕ → ℝ) := ⋂ n : ℕ, {s | 0 < s n}
  let B : Set (ℕ → ℝ) := ⋂ k : ℕ, ⋃ N : ℕ, ⋂ n : ℕ,
    {s | N ≤ n → (k:ℝ) ≤ ∑ j ∈ Finset.range n, s j}
  have he : {s | variableSpeedWaitingTimesValid s} = A ∩ B := by
    ext s
    simp only [A,B,variableSpeedWaitingTimesValid,mem_inter_iff,mem_iInter,mem_iUnion,mem_setOf_eq]
    refine and_congr_right fun _ => ⟨?_,?_⟩
    · intro ht k
      exact eventually_atTop.1 ((tendsto_atTop.1 ht) (k:ℝ))
    · intro h
      apply tendsto_atTop.2
      intro r
      obtain ⟨k,hk⟩ := exists_nat_ge r
      exact (eventually_atTop.2 (h k)).mono fun _ hn => hk.trans hn
  rw [he]
  refine (MeasurableSet.iInter (fun n => measurableSet_lt measurable_const (measurable_pi_apply n))).inter ?_
  refine MeasurableSet.iInter fun k => MeasurableSet.iUnion fun N => MeasurableSet.iInter fun n => ?_
  by_cases h : N ≤ n
  · simpa only [h,true_implies] using measurableSet_le
      (show Measurable (fun _ : ℕ → ℝ => (k:ℝ)) from measurable_const)
      (measurable_waitingPartialSum n)
  · simpa only [h,false_implies,Set.setOf_true] using
      (MeasurableSet.univ : MeasurableSet (Set.univ : Set (ℕ → ℝ)))

theorem variableSpeedSampleLaw_ae_valid {d : ℕ} (hd : 0 < d) :
    ∀ᵐ s ∂variableSpeedSampleLaw d, variableSpeedWaitingTimesValid s.1 := by
  letI : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
  let D := Measure.infinitePi fun _ : ℕ => uniformOn (Set.univ : Set (Fin d × Bool))
  have h : MeasurePreserving Prod.fst
      ((variableSpeedWaitingLaw (2*d:ℝ)).prod D) (variableSpeedWaitingLaw (2*d:ℝ)) :=
    measurePreserving_fst
  have hr : 0 < (2*d:ℝ) := mul_pos (by norm_num) (by exact_mod_cast hd)
  exact h.quasiMeasurePreserving.ae (variableSpeedWaitingLaw_ae_nonexplosive hr)

/-- Totalized count on the exponential waiting-time sample space. -/
def variableSpeedWaitingCount (t : ℝ) (s : ℕ → ℝ) : ℕ :=
  if h : variableSpeedWaitingTimesValid s then
    (VariableSpeedJumpClock.ofWaitingTimes s h.1 h.2).count t
  else 0

theorem measurable_variableSpeedWaitingCount (t : ℝ) : Measurable (variableSpeedWaitingCount t) := by
  apply measurable_of_Iic
  intro n
  have he : variableSpeedWaitingCount t ⁻¹' Iic n =
      {s | variableSpeedWaitingTimesValid s}ᶜ ∪
      {s | t < ∑ j ∈ Finset.range (n+1), s j} := by
    ext s
    by_cases h : variableSpeedWaitingTimesValid s
    · have hcount := (VariableSpeedJumpClock.ofWaitingTimes s h.1 h.2).count_le_iff_lt_next
        (t := t) (n := n)
      simpa only [mem_preimage,mem_Iic,mem_union,mem_compl_iff,mem_setOf_eq,h,not_true,
        false_or,variableSpeedWaitingCount,dif_pos,VariableSpeedJumpClock.ofWaitingTimes] using hcount
    · simp [variableSpeedWaitingCount,h]
  rw [he]
  exact measurableSet_variableSpeedWaitingTimesValid.compl.union
    (measurableSet_lt measurable_const (measurable_waitingPartialSum (n+1)))

/-- The actual lattice-valued path, with a constant extension on the
exceptional event where the waiting times fail to define the clock. -/
def variableSpeedSamplePath {d : ℕ} (ω : Configuration d) (x : Vertex d)
    (s : (ℕ → ℝ) × (ℕ → Fin d × Bool)) : ℝ → Vertex d :=
  fun t => variableSpeedEndpoint ω (variableSpeedWaitingCount t s.1) x (fun k => s.2 k.val)

theorem variableSpeedSamplePath_isCadlag {d : ℕ} (ω : Configuration d) (x : Vertex d)
    (s : (ℕ → ℝ) × (ℕ → Fin d × Bool)) : IsCadlag (variableSpeedSamplePath ω x s) := by
  by_cases h : variableSpeedWaitingTimesValid s.1
  · let c := VariableSpeedJumpClock.ofWaitingTimes s.1 h.1 h.2
    have he : variableSpeedSamplePath ω x s = variableSpeedJumpPath ω x c s.2 := by
      funext t
      have hcount : variableSpeedWaitingCount t s.1 = c.count t := by
        unfold variableSpeedWaitingCount
        split
        · rfl
        · contradiction
      unfold variableSpeedSamplePath variableSpeedJumpPath
      rw [hcount]
    rw [he]
    exact variableSpeedJumpPath_isCadlag ω x c s.2
  · have he : variableSpeedSamplePath ω x s = fun _ => x := by
      funext t
      have hcount : variableSpeedWaitingCount t s.1 = 0 := by
        unfold variableSpeedWaitingCount
        split
        · contradiction
        · rfl
      unfold variableSpeedSamplePath
      rw [hcount]
      rfl
    rw [he]
    exact IsCadlag.const

/-- Each time evaluation of the uniformized path is measurable under
the product measurable structure of the clocks and directed proposals. -/
theorem measurable_variableSpeedSamplePath_eval {d : ℕ} (ω : Configuration d) (x : Vertex d)
    (t : ℝ) : Measurable (fun s => variableSpeedSamplePath ω x s t) := by
  let S := (ℕ → ℝ) × (ℕ → Fin d × Bool)
  let W (s : S) := variableSpeedWaitingCount t s.1
  let X (n : ℕ) (s : S) := variableSpeedEndpoint ω n x (fun k => s.2 k.val)
  have hW : Measurable W := (measurable_variableSpeedWaitingCount t).comp measurable_fst
  have hX (n : ℕ) : Measurable (X n) :=
    (measurable_of_finite (variableSpeedEndpoint ω n x)).comp
      (measurable_pi_iff.mpr fun k => (measurable_pi_apply k.val).comp measurable_snd)
  apply measurable_to_countable'
  intro y
  have he : (fun s : S => variableSpeedSamplePath ω x s t) ⁻¹' {y} =
      ⋃ n : ℕ, W ⁻¹' {n} ∩ X n ⁻¹' {y} := by
    ext s
    simp only [mem_preimage,mem_singleton_iff,mem_iUnion,mem_inter_iff]
    change X (W s) s = y ↔ ∃ n, W s = n ∧ X n s = y
    exact ⟨fun h => ⟨W s,rfl,h⟩, by rintro ⟨n,rfl,h⟩; exact h⟩
  rw [he]
  exact MeasurableSet.iUnion fun n => (hW (measurableSet_singleton n)).inter
    (hX n (measurableSet_singleton y))

end NearCritical
