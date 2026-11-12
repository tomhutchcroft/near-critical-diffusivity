module

public import NearCritical.BK
public import NearCritical.InhomogeneousExpectation

/-! Stage 1: genuine BK for finite independent profiles whose every coordinate
rate is at most one half. The original deterministic section proof is reused.
No OR amplification, all-parameter profile BK, or countable lift is claimed. -/
@[expose] public section
noncomputable section
namespace NearCritical.BK
open Set MeasureTheory ProbabilityTheory
open scoped Classical

/-- Literal event expectation for a coordinate-dependent real profile. -/
def profileEventProbability {E : Type*} [Fintype E] (r : E → ℝ)
    (A : Set (E → Bool)) : ℝ :=
  finiteExpectationProfile r (fun η ↦ if η ∈ A then 1 else 0)

lemma profileEventProbability_mono {E : Type*} [Fintype E] {r : E → ℝ}
    (hr0 : ∀ e, 0 ≤ r e) (hr1 : ∀ e, r e ≤ 1)
    {A B : Set (E → Bool)} (hAB : A ⊆ B) :
    profileEventProbability r A ≤ profileEventProbability r B := by
  apply Finset.sum_le_sum
  intro η _
  apply mul_le_mul_of_nonneg_right
  · by_cases hη : η ∈ A
    · simp [hη, hAB hη]
    · simp only [ite_eq_right hη]
      split <;> norm_num
  · apply Finset.prod_nonneg
    intro e _
    split <;> linarith [hr0 e, hr1 e]

lemma profile_weight_extend {E : Type*} [Fintype E] (r : Option E → ℝ)
    (b : Bool) (η : E → Bool) :
    (∏ e : Option E, if extend b η e then r e else 1-r e) =
      (if b then r none else 1-r none) *
        ∏ e : E, if η e then r (some e) else 1-r (some e) := by
  rw [univ_option, Finset.prod_insertNone]
  rfl

lemma finiteExpectationProfile_option {E : Type*} [Fintype E]
    (r : Option E → ℝ) (f : (Option E → Bool) → ℝ) :
    finiteExpectationProfile r f =
      (1-r none)*finiteExpectationProfile (fun e ↦ r (some e)) (fun η ↦ f (extend false η)) +
      r none*finiteExpectationProfile (fun e ↦ r (some e)) (fun η ↦ f (extend true η)) := by
  calc
    _ = ∑ b : Bool, ∑ η : E → Bool,
        f (extend b η) * ∏ e : Option E, if extend b η e then r e else 1-r e := by
      unfold finiteExpectationProfile
      convert! sum_configs_option (E := E)
        (fun ω ↦ f ω * ∏ e : Option E, if ω e then r e else 1-r e) using 1
      apply Finset.sum_congr (by ext η; simp)
      intro η _
      apply congrArg (fun z : ℝ ↦ f η*z)
      apply Finset.prod_congr (by ext e; simp)
      intro e _
      rfl
    _ = ∑ b : Bool, (if b then r none else 1-r none) *
        finiteExpectationProfile (fun e ↦ r (some e)) (fun η : E → Bool ↦ f (extend b η)) := by
      apply Finset.sum_congr rfl
      intro b _
      unfold finiteExpectationProfile
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro η _
      rw [profile_weight_extend]
      ring
    _ = _ := by
      simp [Fintype.univ_bool]
      ring

lemma profileEventProbability_option {E : Type*} [Fintype E]
    (r : Option E → ℝ) (A : Set (Option E → Bool)) :
    profileEventProbability r A =
      (1-r none)*profileEventProbability (fun e ↦ r (some e)) (sectionEvent A false) +
      r none*profileEventProbability (fun e ↦ r (some e)) (sectionEvent A true) :=
  finiteExpectationProfile_option r (fun η ↦ if η ∈ A then 1 else 0)

lemma profile_occurrence_section_probability_bound {E : Type*} [Fintype E]
    {r : E → ℝ} (hr0 : ∀ e, 0 ≤ r e) (hr1 : ∀ e, r e ≤ 1)
    {A B : Set (Option E → Bool)} (hA : Increasing A) (hB : Increasing B) :
    profileEventProbability r (sectionEvent (occurrenceEvent A B) true) ≤
      profileEventProbability r (occurrenceEvent (sectionEvent A true) (sectionEvent B false)) +
      profileEventProbability r (occurrenceEvent (sectionEvent A false) (sectionEvent B true)) -
      profileEventProbability r (occurrenceEvent (sectionEvent A false) (sectionEvent B false)) := by
  calc
    _ ≤ ∑ η : E → Bool,
        ((if DisjointOccurrence (sectionEvent A true) (sectionEvent B false) η then (1 : ℝ) else 0) +
        (if DisjointOccurrence (sectionEvent A false) (sectionEvent B true) η then 1 else 0) -
        (if DisjointOccurrence (sectionEvent A false) (sectionEvent B false) η then 1 else 0)) *
        ∏ e, if η e then r e else 1-r e := by
      apply Finset.sum_le_sum
      intro η _
      apply mul_le_mul_of_nonneg_right (occurrence_section_indicator_bound hA hB η)
      apply Finset.prod_nonneg
      intro e _
      split <;> linarith [hr0 e, hr1 e]
    _ = _ := by
      simp only [profileEventProbability, finiteExpectationProfile, occurrenceEvent, mem_ofPred_eq,
        add_mul, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib]
      convert! rfl

lemma profile_eventProbability_occurrence_option {E : Type*} [Fintype E]
    {r : Option E → ℝ} (hr0 : ∀ e, 0 ≤ r e) (hr1 : ∀ e, r e ≤ 1)
    {A B : Set (Option E → Bool)} (hA : Increasing A) (hB : Increasing B) :
    profileEventProbability r (occurrenceEvent A B) ≤
      (1-2*r none)*profileEventProbability (fun e ↦ r (some e))
        (occurrenceEvent (sectionEvent A false) (sectionEvent B false)) +
      r none*(profileEventProbability (fun e ↦ r (some e))
          (occurrenceEvent (sectionEvent A true) (sectionEvent B false)) +
        profileEventProbability (fun e ↦ r (some e))
          (occurrenceEvent (sectionEvent A false) (sectionEvent B true))) := by
  have h0 : sectionEvent (occurrenceEvent A B) false =
      occurrenceEvent (sectionEvent A false) (sectionEvent B false) := by
    ext η
    exact disjointOccurrence_section_false_iff hA hB η
  rw [profileEventProbability_option, h0]
  have hbound := mul_le_mul_of_nonneg_left
    (profile_occurrence_section_probability_bound (fun e ↦ hr0 (some e))
      (fun e ↦ hr1 (some e)) hA hB) (hr0 none)
  calc
    _ ≤ (1-r none)*profileEventProbability (fun e ↦ r (some e))
        (occurrenceEvent (sectionEvent A false) (sectionEvent B false)) +
      r none*(profileEventProbability (fun e ↦ r (some e))
          (occurrenceEvent (sectionEvent A true) (sectionEvent B false)) +
        profileEventProbability (fun e ↦ r (some e))
          (occurrenceEvent (sectionEvent A false) (sectionEvent B true)) -
        profileEventProbability (fun e ↦ r (some e))
          (occurrenceEvent (sectionEvent A false) (sectionEvent B false))) := by linarith [hbound]
    _ = _ := by ring

/-- The range restriction is coordinatewise, rather than a homogeneous scalar. -/
def LowDensityProfileBK (E : Type*) [Fintype E] : Prop :=
  ∀ r : E → ℝ, (∀ e, 0 ≤ r e) → (∀ e, r e ≤ 1/2) →
    ∀ A B : Set (E → Bool), Increasing A → Increasing B →
      profileEventProbability r (occurrenceEvent A B) ≤
        profileEventProbability r A*profileEventProbability r B

lemma lowDensityProfileBK_option {E : Type*} [Fintype E]
    (hBK : LowDensityProfileBK E) : LowDensityProfileBK (Option E) := by
  intro r hr0 hrHalf A B hA hB
  have hr1 : ∀ e, r e ≤ 1 := fun e ↦ (hrHalf e).trans (by norm_num)
  have h00 := hBK (fun e ↦ r (some e)) (fun e ↦ hr0 (some e)) (fun e ↦ hrHalf (some e))
    (sectionEvent A false) (sectionEvent B false) (increasing_section hA false) (increasing_section hB false)
  have h10 := hBK (fun e ↦ r (some e)) (fun e ↦ hr0 (some e)) (fun e ↦ hrHalf (some e))
    (sectionEvent A true) (sectionEvent B false) (increasing_section hA true) (increasing_section hB false)
  have h01 := hBK (fun e ↦ r (some e)) (fun e ↦ hr0 (some e)) (fun e ↦ hrHalf (some e))
    (sectionEvent A false) (sectionEvent B true) (increasing_section hA false) (increasing_section hB true)
  have hc : 0 ≤ 1-2*r none := by linarith [hrHalf none]
  have hrec := profile_eventProbability_occurrence_option hr0 hr1 hA hB
  have hfirst : profileEventProbability r (occurrenceEvent A B) ≤
      (1-2*r none)*(profileEventProbability (fun e ↦ r (some e)) (sectionEvent A false)*
        profileEventProbability (fun e ↦ r (some e)) (sectionEvent B false)) +
      r none*(profileEventProbability (fun e ↦ r (some e)) (sectionEvent A true)*
          profileEventProbability (fun e ↦ r (some e)) (sectionEvent B false) +
        profileEventProbability (fun e ↦ r (some e)) (sectionEvent A false)*
          profileEventProbability (fun e ↦ r (some e)) (sectionEvent B true)) := by
    apply hrec.trans
    have hm00 := mul_le_mul_of_nonneg_left h00 hc
    have hm10 := mul_le_mul_of_nonneg_left h10 (hr0 none)
    have hm01 := mul_le_mul_of_nonneg_left h01 (hr0 none)
    nlinarith
  have ha := profileEventProbability_mono (fun e ↦ hr0 (some e)) (fun e ↦ hr1 (some e))
    (section_false_subset_true hA)
  have hb := profileEventProbability_mono (fun e ↦ hr0 (some e)) (fun e ↦ hr1 (some e))
    (section_false_subset_true hB)
  rw [profileEventProbability_option r A, profileEventProbability_option r B]
  exact hfirst.trans (bk_step_arithmetic ha hb)

lemma profileEventProbability_pullEvent {E F : Type*} [Fintype E] [Fintype F]
    (e : E ≃ F) (r : F → ℝ) (A : Set (F → Bool)) :
    profileEventProbability (r ∘ e) (pullEvent e A) = profileEventProbability r A := by
  change (∑ η : E → Bool, (if coordinateEquiv e η ∈ A then (1 : ℝ) else 0)*
      ∏ a : E, if η a then r (e a) else 1-r (e a)) =
    ∑ θ : F → Bool, (if θ ∈ A then (1 : ℝ) else 0)*∏ f : F, if θ f then r f else 1-r f
  apply Fintype.sum_equiv (coordinateEquiv e)
  intro η
  congr 1
  exact Fintype.prod_equiv e _ _ (fun a ↦ by simp [coordinateEquiv])

lemma profileEventProbability_occurrence_pullEvent {E F : Type*} [Fintype E] [Fintype F]
    (e : E ≃ F) (r : F → ℝ) (A B : Set (F → Bool)) :
    profileEventProbability (r ∘ e) (occurrenceEvent (pullEvent e A) (pullEvent e B)) =
      profileEventProbability r (occurrenceEvent A B) := by
  have heq : occurrenceEvent (pullEvent e A) (pullEvent e B) = pullEvent e (occurrenceEvent A B) := by
    ext η
    exact disjointOccurrence_pullEvent_iff e A B η
  rw [heq]
  exact profileEventProbability_pullEvent e r _

lemma lowDensityProfileBK_equiv {E F : Type*} [Fintype E] [Fintype F]
    (e : E ≃ F) (hBK : LowDensityProfileBK E) : LowDensityProfileBK F := by
  intro r hr0 hrHalf A B hA hB
  have h := hBK (r ∘ e) (fun a ↦ hr0 (e a)) (fun a ↦ hrHalf (e a))
    (pullEvent e A) (pullEvent e B) (increasing_pullEvent e hA) (increasing_pullEvent e hB)
  rw [profileEventProbability_occurrence_pullEvent, profileEventProbability_pullEvent,
    profileEventProbability_pullEvent] at h
  exact h

lemma lowDensityProfileBK_empty : LowDensityProfileBK PEmpty := by
  intro r _ _ A B _ _
  let η : PEmpty → Bool := fun e ↦ nomatch e
  have hprob (C : Set (PEmpty → Bool)) : profileEventProbability r C = if η ∈ C then 1 else 0 := by
    unfold profileEventProbability finiteExpectationProfile
    rw [Finset.sum_eq_single η]
    · simp
    · intro θ _ hθη
      exact False.elim (hθη (by funext e; exact PEmpty.elim e))
    · intro hn
      exact False.elim (hn (by
        apply Finset.mem_singleton.mpr
        funext e
        exact PEmpty.elim e))
  rw [hprob, hprob, hprob]
  by_cases h : DisjointOccurrence A B η
  · have hm := disjointOccurrence_mem h
    simp [occurrenceEvent, h, hm.1, hm.2]
  · by_cases ha : η ∈ A <;> by_cases hb : η ∈ B <;> simp [occurrenceEvent, h, ha, hb]

/-- Genuine finite low-density profile BK, obtained by independent-coordinate
induction, not supplied as a hypothesis. -/
theorem lowDensity_profile_bk {E : Type*} [Fintype E] : LowDensityProfileBK E := by
  refine Fintype.induction_empty_option (P := fun α [h : Fintype α] ↦ @LowDensityProfileBK α h)
    ?_ lowDensityProfileBK_empty ?_ E
  · intro α β hβ e hBK
    let : Fintype α := Fintype.ofEquiv β e.symm
    exact lowDensityProfileBK_equiv e hBK
  · intro α hα hBK
    exact lowDensityProfileBK_option hBK

lemma profileEventProbability_eq_measureReal {E : Type*} [Fintype E]
    (r : E → unitInterval) (A : Set (E → Bool)) :
    profileEventProbability (fun e ↦ (r e : ℝ)) A =
      (Measure.pi (fun e ↦ bernoulliMeasure true false (r e))).real A := by
  have hI := integral_finite_bernoulliProfile r (fun η : E → Bool ↦ if η ∈ A then (1 : ℝ) else 0)
  have hm : MeasurableSet A := (Set.toFinite A).measurableSet
  have hμ : (∫ η : E → Bool, (if η ∈ A then (1 : ℝ) else 0)
      ∂(Measure.pi (fun e ↦ bernoulliMeasure true false (r e)))) =
      (Measure.pi (fun e ↦ bernoulliMeasure true false (r e))).real A := by
    convert! integral_indicator_one hm using 1
  exact hI.symm.trans hμ

/-- Actual independent finite Bernoulli product law, every coordinate <=1/2.
The conclusion retains BOTH probabilities under the same profile. -/
theorem finite_bernoulliProfile_bk_le_half {E : Type*} [Fintype E]
    (r : E → unitInterval) (hrHalf : ∀ e, (r e : ℝ) ≤ 1/2)
    (A B : Set (E → Bool)) (hA : Increasing A) (hB : Increasing B) :
    (Measure.pi (fun e ↦ bernoulliMeasure true false (r e))).real (occurrenceEvent A B) ≤
      (Measure.pi (fun e ↦ bernoulliMeasure true false (r e))).real A *
        (Measure.pi (fun e ↦ bernoulliMeasure true false (r e))).real B := by
  have h := lowDensity_profile_bk (fun e ↦ (r e : ℝ)) (fun e ↦ (r e).2.1) hrHalf A B hA hB
  rw [profileEventProbability_eq_measureReal, profileEventProbability_eq_measureReal,
    profileEventProbability_eq_measureReal] at h
  exact h

end NearCritical.BK
