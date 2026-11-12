module

public import NearCritical.FinitePivotalAvoidance
public import NearCritical.ProfileBKStrict

/-! Closed-coordinate cancellation for the actual independent profile law.
These are the finite probability steps needed before the two-phase slab
Russo estimate. No profile factor is replaced by a homogeneous one. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Set Finset BernoulliCalculus MeasureTheory ProbabilityTheory
open scoped Classical

/-- Profile Mecke removes the closed-coordinate factor for every invariant
observable. This algebraic identity permits arbitrary real rates. -/
theorem finiteExpectationProfile_forceOpen_invariant_closed {E : Type*} [Fintype E]
    (r : E → ℝ) (e : E) (g : (E → Bool) → ℝ)
    (hinv : ∀ ω, g (forceOpen e ω) = g ω) :
    finiteExpectationProfile r (fun ω ↦ (if ω e then 0 else 1) * g ω) =
      (1-r e) * finiteExpectationProfile r g := by
  have hs : finiteExpectationProfile r (fun ω ↦ (if ω e then 0 else 1) * g ω) =
      finiteExpectationProfile r g -
        finiteExpectationProfile r (fun ω ↦ g ω * (if ω e then 1 else 0)) := by
    unfold finiteExpectationProfile
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro ω _
    cases h : ω e <;> simp [h]
  rw [hs, finiteExpectationProfile_mecke]
  have hfun : (fun ω ↦ g (forceOpen e ω)) = g := funext hinv
  rw [hfun]
  ring

/-- Avoiding certificates do not inspect the tested coordinate. -/
theorem finiteExpectationProfile_avoiding_closed_factor {E : Type*} [Fintype E]
    (r : E → ℝ) (e : E) (A B : Set (E → Bool)) :
    finiteExpectationProfile r (fun ω ↦ (if ω e then 0 else 1) *
      (if AvoidingDisjointOccurrence e A B ω then 1 else 0)) =
        (1-r e) * BK.profileEventProbability r
          {ω | AvoidingDisjointOccurrence e A B ω} := by
  apply finiteExpectationProfile_forceOpen_invariant_closed
  intro ω
  rw [avoidingDisjointOccurrence_forceOpen_iff]

/-- Cancellation depends only on the tested rate being different from one;
no inverse of another coordinate's rate is taken. -/
theorem finiteExpectationProfile_avoiding_russo_cancel {E : Type*} [Fintype E]
    (r : E → ℝ) (e : E) (he : r e ≠ 1) (A B : Set (E → Bool)) :
    (1-r e)⁻¹ * finiteExpectationProfile r (fun ω ↦ (if ω e then 0 else 1) *
      (if AvoidingDisjointOccurrence e A B ω then 1 else 0)) =
        BK.profileEventProbability r {ω | AvoidingDisjointOccurrence e A B ω} := by
  rw [finiteExpectationProfile_avoiding_closed_factor, ← mul_assoc,
    inv_mul_cancel₀ (sub_ne_zero.mpr he.symm), one_mul]

/-- Actual finite-profile BK after exact Russo cancellation. Both final
probabilities retain the original profile. Zero coordinate rates are allowed. -/
theorem finite_profile_avoiding_russo_bk {E : Type*} [Fintype E]
    (r : E → unitInterval) (P : unitInterval) (hP : (P : ℝ) < 1)
    (hr : ∀ e, r e ≤ P) (e : E)
    (A B : Set (E → Bool)) (hA : BK.Increasing A) (hB : BK.Increasing B) :
    (1-(r e : ℝ))⁻¹ * finiteExpectationProfile (fun f ↦ (r f : ℝ))
      (fun ω ↦ (if ω e then 0 else 1) *
        (if AvoidingDisjointOccurrence e A B ω then 1 else 0)) ≤
      (Measure.pi (fun f ↦ bernoulliMeasure true false (r f))).real A *
        (Measure.pi (fun f ↦ bernoulliMeasure true false (r f))).real B := by
  have he : (r e : ℝ) ≠ 1 := ne_of_lt (lt_of_le_of_lt (hr e) hP)
  have hmono := BK.profileEventProbability_mono (r := fun f ↦ (r f : ℝ))
    (fun f ↦ (r f).property.1) (fun f ↦ (r f).property.2)
    (show {ω | AvoidingDisjointOccurrence e A B ω} ⊆ BK.occurrenceEvent A B from
      fun _ h ↦ h.to_disjointOccurrence)
  have hBK := BK.finite_bernoulliProfile_bk_of_uniform_lt_one r P hP hr A B hA hB
  calc
    _ = BK.profileEventProbability (fun f ↦ (r f : ℝ))
        {ω | AvoidingDisjointOccurrence e A B ω} := by
      convert! finiteExpectationProfile_avoiding_russo_cancel
        (fun f ↦ (r f : ℝ)) e he A B using 1
    _ ≤ BK.profileEventProbability (fun f ↦ (r f : ℝ)) (BK.occurrenceEvent A B) := hmono
    _ = (Measure.pi (fun f ↦ bernoulliMeasure true false (r f))).real
        (BK.occurrenceEvent A B) := BK.profileEventProbability_eq_measureReal r _
    _ ≤ _ := hBK

end NearCritical
