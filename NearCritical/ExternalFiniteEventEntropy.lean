module

public import NearCritical.ExternalFiniteEntropyCost
public import NearCritical.ExternalEntropyComparison

/-! Binary event data processing for imported finite real-mass entropy, and
the Bernoulli bridge to the imported refined KL event bound. Reference event probabilities at 0 or 1 need separate treatment. -/
@[expose] public section
noncomputable section
namespace NearCritical.External
open MeasureTheory ProbabilityTheory OAI.CriticalPercolation
open scoped Classical BigOperators

/-- Total finite mass of an event. -/
def finiteEventMass {X : Type*} [Fintype X] (P : X → ℝ) (A : Set X) : ℝ :=
  ∑ x, if x ∈ A then P x else 0

/-- Binary masses of a normalized event indicator. -/
def eventBinaryMass (a : ℝ) (b : Bool) : ℝ := if b then a else 1-a

/-- Pushing a normalized finite mass along an event indicator gives its binary law. -/
theorem pushMass_event_indicator {X : Type*} [Fintype X]
    (P : X → ℝ) (hP : ∑ x, P x = 1) (A : Set X) :
    FiniteEntropy.pushMass (fun x => decide (x ∈ A)) P =
      eventBinaryMass (finiteEventMass P A) := by
  have htrue : FiniteEntropy.pushMass (fun x => decide (x ∈ A)) P true =
      finiteEventMass P A := by simp [FiniteEntropy.pushMass, finiteEventMass]
  have hsum := FiniteEntropy.pushMass_sum (fun x => decide (x ∈ A)) P
  rw [hP] at hsum
  simp only [Fintype.sum_bool, htrue] at hsum
  funext b
  cases b
  · simp only [eventBinaryMass, Bool.false_eq_true, ↓reduceIte]
    linarith
  · exact htrue

/-- Finite event data processing, in the binary divergence used by the imported
Bernoulli KL library. No measure-level finite KL formula is needed. -/
theorem finite_event_klBerReal_le {X : Type*} [Fintype X]
    (P R : X → ℝ) (hP : ∀ x, 0 ≤ P x) (hR : ∀ x, 0 ≤ R x)
    (hP1 : ∑ x, P x = 1) (hR1 : ∑ x, R x = 1)
    (hs : ∀ x, 0 < P x → 0 < R x) (A : Set X) :
    InformationTheory.klBerReal (finiteEventMass P A) (finiteEventMass R A) ≤
      FiniteEntropy.divergence P R := by
  have h := FiniteEntropy.divergence_pushMass_le (fun x => decide (x ∈ A)) P R hP hR hs
  rw [pushMass_event_indicator P hP1 A, pushMass_event_indicator R hR1 A] at h
  have heq (a b : ℝ) :
      FiniteEntropy.divergence (eventBinaryMass a) (eventBinaryMass b) =
        InformationTheory.klBerReal a b := by
    simp only [FiniteEntropy.divergence, Fintype.sum_bool, eventBinaryMass,
      Bool.false_eq_true, ↓reduceIte, InformationTheory.klBerReal_apply]
  rwa [heq] at h

/-- The imported refined comparison specializes to a binary entropy budget.
The reference parameter remains strictly interior; a may be an endpoint. -/
theorem binary_entropy_refined_difference {a b K : ℝ}
    (ha : a ∈ Set.Icc (0 : ℝ) 1) (hb : b ∈ Set.Ioo (0 : ℝ) 1)
    (hK : 0 ≤ K) (hbudget : InformationTheory.klBerReal a b ≤ K) :
    |a-b| ≤ 3 * Real.sqrt (max a b * K) := by
  let au : unitInterval := ⟨a, ha⟩
  let bu : unitInterval := ⟨b, ⟨hb.1.le, hb.2.le⟩⟩
  have hb0 : bu ≠ 0 := fun h => hb.1.ne' (congrArg Subtype.val h)
  have hb1 : bu ≠ 1 := fun h => hb.2.ne (congrArg Subtype.val h)
  have hKL : InformationTheory.klDiv (bernoulliMeasure true false au)
      (bernoulliMeasure true false bu) ≤ ENNReal.ofReal K := by
    rw [InformationTheory.klDiv_bernoulliMeasure_eq_klBerReal
      (by decide : true ≠ false) au hb0 hb1]
    exact ENNReal.ofReal_le_ofReal hbudget
  have hμ : (bernoulliMeasure true false au).real {true} = a :=
    bernoulliMeasure_real_apply_of_mem_of_notMem au (measurableSet_singleton true)
      (by simp) (by simp)
  have hν : (bernoulliMeasure true false bu).real {true} = b :=
    bernoulliMeasure_real_apply_of_mem_of_notMem bu (measurableSet_singleton true)
      (by simp) (by simp)
  have h := event_difference_le_three_sqrt_max_kl
    (bernoulliMeasure true false au) (bernoulliMeasure true false bu)
    {true} (measurableSet_singleton true) hK hKL
  simpa only [hμ, hν] using h

end NearCritical.External
