module

public import NearCritical.BK
public import NearCritical.ProductExpectation
public import Mathlib.Probability.ProductMeasure
public import Mathlib.MeasureTheory.Measure.Dirac.Basic

/-! The OR refinement map and its exact Bernoulli product-law pushforward. -/
@[expose] public section
noncomputable section
namespace NearCritical.BK
open Set MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

/-- One old coordinate is open when at least one refined bit is open. -/
def orProject (m : ℕ) {E : Type*} (ω : E × Fin m → Bool) (e : E) : Bool :=
  decide (∃ j : Fin m, ω (e, j) = true)

@[simp] lemma orProject_eq_true (m : ℕ) {E : Type*} (ω : E × Fin m → Bool) (e : E) :
    orProject m ω e = true ↔ ∃ j : Fin m, ω (e, j) = true := by
  simp [orProject]

/-- OR on a single block of refined bits. -/
def orBlock (m : ℕ) (ω : Fin m → Bool) : Bool := decide (∃ j, ω j = true)

@[simp] lemma orBlock_eq_false (m : ℕ) (ω : Fin m → Bool) :
    orBlock m ω = false ↔ ∀ j, ω j = false := by
  simp [orBlock]

lemma orBlock_false_preimage (m : ℕ) :
    (orBlock m) ⁻¹' ({false} : Set Bool) = {fun _ : Fin m ↦ false} := by
  ext ω
  simp [orBlock_eq_false, funext_iff]

lemma orBlock_false_probability (m : ℕ) (q : unitInterval) :
    ((Measure.pi (fun _ : Fin m ↦ bernoulliMeasure true false q)).map (orBlock m)).real {false} =
      (1 - (q : ℝ)) ^ m := by
  rw [map_measureReal_apply (measurable_of_finite _) (measurableSet_singleton false),
    orBlock_false_preimage, finite_bernoulli_singleton_real]
  simp

/-- OR of m independent q-bits is exactly Bernoulli with success probability
p=1-(1-q)^m, including the m=0 endpoint. -/
theorem orBlock_map_bernoulli (m : ℕ) (p q : unitInterval)
    (hp : (p : ℝ) = 1 - (1 - (q : ℝ)) ^ m) :
    (Measure.pi (fun _ : Fin m ↦ bernoulliMeasure true false q)).map (orBlock m) =
      bernoulliMeasure true false p := by
  apply MeasureTheory.ext_iff_measureReal_singleton.mpr
  intro b
  cases b
  · have hber : (bernoulliMeasure true false p).real {false} = 1 - (p : ℝ) := by
      simp
    rw [orBlock_false_probability, hber]
    linarith
  · have hc : ({false} : Set Bool)ᶜ = {true} := by ext b; cases b <;> simp
    have hber : (bernoulliMeasure true false p).real {true} = (p : ℝ) := by
      simp
    have htot := measureReal_add_measureReal_compl
      (μ := (Measure.pi (fun _ : Fin m ↦ bernoulliMeasure true false q)).map (orBlock m))
      (measurableSet_singleton false)
    rw [hc, orBlock_false_probability, probReal_univ] at htot
    rw [hber]
    linarith

/-- Exact independent product law under OR refinement. The product measure is
reindexed into independent blocks, then each block is mapped by its scalar OR. -/
theorem orProject_map_bernoulli {E : Type*} [Fintype E] (m : ℕ) (p q : unitInterval)
    (hp : (p : ℝ) = 1 - (1 - (q : ℝ)) ^ m) :
    (Measure.pi (fun _ : E × Fin m ↦ bernoulliMeasure true false q)).map (orProject m) =
      Measure.pi (fun _ : E ↦ bernoulliMeasure true false p) := by
  classical
  let curryMap : (E × Fin m → Bool) → (E → Fin m → Bool) :=
    MeasurableEquiv.curry E (Fin m) Bool
  let blockMap : (E → Fin m → Bool) → (E → Bool) := fun ω e ↦ orBlock m (ω e)
  have hcurry :
      (Measure.pi (fun _ : E × Fin m ↦ bernoulliMeasure true false q)).map curryMap =
        Measure.pi (fun _ : E ↦ Measure.pi (fun _ : Fin m ↦ bernoulliMeasure true false q)) := by
    simpa only [Measure.infinitePi_eq_pi] using
      (Measure.infinitePi_map_curry (fun (_ : E) (_ : Fin m) ↦ bernoulliMeasure true false q))
  have hblocks :
      (Measure.pi (fun _ : E ↦ Measure.pi (fun _ : Fin m ↦ bernoulliMeasure true false q))).map blockMap =
        Measure.pi (fun _ : E ↦ bernoulliMeasure true false p) := by
    rw [Measure.pi_map_pi (fun _ ↦ (measurable_of_finite (orBlock m)).aemeasurable)]
    simp only [orBlock_map_bernoulli m p q hp]
  calc
    _ = ((Measure.pi (fun _ : E × Fin m ↦ bernoulliMeasure true false q)).map curryMap).map blockMap := by
      rw [Measure.map_map (measurable_of_finite blockMap) (measurable_of_finite curryMap)]
      rfl
    _ = _ := by rw [hcurry, hblocks]

/-- The finite event-probability identity needed in the BK reduction. -/
theorem eventProbability_orProject {E : Type*} [Fintype E] (m : ℕ) (p q : unitInterval)
    (hp : (p : ℝ) = 1 - (1 - (q : ℝ)) ^ m) (A : Set (E → Bool)) :
    eventProbability (q : ℝ) ((orProject m) ⁻¹' A) = eventProbability (p : ℝ) A := by
  classical
  rw [eventProbability_eq_measureReal q, eventProbability_eq_measureReal p]
  rw [← orProject_map_bernoulli (E := E) m p q hp,
    map_measureReal_apply (measurable_of_finite _) (Set.toFinite A).measurableSet]

end NearCritical.BK
