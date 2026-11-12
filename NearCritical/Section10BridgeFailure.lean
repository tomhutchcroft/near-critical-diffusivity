module

public import NearCritical.Section10CoalescenceScale

@[expose] public section
namespace NearCritical.Section10
open MeasureTheory
open scoped ENNReal

/-- The four failure probabilities control failure of the actual
typicality predicate, without any independence between the tests. -/
theorem bridge_typicality_failure_le {d : ℕ} {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (offspring : Ω → Finset ι)
    (coalescing : Ω → Finset (Vertex d)) (diameter : Ω → ℕ)
    (minOff maxOff maxCoal maxDiam : ℕ) (hmin : 10 ≤ minOff) :
    μ {ω | ¬ IsTypicalSprinklingBridge (offspring ω) (coalescing ω) (diameter ω)
      minOff maxOff maxCoal maxDiam} ≤
      μ {ω | (offspring ω).card < minOff} +
        (μ {ω | maxOff < (offspring ω).card} +
          (μ {ω | maxCoal < (coalescing ω).card} + μ {ω | maxDiam < diameter ω})) := by
  let A := {ω | (offspring ω).card < minOff}
  let B := {ω | maxOff < (offspring ω).card}
  let C := {ω | maxCoal < (coalescing ω).card}
  let D := {ω | maxDiam < diameter ω}
  have hsub : {ω | ¬ IsTypicalSprinklingBridge (offspring ω) (coalescing ω) (diameter ω)
      minOff maxOff maxCoal maxDiam} ⊆ A ∪ (B ∪ (C ∪ D)) := by
    intro ω h
    simpa only [IsTypicalSprinklingBridge, hmin, true_and, not_and_or, not_le, A, B, C, D,
      Set.mem_setOf_eq, Set.mem_union] using h
  exact (measure_mono hsub).trans ((measure_union_le _ _).trans
    (add_le_add le_rfl ((measure_union_le _ _).trans (add_le_add le_rfl (measure_union_le _ _)))))

/-- A uniform coalescence first-moment bound permits a single coalescence
cutoff while the other three failure budgets are supplied independently. -/
theorem exists_bridge_typicality_coalescence_cutoff {d : ℕ} {Ω ι : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) (offspring : Ω → Finset ι)
    (coalescing : Ω → Finset (Vertex d)) (diameter : Ω → ℕ)
    (minOff maxOff maxDiam : ℕ) (hmin : 10 ≤ minOff) (K ε : ℝ) (hε : 0 < ε)
    (hcoal : ∀ m : ℕ, (m : ENNReal) * μ {ω | m ≤ (coalescing ω).card} ≤ ENNReal.ofReal K)
    (a b c : ENNReal)
    (ha : μ {ω | (offspring ω).card < minOff} ≤ a)
    (hb : μ {ω | maxOff < (offspring ω).card} ≤ b)
    (hc : μ {ω | maxDiam < diameter ω} ≤ c) :
    ∃ m : ℕ, 0 < m ∧
      μ {ω | ¬ IsTypicalSprinklingBridge (offspring ω) (coalescing ω) (diameter ω)
        minOff maxOff m maxDiam} ≤ a + (b + (ENNReal.ofReal ε + c)) := by
  obtain ⟨m, hm, htail⟩ := exists_bridge_coalescence_threshold K ε hε
  have hsub : {ω | m < (coalescing ω).card} ⊆ {ω | m ≤ (coalescing ω).card} := by
    intro ω h
    change m < (coalescing ω).card at h
    change m ≤ (coalescing ω).card
    exact le_of_lt h
  have hbad := (measure_mono hsub).trans (htail _ (hcoal m))
  exact ⟨m, hm, (bridge_typicality_failure_le μ offspring coalescing diameter
    minOff maxOff m maxDiam hmin).trans (add_le_add ha (add_le_add hb (add_le_add hbad hc)))⟩

end NearCritical.Section10
