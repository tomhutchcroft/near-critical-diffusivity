module

public import NearCritical.ORParameter
public import NearCritical.BKEndpoints
public import NearCritical.ORDisjointOccurrence

/-! Finite Bernoulli BK for every p in [0,1]. The low-density theorem is
transported through an exact OR product-law refinement; p=1 is deterministic. -/
@[expose] public section
noncomputable section
namespace NearCritical.BK
open Set MeasureTheory ProbabilityTheory

/-- Finite BK at every Bernoulli parameter, using the original disjoint-occurrence
operator and no restriction p<=1/2. -/
theorem bk_eventProbability {E : Type*} [Fintype E] (p : unitInterval)
    (A B : Set (E → Bool)) (hA : Increasing A) (hB : Increasing B) :
    eventProbability (p : ℝ) (occurrenceEvent A B) ≤
      eventProbability (p : ℝ) A * eventProbability (p : ℝ) B := by
  classical
  by_cases hp : (p : ℝ) < 1
  · obtain ⟨m, _, q, hq, hparam⟩ := exists_or_parameter p hp
    have hsub := orProject_preimage_occurrence_subset m hA hB
    have hmono := eventProbability_mono q.property.1 q.property.2 hsub
    have hBK := lowDensity_bk (E := E × Fin m) (q : ℝ) q.property.1 hq
      ((orProject m) ⁻¹' A) ((orProject m) ⁻¹' B)
      (increasing_preimage_orProject m hA) (increasing_preimage_orProject m hB)
    have h := hmono.trans hBK
    rw [eventProbability_orProject m p q hparam (occurrenceEvent A B),
      eventProbability_orProject m p q hparam A,
      eventProbability_orProject m p q hparam B] at h
    exact h
  · have hp1 : (p : ℝ) = 1 := le_antisymm p.property.2 (not_lt.mp hp)
    rw [hp1]
    exact bk_at_one A B

/-- BK for the actual finite independent Bernoulli product law, at every p. -/
theorem finite_bernoulli_bk {E : Type*} [Fintype E] (p : unitInterval)
    (A B : Set (E → Bool)) (hA : Increasing A) (hB : Increasing B) :
    (Measure.pi (fun _ : E ↦ bernoulliMeasure true false p)).real (occurrenceEvent A B) ≤
      (Measure.pi (fun _ : E ↦ bernoulliMeasure true false p)).real A *
      (Measure.pi (fun _ : E ↦ bernoulliMeasure true false p)).real B := by
  have h := bk_eventProbability p A B hA hB
  rw [eventProbability_eq_measureReal p, eventProbability_eq_measureReal p,
    eventProbability_eq_measureReal p] at h
  exact h

end NearCritical.BK

namespace NearCritical.Network
open Set MeasureTheory ProbabilityTheory
variable {V E : Type*} (G : NearCritical.Network V E)

/-- All-parameter BK for the exact connection certificates used in the
finite-network two-arm and pivotal-support proofs. -/
theorem disjointBoundaryConnections_probability [Fintype E]
    (p : unitInterval) (x y : V) (A B : Set V) :
    (Measure.pi (fun _ : E ↦ bernoulliMeasure true false p)).real
        {η | G.DisjointBoundaryConnections (binaryWeights η) x A y B} ≤
      (Measure.pi (fun _ : E ↦ bernoulliMeasure true false p)).real
        (G.boundaryConnectionEvent x A) *
      (Measure.pi (fun _ : E ↦ bernoulliMeasure true false p)).real
        (G.boundaryConnectionEvent y B) := by
  have heq : {η | G.DisjointBoundaryConnections (binaryWeights η) x A y B} =
      BK.occurrenceEvent (G.boundaryConnectionEvent x A) (G.boundaryConnectionEvent y B) := by
    ext η
    exact G.disjointBoundaryConnections_iff_disjointOccurrence η x y A B
  rw [heq]
  exact BK.finite_bernoulli_bk p _ _
    (G.boundaryConnectionEvent_increasing x A) (G.boundaryConnectionEvent_increasing y B)

end NearCritical.Network
