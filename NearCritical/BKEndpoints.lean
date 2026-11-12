module

public import NearCritical.BK

/-! Endpoint identities for finite Bernoulli laws. In particular the p=1 case
of BK is deterministic and does not require a refinement with q<=1/2. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Set Finset
open scoped Classical

lemma finiteExpectation_one {E : Type*} [Fintype E] (f : (E → Bool) → ℝ) :
    finiteExpectation 1 f = f (fun _ ↦ true) := by
  classical
  unfold finiteExpectation
  rw [Finset.sum_eq_single (fun _ ↦ true)]
  · simp
  · intro θ _ hθ
    have hnot : ¬∀ e, θ e = true := fun h ↦ hθ (funext h)
    obtain ⟨e, he⟩ := not_forall.mp hnot
    have hf : θ e = false := Bool.eq_false_iff.mpr he
    have hz : (∏ j : E, if θ j then (1 : ℝ) else 1 - 1) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ e)
      simp [hf]
    rw [hz, mul_zero]
  · simp

namespace BK

lemma eventProbability_one {E : Type*} [Fintype E] (A : Set (E → Bool)) :
    eventProbability 1 A = if (fun _ ↦ true) ∈ A then 1 else 0 :=
  finiteExpectation_one _

/-- BK at p=1 even for events that are not increasing. -/
theorem bk_at_one {E : Type*} [Fintype E] (A B : Set (E → Bool)) :
    eventProbability 1 (occurrenceEvent A B) ≤ eventProbability 1 A * eventProbability 1 B := by
  classical
  rw [eventProbability_one, eventProbability_one, eventProbability_one]
  by_cases h : DisjointOccurrence A B (fun _ ↦ true)
  · obtain ⟨hA, hB⟩ := disjointOccurrence_mem h
    simp [occurrenceEvent, h, hA, hB]
  · by_cases hA : (fun _ ↦ true) ∈ A <;> by_cases hB : (fun _ ↦ true) ∈ B <;>
      simp [occurrenceEvent, h, hA, hB]

end BK
end NearCritical
