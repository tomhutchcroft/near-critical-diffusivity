module

public import NearCritical.ExternalPositiveEventComparison

/-! Actual finite search-output event comparison from the imported finite
entropy chain. No graph-event identification
or percolation parameter-window constant is supplied by this module. -/
@[expose] public section
noncomputable section
namespace NearCritical.External
open OAI.CriticalPercolation MeasureTheory
open scoped Classical BigOperators

/-- A leaf event interpreted in the actual bond configuration space. -/
def queryTreeEvent {d : ℕ} (D : Finset (Bond d)) (t : QueryTree D)
    (A : Set t.Leaf) : Set (Configuration d) := {ω | t.run (D.restrict ω) ∈ A}

/-- An arbitrary event of the result of a finite imported search. -/
def searchOutputEvent {d : ℕ} (D : Finset (Bond d)) {R : Type*}
    (t : SearchTree D R) (B : Set R) : Set (Configuration d) :=
  {ω | t.run (D.restrict ω) ∈ B}

theorem measurableSet_queryTreeEvent {d : ℕ} (D : Finset (Bond d))
    (t : QueryTree D) (A : Set t.Leaf) : MeasurableSet (queryTreeEvent D t A) := by
  have hm : MeasurableSet {ξ : D → Bool | t.run ξ ∈ A} := (Set.to_countable _).measurableSet
  exact hm.preimage (Finset.measurable_restrict D)

/-- Actual leaf-event probabilities are the imported reference event masses. -/
theorem actual_queryTree_event_probability {d : ℕ} (p : unitInterval)
    (D : Finset (Bond d)) (t : QueryTree D) (used : Finset D)
    (ht : t.Valid used) (A : Set t.Leaf) :
    (percolation d p).real (queryTreeEvent D t A) = finiteEventMass (t.reference (p : ℝ)) A := by
  calc
    _ = ∫ ω, (if t.run (D.restrict ω) ∈ A then (1 : ℝ) else 0) ∂percolation d p := by
      simpa only [Set.indicator, queryTreeEvent, Set.mem_setOf_eq, Pi.one_apply] using
        (integral_indicator_one (μ := percolation d p) (measurableSet_queryTreeEvent D t A)).symm
    _ = ∑ leaf, t.reference (p : ℝ) leaf * (if leaf ∈ A then (1 : ℝ) else 0) :=
      integral_queryTree_leaf_observable p D t used ht
        (fun leaf => if leaf ∈ A then (1 : ℝ) else 0)
    _ = _ := by simp only [finiteEventMass, mul_ite, mul_one, mul_zero]

/-- A finite reference-entropy budget controls an actual transcript event. -/
theorem actual_queryTree_event_entropy_budget {d : ℕ} (q p : unitInterval)
    (hq : (q : ℝ) ∈ Set.Ioo (0 : ℝ) 1) (hp : (p : ℝ) ∈ Set.Ioo (0 : ℝ) 1)
    (D : Finset (Bond d)) (t : QueryTree D) (used : Finset D) (ht : t.Valid used)
    (A : Set t.Leaf) {K : ℝ} (hK : 0 ≤ K)
    (hbudget : FiniteEntropy.divergence (t.reference (q : ℝ)) (t.reference (p : ℝ)) ≤ K) :
    |(percolation d q).real (queryTreeEvent D t A) -
      (percolation d p).real (queryTreeEvent D t A)| ≤
        3 * Real.sqrt (max ((percolation d q).real (queryTreeEvent D t A))
          ((percolation d p).real (queryTreeEvent D t A)) * K) := by
  have h := queryTree_refined_event_difference t hq hp A hK hbudget
  rw [← actual_queryTree_event_probability q D t used ht A,
    ← actual_queryTree_event_probability p D t used ht A] at h
  exact h

/-- Any event decoded from a valid finite search obeys the refined comparison,
with the actual expected number of queries under q in the entropy budget. -/
theorem actual_search_output_event_comparison {d : ℕ} (q p : unitInterval)
    (hq : (q : ℝ) ∈ Set.Ioo (0 : ℝ) 1) (hp : (p : ℝ) ∈ Set.Ioo (0 : ℝ) 1)
    (D : Finset (Bond d)) {R : Type*} (t : SearchTree D R) (used : Finset D)
    (ht : t.Valid used) (B : Set R) :
    |(percolation d q).real (searchOutputEvent D t B) -
      (percolation d p).real (searchOutputEvent D t B)| ≤
      3 * Real.sqrt (max ((percolation d q).real (searchOutputEvent D t B))
        ((percolation d p).real (searchOutputEvent D t B)) *
        ((((q : ℝ) - (p : ℝ))^2 / ((p : ℝ) * (1-(p : ℝ)))) *
          (∫ ω, ((t.reads (D.restrict ω)).length : ℝ) ∂percolation d q))) := by
  let A : Set (searchTranscriptTree t).Leaf := {leaf | decodeSearchTranscript t leaf ∈ B}
  have hevent : queryTreeEvent D (searchTranscriptTree t) A = searchOutputEvent D t B := by
    ext ω
    change decodeSearchTranscript t ((searchTranscriptTree t).run (D.restrict ω)) ∈ B ↔
      t.run (D.restrict ω) ∈ B
    rw [decode_search_transcript_run]
  have hK : 0 ≤ (((q : ℝ) - (p : ℝ))^2 / ((p : ℝ) * (1-(p : ℝ)))) *
      (∫ ω, ((t.reads (D.restrict ω)).length : ℝ) ∂percolation d q) :=
    mul_nonneg (div_nonneg (sq_nonneg _) (mul_nonneg p.2.1 (sub_nonneg.mpr p.2.2)))
      (integral_nonneg (fun ω => Nat.cast_nonneg _))
  have h := actual_queryTree_event_entropy_budget q p hq hp D (searchTranscriptTree t) used
    (search_transcript_valid t used ht) A hK (actual_search_entropy_le_query_cost q p hq hp D t used ht)
  rwa [hevent] at h

end NearCritical.External
