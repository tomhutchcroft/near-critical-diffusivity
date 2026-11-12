module

public import NearCritical.ExternalTranscriptExpectation

/-! Finite-mass entropy cost for the imported Bernoulli query-tree references.
 This uses finite real-density divergence,
not Mathlib measure klDiv, and retains both parameter interior assumptions. -/
@[expose] public section
noncomputable section
namespace NearCritical.External
open OAI.CriticalPercolation MeasureTheory
open scoped Classical BigOperators

private theorem divergence_scaled_pair {X : Type*} [Fintype X]
    (P R : X → ℝ) (hP : ∀ x, 0 < P x) (hR : ∀ x, 0 < R x)
    (hm : ∑ x, P x = 1) {c d : ℝ} (hc : 0 < c) (hd : 0 < d) :
    FiniteEntropy.divergence (fun x => c * P x) (fun x => d * R x) =
      c * FiniteEntropy.divergence P R + c * Real.log (c / d) := by
  have ht (x : X) :
      (c * P x) * Real.log ((c * P x) / (d * R x)) =
        c * (P x * Real.log (P x / R x)) + (c * Real.log (c / d)) * P x := by
    rw [Real.log_div (mul_pos hc (hP x)).ne' (mul_pos hd (hR x)).ne',
      Real.log_mul hc.ne' (hP x).ne', Real.log_mul hd.ne' (hR x).ne',
      Real.log_div (hP x).ne' (hR x).ne', Real.log_div hc.ne' hd.ne']
    ring
  simp only [FiniteEntropy.divergence, ht, Finset.sum_add_distrib,
    ← Finset.mul_sum, hm, mul_one]

/-- Expected reference depth obeys the ordinary two-branch query recurrence. -/
theorem expectedTranscriptDepth_ask {E : Type*} (e : E) (left right : QueryTree E)
    (q : ℝ) :
    expectedTranscriptDepth (.ask e left right) q =
      1 + (1 - q) * expectedTranscriptDepth left q + q * expectedTranscriptDepth right q := by
  simp only [expectedTranscriptDepth, Fintype.sum_sum_type, QueryTree.reference,
    queryLeafDepth, Nat.cast_add, Nat.cast_one, mul_add, Finset.sum_add_distrib,
    mul_assoc, ← Finset.mul_sum, QueryTree.reference_sum, mul_one]
  ring

/-- Exact finite transcript entropy: one-query Bernoulli divergence times
reference-weighted expected query count. This is an algebraic reference-law
identity, independent of query-tree validity; actual-law use needs validity. -/
theorem finite_tree_entropy_eq_cost {E : Type*} (t : QueryTree E)
    {q p : ℝ} (hq : q ∈ Set.Ioo (0 : ℝ) 1) (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    FiniteEntropy.divergence (t.reference q) (t.reference p) =
      FiniteEntropy.binaryDivergence q p * expectedTranscriptDepth t q := by
  induction t with
  | stop => simp [FiniteEntropy.divergence, QueryTree.reference,
      expectedTranscriptDepth, queryLeafDepth, QueryTree.Leaf]
  | ask e left right hl hr =>
    change (∑ leaf : Sum left.Leaf right.Leaf,
      (QueryTree.ask e left right).reference q leaf *
        Real.log ((QueryTree.ask e left right).reference q leaf /
          (QueryTree.ask e left right).reference p leaf)) = _
    rw [Fintype.sum_sum_type]
    change FiniteEntropy.divergence (fun l => (1-q) * left.reference q l)
        (fun l => (1-p) * left.reference p l) +
      FiniteEntropy.divergence (fun l => q * right.reference q l)
        (fun l => p * right.reference p l) = _
    rw [divergence_scaled_pair (left.reference q) (left.reference p)
      (QueryTree.reference_pos hq left) (QueryTree.reference_pos hp left)
      (QueryTree.reference_sum q left) (sub_pos.mpr hq.2) (sub_pos.mpr hp.2),
      divergence_scaled_pair (right.reference q) (right.reference p)
      (QueryTree.reference_pos hq right) (QueryTree.reference_pos hp right)
      (QueryTree.reference_sum q right) hq.1 hp.1,
      hl, hr, expectedTranscriptDepth_ask]
    unfold FiniteEntropy.binaryDivergence
    ring

/-- The imported one-query quadratic entropy bound extends to the entire
finite transcript with its expected query cost as multiplier. -/
theorem finite_tree_entropy_le_quadratic_cost {E : Type*} (t : QueryTree E)
    {q p : ℝ} (hq : q ∈ Set.Ioo (0 : ℝ) 1) (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    FiniteEntropy.divergence (t.reference q) (t.reference p) ≤
      ((q - p)^2 / (p * (1-p))) * expectedTranscriptDepth t q := by
  rw [finite_tree_entropy_eq_cost t hq hp]
  have hdepth : 0 ≤ expectedTranscriptDepth t q :=
    Finset.sum_nonneg (fun leaf _ =>
      mul_nonneg (QueryTree.reference_pos hq t leaf).le (Nat.cast_nonneg _))
  exact mul_le_mul_of_nonneg_right
    (FiniteEntropy.binaryDivergence_upper hp ⟨hq.1.le, hq.2.le⟩) hdepth

/-- For a valid imported search, the multiplier is its actual expected query
count under the lower-parameter input law. The finite divergence here is that
of its actual leaf masses, as identified by actual_search_transcript_leaf_probability. -/
theorem actual_search_entropy_le_query_cost {d : ℕ} (q p : unitInterval)
    (hq : (q : ℝ) ∈ Set.Ioo (0 : ℝ) 1) (hp : (p : ℝ) ∈ Set.Ioo (0 : ℝ) 1)
    (D : Finset (Bond d)) {R : Type*} (t : SearchTree D R) (used : Finset D)
    (ht : t.Valid used) :
    FiniteEntropy.divergence ((searchTranscriptTree t).reference (q : ℝ))
      ((searchTranscriptTree t).reference (p : ℝ)) ≤
      (((q : ℝ) - (p : ℝ))^2 / ((p : ℝ) * (1-(p : ℝ)))) *
        (∫ ω, ((t.reads (D.restrict ω)).length : ℝ) ∂percolation d q) := by
  rw [integral_search_transcript_query_count q D t used ht]
  exact finite_tree_entropy_le_quadratic_cost (searchTranscriptTree t) hq hp

end NearCritical.External
