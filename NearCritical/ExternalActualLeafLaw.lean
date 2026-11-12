module

public import NearCritical.ExternalFiniteLeafLaw
public import NearCritical.ExternalFiniteTranscript
public import NearCritical.ProductExpectation

/-! Actual-law bridge for the imported finite Bernoulli leaf identity.
Uses project finite-cylinder integration; no new measure law hypothesis.
 No KL-cost identity or event comparison yet. -/
@[expose] public section
noncomputable section
namespace NearCritical.External
open MeasureTheory OAI.CriticalPercolation
open scoped Classical

/-- The upstream finite real-density expectation is the project's finite sum. -/
theorem finiteExpectation_eq_tree_expect {E : Type*} [Fintype E]
    (p : ℝ) (f : (E → Bool) → ℝ) :
    finiteExpectation p f = FiniteProduct.expect (QueryTree.bitWeight p) f := by
  simp only [finiteExpectation, FiniteProduct.expect, FiniteProduct.density, QueryTree.bitWeight]
  apply Finset.sum_congr rfl
  intro ω _
  exact mul_comm _ _

/-- A finite leaf transcript event is measurable under the actual bond model. -/
theorem measurableSet_queryTree_leaf {d : ℕ} (D : Finset (Bond d))
    (t : QueryTree D) (leaf : t.Leaf) :
    MeasurableSet {ω : Configuration d | t.run (D.restrict ω) = leaf} := by
  have hm : MeasurableSet {ξ : D → Bool | t.run ξ = leaf} :=
    (Set.to_countable _).measurableSet
  exact hm.preimage (Finset.measurable_restrict D)

/-- Every leaf of a valid finite query tree has exactly its Bernoulli reference
probability under the actual percolation law, including parameters 0 and 1. -/
theorem actual_queryTree_leaf_probability {d : ℕ} (p : unitInterval)
    (D : Finset (Bond d)) (t : QueryTree D) (used : Finset D)
    (ht : t.Valid used) (leaf : t.Leaf) :
    (percolation d p).real {ω | t.run (D.restrict ω) = leaf} =
      t.reference (p : ℝ) leaf := by
  have hdec : (fun a b : D => Classical.propDecidable (a = b)) =
      (inferInstance : DecidableEq D) := Subsingleton.elim _ _
  have ht' : @QueryTree.Valid D
      (fun a b => Classical.propDecidable (a = b)) t used := by
    rw [hdec]
    exact ht
  classical
  calc
    _ = ∫ ω, (if t.run (D.restrict ω) = leaf then (1 : ℝ) else 0) ∂percolation d p := by
      simpa only [Set.indicator, Set.mem_setOf_eq, Pi.one_apply] using
        (integral_indicator_one (μ := percolation d p)
          (measurableSet_queryTree_leaf D t leaf)).symm
    _ = finiteExpectation (p : ℝ) (fun ξ => if t.run ξ = leaf then (1 : ℝ) else 0) :=
      percolation_cylinder_expectation d p D
        (fun ξ => if t.run ξ = leaf then (1 : ℝ) else 0)
    _ = FiniteProduct.expect (QueryTree.bitWeight (p : ℝ))
        (fun ξ => if t.run ξ = leaf then (1 : ℝ) else 0) :=
      finiteExpectation_eq_tree_expect (p : ℝ)
        (fun ξ => if t.run ξ = leaf then (1 : ℝ) else 0)
    _ = t.reference (p : ℝ) leaf := by
      exact (QueryTree.expect_indicator (E := D) (p : ℝ) t.run leaf).trans
        (congrFun (QueryTree.reference_eq_product_push (p : ℝ) t used ht') leaf)

/-- The finite transcript conversion of any valid imported search has the
same exact actual-law leaf masses. -/
theorem actual_search_transcript_leaf_probability {d : ℕ} (p : unitInterval)
    (D : Finset (Bond d)) {R : Type*} (t : SearchTree D R) (used : Finset D)
    (ht : t.Valid used) (leaf : (searchTranscriptTree t).Leaf) :
    (percolation d p).real {ω | (searchTranscriptTree t).run (D.restrict ω) = leaf} =
      (searchTranscriptTree t).reference (p : ℝ) leaf :=
  actual_queryTree_leaf_probability p D (searchTranscriptTree t) used
    (search_transcript_valid t used ht) leaf

end NearCritical.External
