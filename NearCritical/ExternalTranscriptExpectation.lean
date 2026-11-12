module

public import NearCritical.ExternalActualLeafLaw

/-! Finite leaf expectations under the actual bond law, reusing the imported
pushMass integration identity. The finite entropy
versus expected-depth identity remains a separate obligation. -/
@[expose] public section
noncomputable section
namespace NearCritical.External
open MeasureTheory OAI.CriticalPercolation
open scoped Classical BigOperators

/-- The number of queries on the branch ending at a given finite transcript leaf. -/
def queryLeafDepth {E : Type*} : (t : QueryTree E) → t.Leaf → ℕ
  | .stop, _ => 0
  | .ask _ left _, .inl leaf => queryLeafDepth left leaf + 1
  | .ask _ _ right, .inr leaf => queryLeafDepth right leaf + 1

/-- Leaf depth is exactly the length of the executed query list. -/
theorem queryLeafDepth_run {E : Type*} (t : QueryTree E) (ω : E → Bool) :
    queryLeafDepth t (t.run ω) = (t.reads ω).length := by
  induction t with
  | stop => rfl
  | ask e left right hl hr =>
    by_cases he : ω e = true
    · simpa [QueryTree.run, QueryTree.reads, queryLeafDepth, he] using hr
    · simpa [QueryTree.run, QueryTree.reads, queryLeafDepth, he] using hl

/-- Reference-weighted expected finite transcript depth. -/
def expectedTranscriptDepth {E : Type*} (t : QueryTree E) (p : ℝ) : ℝ :=
  ∑ leaf, t.reference p leaf * (queryLeafDepth t leaf : ℝ)

/-- Every real observable of a valid finite leaf transcript has its reference
mass expectation under the actual project model. No leaf-space measurability
hypothesis is required: the underlying finite coordinate observable is integrable. -/
theorem integral_queryTree_leaf_observable {d : ℕ} (p : unitInterval)
    (D : Finset (Bond d)) (t : QueryTree D) (used : Finset D)
    (ht : t.Valid used) (F : t.Leaf → ℝ) :
    (∫ ω, F (t.run (D.restrict ω)) ∂percolation d p) =
      ∑ leaf, t.reference (p : ℝ) leaf * F leaf := by
  have hdec : (fun a b : D => Classical.propDecidable (a = b)) =
      (inferInstance : DecidableEq D) := Subsingleton.elim _ _
  have ht' : @QueryTree.Valid D
      (fun a b => Classical.propDecidable (a = b)) t used := by
    rw [hdec]
    exact ht
  rw [percolation_cylinder_expectation d p D (fun ξ => F (t.run ξ)),
    finiteExpectation_eq_tree_expect (p : ℝ) (fun ξ => F (t.run ξ))]
  rw [FiniteProduct.expect_partition (QueryTree.bitWeight (p : ℝ)) t.run
    (fun leaf _ => F leaf)]
  apply Finset.sum_congr rfl
  intro leaf _
  have hf : (fun ξ => if t.run ξ = leaf then F leaf else 0) =
      (fun ξ => (if t.run ξ = leaf then (1 : ℝ) else 0) * F leaf) := by
    funext ξ
    split_ifs <;> simp
  rw [hf, FiniteProduct.expect_mul_const]
  rw [(QueryTree.expect_indicator (E := D) (p : ℝ) t.run leaf).trans
    (congrFun (QueryTree.reference_eq_product_push (p : ℝ) t used ht') leaf)]

/-- Actual expected finite query count equals reference-weighted leaf depth. -/
theorem integral_queryTree_query_count {d : ℕ} (p : unitInterval)
    (D : Finset (Bond d)) (t : QueryTree D) (used : Finset D) (ht : t.Valid used) :
    (∫ ω, ((t.reads (D.restrict ω)).length : ℝ) ∂percolation d p) =
      expectedTranscriptDepth t (p : ℝ) := by
  calc
    _ = ∫ ω, (queryLeafDepth t (t.run (D.restrict ω)) : ℝ) ∂percolation d p := by
      apply integral_congr_ae
      filter_upwards [] with ω
      rw [queryLeafDepth_run]
    _ = _ := by
      simpa only [expectedTranscriptDepth] using
        integral_queryTree_leaf_observable p D t used ht
          (fun leaf => (queryLeafDepth t leaf : ℝ))

/-- Converted search transcripts retain actual expected query cost exactly. -/
theorem integral_search_transcript_query_count {d : ℕ} (p : unitInterval)
    (D : Finset (Bond d)) {R : Type*} (t : SearchTree D R) (used : Finset D)
    (ht : t.Valid used) :
    (∫ ω, ((t.reads (D.restrict ω)).length : ℝ) ∂percolation d p) =
      expectedTranscriptDepth (searchTranscriptTree t) (p : ℝ) := by
  simpa only [search_transcript_reads] using
    integral_queryTree_query_count p D (searchTranscriptTree t) used
      (search_transcript_valid t used ht)

end NearCritical.External
