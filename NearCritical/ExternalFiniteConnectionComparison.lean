module

public import NearCritical.ExternalActualEventComparison
public import NearCritical.ExternalExposureExpectation

/-! Actual finite connection-event entropy comparison, using the imported
exact exposure and finite entropy machinery. Parameter
window constants and half-space geometric specialization remain separate. -/
@[expose] public section
noncomputable section
namespace NearCritical.External
open OAI.CriticalPercolation MeasureTheory
open scoped Classical BigOperators

/-- Fully fueled finite-domain imported exact exposure. -/
def connectionExposureTree {d : ℕ} (U : Finset (Vertex d)) (x : Vertex d) :
    SearchTree (internalBondSet U) (ExactExposure.State (Vertex d) (internalBondSet U)) :=
  ExactExposure.compile (finiteBondSearchGraph (internalBondSet U))
    (internalBondSet U).card (rootExposureState (internalBondSet U) x)

/-- The source event's root/domain/target guards, read from the final reached set. -/
def connectionExposureOutput {d : ℕ} (U : Finset (Vertex d)) (x : Vertex d)
    (A : Set (Vertex d)) : Set (ExactExposure.State (Vertex d) (internalBondSet U)) :=
  {st | x ∈ U ∧ ∃ y ∈ st.reached, y ∈ A ∧ y ∈ U}

/-- Exact identification with the project's finite-domain connection event. -/
theorem connectionExposure_event_eq {d : ℕ} (U : Finset (Vertex d))
    (x : Vertex d) (A : Set (Vertex d)) :
    searchOutputEvent (internalBondSet U) (connectionExposureTree U x)
      (connectionExposureOutput U x A) = connectionToSetEvent (U : Set (Vertex d)) x A := by
  ext ω
  change (x ∈ U ∧ ∃ y ∈ ((ExactExposure.compile
      (finiteBondSearchGraph (internalBondSet U)) (internalBondSet U).card
      (rootExposureState (internalBondSet U) x)).run (fun e => ω e.val)).reached,
        y ∈ A ∧ y ∈ U) ↔ _
  exact (finite_exposure_connection_event_iff U x A ω).symm

/-- Refined actual finite-domain connection comparison. The entropy cost uses
the actual lower-law cluster first moment, with neither a law bridge nor an
expected-query bound supplied as a hypothesis. -/
theorem finite_connection_entropic_budget {d : ℕ} (q p : unitInterval)
    (hq : (q : ℝ) ∈ Set.Ioo (0 : ℝ) 1) (hp : (p : ℝ) ∈ Set.Ioo (0 : ℝ) 1)
    (U : Finset (Vertex d)) (x : Vertex d) (hx : x ∈ U) (A : Set (Vertex d)) :
    let E := connectionToSetEvent (U : Set (Vertex d)) x A
    |(percolation d q).real E - (percolation d p).real E| ≤
      3 * Real.sqrt (max ((percolation d q).real E) ((percolation d p).real E) *
        ((((q : ℝ) - (p : ℝ))^2 / ((p : ℝ) * (1-(p : ℝ)))) *
          ((2*d : ℕ) * ∑ y ∈ U, (percolation d q).real
            (connectionToSetEvent (U : Set (Vertex d)) x {y})))) := by
  have ht : (connectionExposureTree U x).Valid ∅ :=
    ExactExposure.compile_valid (finiteBondSearchGraph (internalBondSet U))
      (internalBondSet U).card (rootExposureState (internalBondSet U) x)
  have h := actual_search_output_event_comparison q p hq hp (internalBondSet U)
    (connectionExposureTree U x) ∅ ht (connectionExposureOutput U x A)
  rw [connectionExposure_event_eq] at h
  have hcost := integral_exposureQueryCount_le q U x hx
  have hcoef : 0 ≤ ((q : ℝ) - (p : ℝ))^2 / ((p : ℝ) * (1-(p : ℝ))) :=
    div_nonneg (sq_nonneg _) (mul_nonneg p.2.1 (sub_nonneg.mpr p.2.2))
  have hmax : 0 ≤ max
      ((percolation d q).real (connectionToSetEvent (U : Set (Vertex d)) x A))
      ((percolation d p).real (connectionToSetEvent (U : Set (Vertex d)) x A)) :=
    le_trans measureReal_nonneg (le_max_left _ _)
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Real.sqrt_le_sqrt
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hcost hcoef) hmax

end NearCritical.External
