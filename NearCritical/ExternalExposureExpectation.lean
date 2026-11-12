module

public import NearCritical.ExternalExposureCost
public import NearCritical.HeartConnectionCount

/-! Actual finite-component expectation bridge for the imported exposure.
Reuses existing project finite-support integrability and first-moment identity.
 Does not supply a common stopping-rule or KL argument. -/
@[expose] public section
noncomputable section
namespace NearCritical.External
open OAI.CriticalPercolation MeasureTheory
open scoped Classical

/-- The actual number of queries in the fully fueled finite-domain exposure. -/
def exposureQueryCount {d : ℕ} (U : Finset (Vertex d)) (x : Vertex d)
    (ω : Configuration d) : ℝ :=
  (((ExactExposure.compile (finiteBondSearchGraph (internalBondSet U))
    (internalBondSet U).card (rootExposureState (internalBondSet U) x)).reads
      (fun e => ω e.val)).length : ℝ)

/-- For an inside root the final reached set equals the project's domain-checked
finite component. The root hypothesis prevents an extra isolated outside vertex. -/
theorem exposure_reached_eq_finiteBoxCluster {d : ℕ} (U : Finset (Vertex d))
    (x : Vertex d) (hx : x ∈ U) (ω : Configuration d) :
    ((ExactExposure.compile (finiteBondSearchGraph (internalBondSet U))
      (internalBondSet U).card (rootExposureState (internalBondSet U) x)).run
        (fun e => ω e.val)).reached = finiteBoxCluster ω U x := by
  ext y
  rw [finite_exposure_reached_iff_actual, mem_finiteBoxCluster]
  constructor
  · intro hxy
    obtain ⟨walk⟩ := hxy
    exact ⟨restrictedWalk_support walk hx y walk.end_mem_support, ⟨walk⟩⟩
  · exact fun h => h.2

private theorem heart_self_eq_cluster_card {d : ℕ} (U : Finset (Vertex d))
    (x : Vertex d) (ω : Configuration d) :
    heartConnectionCount U U x ω = ((finiteBoxCluster ω U x).card : ℝ) := by
  have he : U.filter (fun y => y ∈ finiteBoxCluster ω U x) = finiteBoxCluster ω U x := by
    ext y
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨finiteBoxCluster_subset ω U x h, h⟩⟩
  simp only [heartConnectionCount, he]

/-- The real query-count observable is integrable under the actual product law. -/
theorem integrable_exposureQueryCount {d : ℕ} (p : unitInterval)
    (U : Finset (Vertex d)) (x : Vertex d) :
    Integrable (exposureQueryCount U x) (percolation d p) := by
  exact percolation_cylinder_integrable d p (internalBondSet U)
    (fun ξ => (((ExactExposure.compile (finiteBondSearchGraph (internalBondSet U))
      (internalBondSet U).card (rootExposureState (internalBondSet U) x)).reads ξ).length : ℝ))

/-- Actual finite-domain query cost, charged to the actual restricted component. -/
theorem exposureQueryCount_le_cluster {d : ℕ} (U : Finset (Vertex d))
    (x : Vertex d) (hx : x ∈ U) (ω : Configuration d) :
    exposureQueryCount U x ω ≤ (2 * d : ℕ) * ((finiteBoxCluster ω U x).card : ℝ) := by
  have h := finite_exposure_query_cost (internalBondSet U) x (internalBondSet U).card ω
  dsimp only at h
  rw [exposure_reached_eq_finiteBoxCluster U x hx ω] at h
  unfold exposureQueryCount
  exact_mod_cast (h.trans_eq (Nat.mul_comm _ _))

/-- Expected query cost is at most 2d times the actual finite cluster first
moment, expressed in restricted singleton connection probabilities. -/
theorem integral_exposureQueryCount_le {d : ℕ} (p : unitInterval)
    (U : Finset (Vertex d)) (x : Vertex d) (hx : x ∈ U) :
    (∫ ω, exposureQueryCount U x ω ∂percolation d p) ≤
      (2 * d : ℕ) * ∑ y ∈ U, (percolation d p).real
        (connectionToSetEvent (U : Set (Vertex d)) x {y}) := by
  have hheart : Integrable (heartConnectionCount U U x) (percolation d p) :=
    integrable_heartConnectionCount_observable p U U x id
  calc
    _ ≤ ∫ ω, (2 * d : ℕ) * heartConnectionCount U U x ω ∂percolation d p := by
      apply integral_mono (integrable_exposureQueryCount p U x) (hheart.const_mul _)
      intro ω
      change exposureQueryCount U x ω ≤ (2 * d : ℕ) * heartConnectionCount U U x ω
      rw [heart_self_eq_cluster_card]
      exact exposureQueryCount_le_cluster U x hx ω
    _ = _ := by
      rw [integral_const_mul, integral_heartConnectionCount p U U x hx]

end NearCritical.External
