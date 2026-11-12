import Percolation.Literature.UniquenessInfiniteCluster
import NearCritical.ExternalPercolation
import NearCritical.ChemicalConverse

/-!
Burton–Keane uniqueness imported from anthropics/formal-math commit
795efb86f191735c5481675763537cfb4ff37e55. License/NOTICE and original hashes
are retained in third_party/formal-math. This module is a new import candidate:
its Lean 4.35 target and axiom audit remain pending the shared resource slot.

The first result retains the upstream law. The second reduces the project's
actual named uniqueness input to the still-unproved encoding pushforward law;
it does not assert that this law, or the literature input, is discharged.
-/

namespace NearCritical.External
open MeasureTheory

/-- Pairwise infinite-cluster uniqueness under the imported edge-set law. -/
theorem upstream_ae_infiniteCluster_unique (d : ℕ) (p : unitInterval) :
    ∀ᵐ ω ∂Percolation.Literature.bondPercolation
        (Percolation.Literature.LatticeModels.zdGraph d) p,
      ∀ x y : Vertex d,
        (Percolation.Literature.openCluster ω x).Infinite →
        (Percolation.Literature.openCluster ω y).Infinite →
        (Percolation.Literature.openGraph ω).Reachable x y := by
  filter_upwards [Percolation.Literature.Grimmett1999_numInfiniteClusters_le_one_holds d p]
    with ω hω
  exact (Percolation.Literature.numInfiniteClusters_le_one_iff ω).1 hω

/-- Exact remaining model-law bridge for the chemical converse's named input. -/
theorem aeInfiniteClusterUniqueness_of_edgeSet_law (d : ℕ) (p : unitInterval)
    (hLaw : (NearCritical.percolation d p).map edgeSetConfig =
      Percolation.Literature.bondPercolation
        (Percolation.Literature.LatticeModels.zdGraph d) p) :
    NearCritical.AEInfiniteClusterUniqueness d p := by
  have h := upstream_ae_infiniteCluster_unique d p
  rw [← hLaw] at h
  have h' := ae_of_ae_map (measurable_edgeSetConfig d).aemeasurable h
  unfold NearCritical.AEInfiniteClusterUniqueness
  filter_upwards [h'] with ω hω
  intro x y hx hy
  have hxy : (NearCritical.cluster ω x).Infinite →
      (NearCritical.cluster ω y).Infinite →
      (NearCritical.openGraph ω).Reachable x y := by
    simpa only [Percolation.Literature.openCluster, NearCritical.cluster,
      openGraph_edgeSetConfig] using hω x y
  exact hxy hx hy

end NearCritical.External
