import Percolation.Literature.SharpnessDCTProofs
import NearCritical.Events

/-!
Imported sharpness theorem from anthropics/formal-math at commit
795efb86f191735c5481675763537cfb4ff37e55 (Apache-2.0).
This entry point deliberately retains the upstream model. No identification
with NearCritical.percolation or its critical parameter is asserted here.
See third_party/formal-math for attribution and the source manifest.
-/

namespace NearCritical.External

/-- Encode the project's configuration as the set of its open undirected edges. -/
def edgeSetConfig {d : ℕ} (ω : Configuration d) :
    Percolation.Literature.BondConfig (Vertex d) := (NearCritical.openGraph ω).edgeSet

/-- The edge-set encoding is measurable for the actual product sigma-algebras. -/
theorem measurable_edgeSetConfig (d : ℕ) :
    Measurable (edgeSetConfig : Configuration d →
      Percolation.Literature.BondConfig (Vertex d)) := by
  apply measurable_set_iff.2
  intro z
  induction z using Sym2.ind with
  | h x y =>
    apply measurableSet_setOfPred.1
    simpa only [edgeSetConfig, SimpleGraph.mem_edgeSet] using
      (measurableSet_open_adj x y)

@[simp] theorem openGraph_edgeSetConfig {d : ℕ} (ω : Configuration d) :
    Percolation.Literature.openGraph (edgeSetConfig ω) = NearCritical.openGraph ω :=
  SimpleGraph.fromEdgeSet_edgeSet _

/-- The encoding preserves the actual unrestricted connection event exactly. -/
@[simp] theorem connection_preimage {d : ℕ} (x y : Vertex d) :
    edgeSetConfig ⁻¹' Percolation.Literature.openConn x y = connectionEvent x y := by
  ext ω
  change (Percolation.Literature.openGraph (edgeSetConfig ω)).Reachable x y ↔
    (NearCritical.openGraph ω).Reachable x y
  rw [openGraph_edgeSetConfig]

/-- The encoding preserves infinite-cluster membership, without a law assumption. -/
@[simp] theorem infiniteCluster_preimage (d : ℕ) :
    edgeSetConfig ⁻¹' Percolation.Literature.percolatesAt (0 : Vertex d) =
      infiniteClusterEvent d := by
  ext ω
  change ({y | (Percolation.Literature.openGraph (edgeSetConfig ω)).Reachable 0 y}).Infinite ↔
    ({y | (NearCritical.openGraph ω).Reachable 0 y}).Infinite
  rw [openGraph_edgeSetConfig]


/-- Subcritical exponential decay in the imported edge-set model.
The measure/critical-point bridge to NearCritical remains to be proved. -/
theorem subcritical_exponential_decay {d : ℕ} (hd : 2 ≤ d)
    (p : unitInterval)
    (hp : (p : ℝ) < Percolation.Literature.criticalProb
      (Percolation.Literature.LatticeModels.zdGraph d) 0) :
    ∃ c > 0, ∀ n : ℕ,
      (Percolation.Literature.bondPercolation
        (Percolation.Literature.LatticeModels.zdGraph d) p).real
        (Percolation.Literature.siteToBoundary d n) ≤ Real.exp (-c * n) :=
  Percolation.Literature.DCT16.perc_sharpness_holds hd p hp

end NearCritical.External
