module

public import NearCritical.Section8ExtensionDeletionCost

/-! Deleting the moat vertices has the same BK loss bound as deleting all
bonds incident to those vertices. This puts the probability comparison on
the vertex-restricted graph used by the cluster reveal. -/
@[expose] public section
noncomputable section

namespace NearCritical.SplitCrossDirect

open MeasureTheory
open scoped Classical

/-- The base connection survives deletion of the moat vertices up to the
sum of two-point products over the removed part of the tube. -/
theorem vertex_deletion_probability_cost {d : ℕ} (p : unitInterval)
    (T F : Finset (Vertex d)) (x y : Vertex d) (hx : x ∈ T \ F) (hy : y ∈ T \ F) :
    (percolation d p).real (connectionToSetEvent (T : Set (Vertex d)) x {y}) ≤
      (percolation d p).real (connectionToSetEvent (T \ F : Finset (Vertex d)) x {y}) +
        ∑ z ∈ F ∩ T,
          (percolation d p).real (connectionToSetEvent (T : Set (Vertex d)) x {z}) *
          (percolation d p).real (connectionToSetEvent (T : Set (Vertex d)) z {y}) := by
  have hsub : {ω | y ∈ sprinklingUnexploredCluster ω T T F x} ⊆
      connectionToSetEvent (T \ F : Finset (Vertex d)) x {y} := by
    intro ω hω
    have hpath := ((mem_sprinklingUnexploredCluster ω T T F x y).mp hω).2
    have hle : sprinklingUnexploredGraph ω T T F ≤
        restrictedGraph ω (T \ F : Finset (Vertex d)) := by
      intro a b h
      refine ⟨h.1, Finset.mem_sdiff.mpr ⟨h.2.1, ?_⟩,
        Finset.mem_sdiff.mpr ⟨h.2.2.1, ?_⟩⟩
      · intro ha
        exact h.2.2.2 ((pair_mem_exploredEdgeSet _ _ a b).mpr ⟨h.2.1, h.2.2.1, Or.inl ha⟩)
      · intro hb
        exact h.2.2.2 ((pair_mem_exploredEdgeSet _ _ a b).mpr ⟨h.2.1, h.2.2.1, Or.inr hb⟩)
    exact ⟨hx, y, rfl, hy, hpath.mono hle⟩
  exact (section8_extension_deletion_probability_cost p T T F x y).trans
    (add_le_add (measureReal_mono (μ := percolation d p) hsub (measure_ne_top _ _)) le_rfl)

end NearCritical.SplitCrossDirect
