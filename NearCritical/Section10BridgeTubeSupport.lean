module

public import NearCritical.SelectedNestChain

@[expose] public section
noncomputable section
namespace NearCritical.NestSprinklingStep
open scoped Classical

/-- Every computed offspring has a short bridge in the union of the two
actual side regions. The joining bond belongs to this same union of vertex
supports, and the whole bridge excludes both examined masks. -/
theorem bridge_in_side_union {d : ℕ} {ι : Type*} {ω : Configuration d}
    {D : Set (Vertex d)} {B : ℝ} (s : NestSprinklingStep d ι ω D B)
    {c : ι} (hc : c ∈ s.offspring) :
    ∃ x ∈ s.sourceBoundary, ∃ y ∈ s.targetBoundary c, ∃ a b,
      (a, b) ∈ s.pivots ∧
      BoundedIntrinsicConnection (sprinklingBridgeGraph s.leftGraph s.rightGraph a b) x y B ∧
      sprinklingBridgeGraph s.leftGraph s.rightGraph a b ≤
        microscopicPieceGraph ω (s.leftRegion ∪ s.rightRegion)
          (exploredEdgeSet s.firstCube s.firstRevealed ∪
            exploredEdgeSet s.lastCube s.lastRevealed)ᶜ :=
  sprinkling_offspring_short_bridge (s.leftRegion ∪ s.rightRegion)
    s.leftRegion s.rightRegion s.firstCube s.firstRevealed s.lastCube s.lastRevealed
    Set.subset_union_left Set.subset_union_right s.left_avoid s.right_avoid
    s.left_deleted s.right_deleted s.sourceBoundary s.candidates s.targetBoundary
    s.pivots s.source_mem s.pivot_open hc s.intrinsic_bound

end NearCritical.NestSprinklingStep
