import NearCritical.Section10ActualStepData
import NearCritical.Section10SelectedPieceEdges
import NearCritical.Section10BridgeTubeSupport

noncomputable section
namespace NearCritical.Section10
open scoped Classical

/-- The actual lattice-rule side regions form the geometric tube associated
with its route label. This lets bridge support use the tube's physical index. -/
theorem actual_layout_side_union_eq_coarseTube {D : ℕ} (typ : TypicalParameters)
    (t : ℕ) (ht : 9 ≤ t) (k : ℕ) (hk : 0 < k) (MOff Mcoal Kdiam M : ℕ)
    {ℓ : RouteLabel D} (hℓ : HasTube M ℓ) :
    let L := actualLayout D typ t ht k hk MOff Mcoal Kdiam M
    ((L.L ℓ : Set (Vertex (D + 1))) ∪ (L.R ℓ : Set (Vertex (D + 1)))) =
      coarseTubeVertices (2 * (t : ℝ)) (vecSite ℓ.site) (dirOf ℓ) := by
  intro L
  change
    ((actualLayout D typ t ht k hk MOff Mcoal Kdiam M).L ℓ : Set (Vertex (D + 1))) ∪
      ((actualLayout D typ t ht k hk MOff Mcoal Kdiam M).R ℓ : Set (Vertex (D + 1))) = _
  rw [actual_L_eq typ t ht k hk MOff Mcoal Kdiam M hℓ,
    actual_R_eq typ t ht k hk MOff Mcoal Kdiam M hℓ]
  ext x
  let c := siteCenter t ℓ.site
  let y := x - c
  have hxy : c + y = x := by dsimp [y]; abel
  have hTube := section9_tube_union_mem_coarseTube (by omega : 0 < t) (vecSite ℓ.site) y (dirOf ℓ)
  change y ∈ section9FiniteTube (dirOf ℓ) t (-(5 : ℝ) / 8) (3 / 8) ∪
      section9FiniteTube (dirOf ℓ) t (-(3 : ℝ) / 8) (5 / 8) ↔
    c + y ∈ coarseTubeVertices (2 * (t : ℝ)) (vecSite ℓ.site) (dirOf ℓ) at hTube
  have hleft := mem_translateSites c (section9FiniteTube (dirOf ℓ) t (-(5 : ℝ) / 8) (3 / 8)) y
  have hright := mem_translateSites c (section9FiniteTube (dirOf ℓ) t (-(3 : ℝ) / 8) (5 / 8)) y
  rw [hxy] at hTube hleft hright
  change (x ∈ translateSites c (section9FiniteTube (dirOf ℓ) t (-(5 : ℝ) / 8) (3 / 8)) ∨
    x ∈ translateSites c (section9FiniteTube (dirOf ℓ) t (-(3 : ℝ) / 8) (5 / 8))) ↔ _
  exact (or_congr hleft hright).trans (by simpa only [Finset.mem_union] using hTube)

/-- A successful layout step with the stated side regions has a short
offspring bridge confined to its physical tube and avoiding both reveals. -/
theorem actual_layout_offspring_bridge_in_coarseTube {D : ℕ} {ι : Type*}
    {ω : Configuration (D + 1)} {U : Set (Vertex (D + 1))} {B : ℝ}
    (typ : TypicalParameters) (t : ℕ) (ht : 9 ≤ t) (k : ℕ) (hk : 0 < k)
    (MOff Mcoal Kdiam M : ℕ) {ℓ : RouteLabel D} (hℓ : HasTube M ℓ)
    (step : NestSprinklingStep (D + 1) ι ω U B)
    (hL : step.leftRegion = ((actualLayout D typ t ht k hk MOff Mcoal Kdiam M).L ℓ :
      Set (Vertex (D + 1))))
    (hR : step.rightRegion = ((actualLayout D typ t ht k hk MOff Mcoal Kdiam M).R ℓ :
      Set (Vertex (D + 1))))
    {c : ι} (hc : c ∈ step.offspring) :
    ∃ x ∈ step.sourceBoundary, ∃ y ∈ step.targetBoundary c, ∃ a b,
      (a, b) ∈ step.pivots ∧
      BoundedIntrinsicConnection (sprinklingBridgeGraph step.leftGraph step.rightGraph a b) x y B ∧
      sprinklingBridgeGraph step.leftGraph step.rightGraph a b ≤
        microscopicPieceGraph ω (coarseTubeVertices (2 * (t : ℝ)) (vecSite ℓ.site) (dirOf ℓ))
          (exploredEdgeSet step.firstCube step.firstRevealed ∪
            exploredEdgeSet step.lastCube step.lastRevealed)ᶜ := by
  obtain ⟨x, hx, y, hy, a, b, hab, hbound, hgraph⟩ := step.bridge_in_side_union hc
  refine ⟨x, hx, y, hy, a, b, hab, hbound, ?_⟩
  rw [hL, hR, actual_layout_side_union_eq_coarseTube typ t ht k hk MOff Mcoal Kdiam M hℓ]
    at hgraph
  exact hgraph

end NearCritical.Section10
