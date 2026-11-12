module

public import NearCritical.Section10ActualBridgeEvents
public import NearCritical.Section10SpreadBridgeEntry

/-! The full-nest bridge mark on an actual lattice label, with the heart
reveal frozen so the mark only reads the fresh tube block. -/

@[expose] public section
noncomputable section

namespace NearCritical.Section10.NestLayout

open scoped Classical

variable {D d : ℕ} (Λ : NestLayout D d)

/-- The union of the bridges from all representatives in the incoming nest,
in the independent sprinkle representation. -/
def firstGoodNestBridge (G : Λ.Φ) (ℓ : RouteLabel D)
    (N : Finset (Finset (Vertex d))) (a : Bool)
    (z : Configuration d × Configuration d) : Finset (Vertex d) :=
  section9SprinklingCluster z.1 z.2 (orientedLatticePairs (Λ.Mid ℓ))
    (Λ.L ℓ) (Λ.R ℓ) (Λ.Q ℓ.site) (Λ.Fat G.1 ℓ.site)
    (Λ.Q ℓ.target) (Λ.Fat G.1 ℓ.target)
    (sprinklingTargetBoundary N (Λ.src G ℓ a))
    (sprinklingTargetBoundary (Λ.fam G ℓ.target) (Λ.tgt G ℓ))

theorem firstGoodNestBridge_readsOnly (G : Λ.Φ) (ℓ : RouteLabel D)
    (N : Finset (Finset (Vertex d))) (a : Bool) :
    ReadsOnly (Λ.S₀ G.1 ∪ Λ.Bl₀ G.1 ℓ) (Λ.firstGoodNestBridge G ℓ N a) := by
  refine (rawBridge_readsOnly _ _ _ _ _ _ _ _ _).mono ?_
  intro e he
  by_cases h : e ∈ Λ.S₀ G.1
  · exact Finset.mem_union_left _ h
  · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨Finset.mem_union_left _ he,h⟩)

/-- For a fixed reveal, evaluate the two bridge sets from the fresh tube
bits and the already explored bonds of the two cubes. -/
def firstGoodSharedTubeMark (G : Λ.Φ) (ℓ : RouteLabel D)
    (N N' : Finset (Finset (Vertex d))) (a b : Bool)
    (z : Configuration d × Configuration d) : Prop :=
  let w := gluePair G.2 ((Λ.Bl₀ G.1 ℓ).restrict (layerVal z))
  (Λ.firstGoodNestBridge G ℓ N a w ∩ Λ.firstGoodNestBridge G ℓ N' b w).Nonempty

theorem firstGoodSharedTubeMark_readsOnly (G : Λ.Φ) (ℓ : RouteLabel D)
    (N N' : Finset (Finset (Vertex d))) (a b : Bool) :
    ReadsOnly (Λ.Bl₀ G.1 ℓ) (Λ.firstGoodSharedTubeMark G ℓ N N' a b) := by
  intro z z' h
  have hbits : (Λ.Bl₀ G.1 ℓ).restrict (layerVal z) =
      (Λ.Bl₀ G.1 ℓ).restrict (layerVal z') :=
    funext fun e => h e e.2
  unfold firstGoodSharedTubeMark
  rw [hbits]

theorem firstGoodSharedTubeMark_iff_or_bridge
    (ℓ : RouteLabel D) (N N' : Finset (Finset (Vertex d))) (a b : Bool)
    (z : Configuration d × Configuration d)
    (hL : Λ.Mid ℓ ⊆ Λ.L ℓ)
    (hQ : Disjoint (Λ.Mid ℓ : Set (Vertex d)) (Λ.Q ℓ.site : Set (Vertex d))) :
    let G := refineReveal Λ.ρ₀ Λ.S₀ z
    let C (P : Finset (Finset (Vertex d))) (sign : Bool) :=
      section9SprinklingCluster z.1 (sprinkleOrConfiguration z.1 z.2)
        (orientedLatticePairs (Λ.Mid ℓ)) (Λ.L ℓ) (Λ.R ℓ)
        (Λ.Q ℓ.site) (Λ.Fat G.1 ℓ.site) (Λ.Q ℓ.target) (Λ.Fat G.1 ℓ.target)
        (sprinklingTargetBoundary P (Λ.src G ℓ sign))
        (sprinklingTargetBoundary (Λ.fam G ℓ.target) (Λ.tgt G ℓ))
    Λ.firstGoodSharedTubeMark G ℓ N N' a b z ↔ (C N a ∩ C N' b).Nonempty := by
  intro G C
  have hglue (P : Finset (Finset (Vertex d))) (sign : Bool) :
      Λ.firstGoodNestBridge G ℓ P sign (gluePair G.2 ((Λ.Bl₀ G.1 ℓ).restrict (layerVal z))) =
        Λ.firstGoodNestBridge G ℓ P sign z :=
    glue_fun_eq _ (Λ.firstGoodNestBridge_readsOnly G ℓ P sign) z
  have hor (P : Finset (Finset (Vertex d))) (sign : Bool) :
      C P sign = Λ.firstGoodNestBridge G ℓ P sign z :=
    middle_sprinklingCluster_or_eq z.1 z.2 _ _ _ _ _ _ _ _ _ hL hQ
  dsimp only [firstGoodSharedTubeMark]
  rw [hglue N a, hglue N' b, hor N a, hor N' b]

end NearCritical.Section10.NestLayout
