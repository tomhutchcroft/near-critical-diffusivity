module

public import NearCritical.Section9CoalescenceWitness
public import NearCritical.HalfSpaceArmGeometry

@[expose] public section
namespace NearCritical

/-- A deleted-edge component connection has an ordinary open-bond witness
whose bond bases all belong to the original component. -/
theorem sprinklingComponent_connection_certificate {d : ℕ}
    (ω : Configuration d) (T Q F : Finset (Vertex d)) {x y : Vertex d}
    (hx : x ∈ T) (hxy : (sprinklingUnexploredGraph ω T Q F).Reachable x y) :
    ∃ S : Finset (Bond d), (∀ e ∈ S, ω e = true) ∧
      (∀ e ∈ S, e.1 ∈ sprinklingUnexploredCluster ω T Q F x) ∧
      ∀ θ : Configuration d, (∀ e ∈ S, θ e = true) →
        connectionToSetEvent (T : Set (Vertex d)) x ({y} : Set (Vertex d)) θ := by
  obtain ⟨w⟩ := hxy
  let v := w.mapLe (microscopicPieceGraph_le ω _ _)
  have hv : v.support = w.support := SimpleGraph.Walk.support_mapLe_eq_support _ _
  have hT : ∀ z ∈ v.support, z ∈ (T : Set (Vertex d)) := by
    intro z hz
    exact microscopicWalk_support w hx z (hv ▸ hz)
  obtain ⟨S, hOpen, hEdge, hForce⟩ := openWalk_certificate v (T : Set (Vertex d)) hT
  refine ⟨S, hOpen, ?_, hForce⟩
  intro e he
  have hz := v.fst_mem_support_of_mem_edges (hEdge e he)
  exact (mem_sprinklingUnexploredCluster ω T Q F x e.1).mpr
    ⟨hT e.1 hz, (w.takeUntil e.1 (hv ▸ hz)).reachable⟩

/-- Two certificates supported on vertex-disjoint components use disjoint bonds. -/
theorem disjoint_bond_certificates_of_disjoint_bases {d : ℕ}
    {A B : Finset (Vertex d)} {S U : Finset (Bond d)}
    (hAB : Disjoint A B)
    (hS : ∀ e ∈ S, e.1 ∈ A) (hU : ∀ e ∈ U, e.1 ∈ B) :
    Disjoint S U := by
  rw [Finset.disjoint_left] at hAB ⊢
  intro e heS heU
  exact hAB (hS e heS) (hU e heU)

end NearCritical
