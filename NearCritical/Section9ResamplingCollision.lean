module

public import NearCritical.Section9Pivotal

@[expose] public section
noncomputable section
namespace NearCritical
open scoped Classical

private theorem reachable_of_component_edge_transport {V : Type*}
    (G H : SimpleGraph V) (root : V)
    (hedge : ∀ a b, G.Reachable root a → G.Adj a b → H.Adj a b)
    {z : V} (hz : G.Reachable root z) : H.Reachable root z := by
  obtain ⟨w⟩ := hz
  have hwalk : ∀ {a b : V} (w : G.Walk a b), G.Reachable root a → H.Reachable a b := by
    intro a b w
    induction w with
    | nil => intro _; exact .refl _
    | @cons a b c hab w ih =>
      intro ha
      exact (hedge a b ha hab).reachable.trans (ih (ha.trans hab.reachable))
  exact hwalk w (.refl root)

/-- Agreement of edges away from a revealed vertex set preserves a tube
cluster whenever both the original and replacement clusters avoid that set. -/
theorem sprinkling_cluster_eq_of_no_resampling_collision {d : ℕ}
    (ω η : Configuration d) (T Q F C : Finset (Vertex d)) (root : Vertex d)
    (hlocal : ∀ a b, a ∉ C → b ∉ C →
      ((sprinklingUnexploredGraph ω T Q F).Adj a b ↔
        (sprinklingUnexploredGraph η T Q F).Adj a b))
    (hω : Disjoint (sprinklingUnexploredCluster ω T Q F root) C)
    (hη : Disjoint (sprinklingUnexploredCluster η T Q F root) C) :
    sprinklingUnexploredCluster ω T Q F root =
      sprinklingUnexploredCluster η T Q F root := by
  have htransfer (ξ ζ : Configuration d)
      (hx : Disjoint (sprinklingUnexploredCluster ξ T Q F root) C)
      (he : ∀ a b, a ∉ C → b ∉ C →
        (sprinklingUnexploredGraph ξ T Q F).Adj a b →
          (sprinklingUnexploredGraph ζ T Q F).Adj a b) :
      sprinklingUnexploredCluster ξ T Q F root ⊆
        sprinklingUnexploredCluster ζ T Q F root := by
    intro z hz
    obtain ⟨hzT, hzreach⟩ := (mem_sprinklingUnexploredCluster ξ T Q F root z).mp hz
    refine (mem_sprinklingUnexploredCluster ζ T Q F root z).mpr ⟨hzT, ?_⟩
    apply reachable_of_component_edge_transport _ _ root ?_ hzreach
    intro a b ha hab
    have haT : a ∈ T := hab.2.1
    have hbT : b ∈ T := hab.2.2.1
    have haC := Finset.disjoint_left.mp hx
      ((mem_sprinklingUnexploredCluster ξ T Q F root a).mpr ⟨haT, ha⟩)
    have hbC := Finset.disjoint_left.mp hx
      ((mem_sprinklingUnexploredCluster ξ T Q F root b).mpr ⟨hbT, ha.trans hab.reachable⟩)
    exact he a b haC hbC hab
  exact Finset.Subset.antisymm
    (htransfer ω η hω (fun a b ha hb => (hlocal a b ha hb).mp))
    (htransfer η ω hη (fun a b ha hb => (hlocal a b ha hb).mpr))

end NearCritical
