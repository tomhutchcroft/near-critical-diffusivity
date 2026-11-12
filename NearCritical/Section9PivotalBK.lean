module

public import NearCritical.Section9Pivotal
public import NearCritical.HalfSpaceArmGeometry

/-! The canonical pivot implies disjoint ordinary connection arms; BK is
applied to those increasing arms, never to the nonmonotone pivot event. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory Set
open scoped Classical

private lemma unexploredWalk_mem_cluster {d : ℕ} {ω : Configuration d}
    (T Q F : Finset (Vertex d)) {root target : Vertex d}
    (w : (sprinklingUnexploredGraph ω T Q F).Walk root target) (hr : root ∈ T)
    (z : Vertex d) (hz : z ∈ w.support) :
    z ∈ sprinklingUnexploredCluster ω T Q F root := by
  apply (mem_sprinklingUnexploredCluster ω T Q F root z).mpr
  exact ⟨microscopicWalk_support w hr z hz, (w.takeUntil z hz).reachable⟩

/-- Disjoint full side components yield disjoint finite bond certificates for
ordinary tube arms. The two tube domains need not themselves be disjoint. -/
theorem sprinklingPivotalPair_disjointOccurrence {d : ℕ} {ω : Configuration d}
    (L R Q₁ F₁ Q₃ F₃ A B : Finset (Vertex d)) (e : Vertex d × Vertex d)
    (he : sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ A B e) :
    DisjointOccurrence (connectionToSetEvent (L : Set (Vertex d)) e.1 (A : Set (Vertex d)))
      (connectionToSetEvent (R : Set (Vertex d)) e.2 (B : Set (Vertex d))) ω := by
  obtain ⟨_, ha, hb, hA, hB, hdis⟩ := he
  obtain ⟨x, hx⟩ := hA
  obtain ⟨hxC, hxA⟩ := Finset.mem_inter.mp hx
  obtain ⟨y, hy⟩ := hB
  obtain ⟨hyC, hyB⟩ := Finset.mem_inter.mp hy
  obtain ⟨p⟩ := ((mem_sprinklingUnexploredCluster ω L Q₁ F₁ e.1 x).mp hxC).2
  obtain ⟨q⟩ := ((mem_sprinklingUnexploredCluster ω R Q₃ F₃ e.2 y).mp hyC).2
  let p' : (openGraph ω).Walk e.1 x := p.mapLe (microscopicPieceGraph_le ω _ _)
  let q' : (openGraph ω).Walk e.2 y := q.mapLe (microscopicPieceGraph_le ω _ _)
  have hpSupport : p'.support = p.support := SimpleGraph.Walk.support_mapLe_eq_support _ _
  have hqSupport : q'.support = q.support := SimpleGraph.Walk.support_mapLe_eq_support _ _
  have hpL : ∀ z ∈ p'.support, z ∈ (L : Set (Vertex d)) := by
    intro z hz
    exact microscopicWalk_support p ha z
      (hpSupport ▸ hz)
  have hqR : ∀ z ∈ q'.support, z ∈ (R : Set (Vertex d)) := by
    intro z hz
    exact microscopicWalk_support q hb z
      (hqSupport ▸ hz)
  obtain ⟨F, hopenF, hedgeF, hforceF⟩ := openWalk_certificate p' (L : Set (Vertex d)) hpL
  obtain ⟨G, hopenG, hedgeG, hforceG⟩ := openWalk_certificate q' (R : Set (Vertex d)) hqR
  refine ⟨F, G, F.finite_toSet, G.finite_toSet, ?_, ?_, ?_⟩
  · apply Set.disjoint_left.mpr
    intro f hfF hfG
    have hpz := p'.fst_mem_support_of_mem_edges (hedgeF f hfF)
    have hqz := q'.fst_mem_support_of_mem_edges (hedgeG f hfG)
    have hcL := unexploredWalk_mem_cluster L Q₁ F₁ p ha f.1
      (hpSupport ▸ hpz)
    have hcR := unexploredWalk_mem_cluster R Q₃ F₃ q hb f.1
      (hqSupport ▸ hqz)
    exact Finset.disjoint_left.mp hdis hcL hcR
  · intro θ hagree
    apply connectionToSetEvent_mono (Set.Subset.refl _)
      (Set.singleton_subset_iff.mpr hxA) e.1
    exact hforceF θ (fun f hf => (hagree f hf).trans (hopenF f hf))
  · intro θ hagree
    apply connectionToSetEvent_mono (Set.Subset.refl _)
      (Set.singleton_subset_iff.mpr hyB) e.2
    exact hforceG θ (fun f hf => (hagree f hf).trans (hopenG f hf))

/-- Fixed-deletion pivot probability is bounded by the product of ordinary
connection-arm probabilities, under the actual Bernoulli measure. -/
theorem sprinklingPivotalPair_probability_le {d : ℕ} (p : unitInterval)
    (L R Q₁ F₁ Q₃ F₃ A B : Finset (Vertex d)) (e : Vertex d × Vertex d) :
    (percolation d p).real {ω | sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ A B e} ≤
      (percolation d p).real (connectionToSetEvent (L : Set (Vertex d)) e.1 (A : Set (Vertex d))) *
      (percolation d p).real (connectionToSetEvent (R : Set (Vertex d)) e.2 (B : Set (Vertex d))) := by
  exact (measureReal_mono (fun ω h =>
    sprinklingPivotalPair_disjointOccurrence L R Q₁ F₁ Q₃ F₃ A B e h)).trans
      (connectionToSet_bk p _ _ _ _ _ _)

end NearCritical
