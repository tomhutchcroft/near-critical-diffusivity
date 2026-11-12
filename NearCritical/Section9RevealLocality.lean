module

public import NearCritical.Section9TwoClusterReveal

@[expose] public section
noncomputable section
namespace NearCritical
open scoped Classical

/-- A deleted-tube cluster is determined by its open interior and examined
closed boundary bonds. -/
theorem sprinkling_cluster_eq_of_reveal_agree {d : ℕ}
    (T Q F : Finset (Vertex d)) (root : Vertex d)
    (ω η : Configuration d)
    (hagree : ∀ e ∈ sprinklingClusterRevealBonds ω T Q F root, ω e = η e) :
    sprinklingUnexploredCluster ω T Q F root =
      sprinklingUnexploredCluster η T Q F root := by
  let G := sprinklingUnexploredGraph ω T Q F
  let H := sprinklingUnexploredGraph η T Q F
  have htransport (ξ ζ : Configuration d)
      (hbits : ∀ e ∈ sprinklingClusterRevealBonds ω T Q F root, ξ e = ζ e)
      (a b : Vertex d) (ha : G.Reachable root a)
      (hab : (sprinklingUnexploredGraph ξ T Q F).Adj a b) :
      (sprinklingUnexploredGraph ζ T Q F).Adj a b := by
    obtain ⟨⟨e, he, hends⟩, hx, hy, hnot⟩ := hab
    have heT : e ∈ internalBondSet T := by
      apply (mem_internalBondSet T e).mpr
      rcases hends with ⟨hxb, hyt⟩ | ⟨hyb, hxt⟩
      · exact ⟨hxb ▸ hx, hyt ▸ hy⟩
      · exact ⟨hyb ▸ hy, hxt ▸ hx⟩
    have hen : e ∉ clusterRevealBonds Q F := by
      intro hex
      have hp := (mem_clusterRevealBonds Q F e).mp hex
      have hh : s(e.1, bondTip e) ∈ exploredEdgeSet (Q : Set (Vertex d)) (F : Set (Vertex d)) :=
        (pair_mem_exploredEdgeSet _ _ _ _).mpr hp
      apply hnot
      rcases hends with ⟨hxb, hyt⟩ | ⟨hyb, hxt⟩
      · simpa only [hxb, hyt] using hh
      · simpa only [hyb, hxt, Sym2.eq_swap] using hh
    have haC : a ∈ sprinklingUnexploredCluster ω T Q F root :=
      (mem_sprinklingUnexploredCluster ω T Q F root a).mpr ⟨hx, ha⟩
    have heM : e ∈ sprinklingClusterRevealBonds ω T Q F root := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_sdiff.mpr ⟨heT, hen⟩, ?_⟩
      rcases hends with ⟨hxb, hyt⟩ | ⟨hyb, hxt⟩
      · exact Or.inl (hxb ▸ haC)
      · exact Or.inr (hxt ▸ haC)
    exact ⟨⟨e, (hbits e heM).symm.trans he, hends⟩, hx, hy, hnot⟩
  have hforward : ∀ {a b} (w : G.Walk a b), G.Reachable root a → H.Reachable a b := by
    intro a b w
    induction w with
    | nil => intro _; exact .refl _
    | @cons a b c hab w ih =>
      intro ha
      exact (htransport ω η hagree a b ha hab).reachable.trans
        (ih (ha.trans hab.reachable))
  have hbackward : ∀ {a b} (w : H.Walk a b), G.Reachable root a → G.Reachable root b := by
    intro a b w
    induction w with
    | nil => intro ha; exact ha
    | @cons a b c hab w ih =>
      intro ha
      exact ih (ha.trans
        (htransport η ω (fun e he => (hagree e he).symm) a b ha hab).reachable)
  apply Finset.Subset.antisymm
  · intro z hz
    obtain ⟨hzT, ⟨w⟩⟩ := (mem_sprinklingUnexploredCluster ω T Q F root z).mp hz
    exact (mem_sprinklingUnexploredCluster η T Q F root z).mpr
      ⟨hzT, hforward w (.refl root)⟩
  · intro z hz
    obtain ⟨hzT, ⟨w⟩⟩ := (mem_sprinklingUnexploredCluster η T Q F root z).mp hz
    exact (mem_sprinklingUnexploredCluster ω T Q F root z).mpr
      ⟨hzT, hbackward w (.refl root)⟩

end NearCritical
