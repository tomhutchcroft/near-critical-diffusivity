module

public import NearCritical.Section9RevealSupport
public import NearCritical.SpanningBoundaryDiameter

/-! Intrinsic metric locality on the actual incident-heart reveal mask.
Graphs outside the revealed components may differ. The entire cube graph
is never asserted to be determined by the revealed heart union. -/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open scoped Classical

theorem clusterRevealBonds_mono_vertices {d : ℕ} (Q C F : Finset (Vertex d))
    (hCF : C ⊆ F) : clusterRevealBonds Q C ⊆ clusterRevealBonds Q F := by
  intro e he
  obtain ⟨hb, ht, hc | hc⟩ := (mem_clusterRevealBonds Q C e).mp he
  · exact (mem_clusterRevealBonds Q F e).mpr ⟨hb, ht, Or.inl (hCF hc)⟩
  · exact (mem_clusterRevealBonds Q F e).mpr ⟨hb, ht, Or.inr (hCF hc)⟩

/-- Preserve EACH heart-root component, not just their vertex union. -/
theorem heartRootCluster_eq_of_union_reveal_agree {d : ℕ}
    (Q H F : Finset (Vertex d)) (hH : H ⊆ Q) (ω η : Configuration d)
    (hF : heartClusterUnion ω Q H = F)
    (hagree : ∀ e ∈ clusterRevealBonds Q F, ω e = η e)
    {root : Vertex d} (hroot : root ∈ H) :
    finiteBoxCluster η Q root = finiteBoxCluster ω Q root := by
  have hCF : finiteBoxCluster ω Q root ⊆ F := by
    rw [← hF]
    exact cluster_subset_heartClusterUnion ω Q H hroot
  apply finiteBoxCluster_eq_of_reveal_agree Q (finiteBoxCluster ω Q root)
    root (hH hroot) rfl
  intro e he
  exact hagree e (clusterRevealBonds_mono_vertices Q _ F hCF he)

/-- All internal edges of a revealed component are known even though
unexplored edges of Q outside F are not known. -/
theorem componentGraph_eq_of_union_reveal_agree {d : ℕ}
    (Q C F : Finset (Vertex d)) (hCQ : C ⊆ Q) (hCF : C ⊆ F)
    (ω η : Configuration d)
    (hagree : ∀ e ∈ clusterRevealBonds Q F, ω e = η e) :
    restrictedGraph ω (C : Set (Vertex d)) = restrictedGraph η (C : Set (Vertex d)) := by
  apply restrictedGraph_eq_of_internalBondSet_agree C (C : Set (Vertex d))
    (by intro x hx; exact hx) ω η
  intro e he
  obtain ⟨hb, ht⟩ := (mem_internalBondSet C e).mp he
  exact hagree e ((mem_clusterRevealBonds Q F e).mpr
    ⟨hCQ hb, hCQ ht, Or.inl (hCF hb)⟩)

/-- Cube-restricted distances between vertices of the SAME actual component
agree under changes outside the incident mask. No global metric equality. -/
theorem componentDistances_eq_of_union_reveal_agree {d : ℕ}
    (Q C F : Finset (Vertex d)) (root : Vertex d) (hroot : root ∈ Q)
    (ω η : Configuration d) (hC : finiteBoxCluster ω Q root = C) (hCF : C ⊆ F)
    (hagree : ∀ e ∈ clusterRevealBonds Q F, ω e = η e)
    {x y : Vertex d} (hx : x ∈ C) (hy : y ∈ C) :
    (restrictedGraph ω (Q : Set (Vertex d))).dist x y =
      (restrictedGraph η (Q : Set (Vertex d))).dist x y := by
  have hCQ : C ⊆ Q := by
    rw [← hC]
    exact finiteBoxCluster_subset ω Q root
  have hCη : finiteBoxCluster η Q root = C := by
    apply finiteBoxCluster_eq_of_reveal_agree Q C root hroot hC
    intro e he
    exact hagree e (clusterRevealBonds_mono_vertices Q C F hCF he)
  have hg := componentGraph_eq_of_union_reveal_agree Q C F hCQ hCF ω η hagree
  have hw := finiteBoxCluster_dist_eq ω Q root (hC.symm ▸ hx) (hC.symm ▸ hy)
  have he := finiteBoxCluster_dist_eq η Q root (hCη.symm ▸ hx) (hCη.symm ▸ hy)
  rw [hC] at hw
  rw [hCη] at he
  exact hw.symm.trans ((congrArg (fun G : SimpleGraph (Vertex d) => G.dist x y) hg).trans he)

/-- The literal distinct-labelled-face rin is incident-mask local on an
actual revealed component. Empty face intersections are allowed. -/
theorem spanningFaceDiameter_eq_of_union_reveal_agree {d : ℕ} {ι : Type*}
    [Fintype ι] [DecidableEq ι] (Q C F : Finset (Vertex d))
    (faces : ι → Finset (Vertex d)) (root : Vertex d) (hroot : root ∈ Q)
    (ω η : Configuration d) (hC : finiteBoxCluster ω Q root = C) (hCF : C ⊆ F)
    (hagree : ∀ e ∈ clusterRevealBonds Q F, ω e = η e) :
    spanningFaceDiameter (restrictedGraph ω (Q : Set (Vertex d))) C faces =
      spanningFaceDiameter (restrictedGraph η (Q : Set (Vertex d))) C faces := by
  unfold spanningFaceDiameter
  apply Finset.sup_congr rfl
  intro pair _
  apply Finset.sup_congr rfl
  intro xy hxy
  obtain ⟨hx, hy⟩ := Finset.mem_product.mp hxy
  exact componentDistances_eq_of_union_reveal_agree Q C F root hroot ω η hC hCF hagree
    (Finset.mem_inter.mp hx).1 (Finset.mem_inter.mp hy).1

end NearCritical.Section10
