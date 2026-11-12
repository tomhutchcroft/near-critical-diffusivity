module

public import NearCritical.ClusterResampling

/-! Deterministic collision comparison for prop.num_spanning_new Step 2.
The entire induced cluster graph, not only its vertex set, is preserved. -/
@[expose] public section
noncomputable section
namespace NearCritical
open scoped Classical

/-- Actual replacement retains every bond whose endpoints avoid the revealed component. -/
lemma clusterResample_bond_away {d : ℕ} (U : Finset (Vertex d))
    (root : Vertex d) (ω ζ : Configuration d) (e : Bond d)
    (hb : e.1 ∉ finiteBoxCluster ω U root)
    (ht : bondTip e ∉ finiteBoxCluster ω U root) :
    clusterResample U root ω ζ e = ω e := by
  have hn : e ∉ clusterRevealBonds U (finiteBoxCluster ω U root) := by
    simp [mem_clusterRevealBonds, hb, ht]
  simp [clusterResample, resampleBonds, extendConfiguration, hn]

/-- Internal open graphs of sets avoiding the revealed component agree exactly. -/
theorem clusterResample_graph_away {d : ℕ} (U A : Finset (Vertex d))
    (root : Vertex d) (ω ζ : Configuration d)
    (ha : Disjoint A (finiteBoxCluster ω U root)) :
    restrictedGraph (clusterResample U root ω ζ) (A : Set (Vertex d)) =
      restrictedGraph ω (A : Set (Vertex d)) := by
  have hbits : ∀ e : Bond d, e.1 ∈ A → bondTip e ∈ A →
      clusterResample U root ω ζ e = ω e := by
    intro e hb ht
    exact clusterResample_bond_away U root ω ζ e
      (fun h => Finset.disjoint_left.mp ha hb h)
      (fun h => Finset.disjoint_left.mp ha ht h)
  have hle : ∀ α β : Configuration d,
      (∀ e : Bond d, e.1 ∈ A → bondTip e ∈ A → α e = β e) →
      restrictedGraph α (A : Set (Vertex d)) ≤ restrictedGraph β (A : Set (Vertex d)) := by
    intro α β he x y hxy
    obtain ⟨⟨e, hopen, hends | hends⟩, hx, hy⟩ := hxy
    · obtain ⟨rfl, rfl⟩ := hends
      exact ⟨⟨e, (he e hx hy).symm.trans hopen, Or.inl ⟨rfl,rfl⟩⟩, hx, hy⟩
    · obtain ⟨rfl, rfl⟩ := hends
      exact ⟨⟨e, (he e hy hx).symm.trans hopen, Or.inr ⟨rfl,rfl⟩⟩, hx, hy⟩
  exact le_antisymm (hle _ _ hbits) (hle _ _ (fun e hb ht => (hbits e hb ht).symm))

/-- Distinct rooted components cannot meet. The root exclusion is actual
nonconnection, not a disjointness assumption about the full second component. -/
lemma finiteBoxCluster_disjoint_of_root_not_mem {d : ℕ} (ω : Configuration d)
    (U : Finset (Vertex d)) (r s : Vertex d) (hs : s ∈ U)
    (hn : s ∉ finiteBoxCluster ω U r) :
    Disjoint (finiteBoxCluster ω U s) (finiteBoxCluster ω U r) := by
  apply Finset.disjoint_left.mpr
  intro x hxS hxR
  have hrs := ((mem_finiteBoxCluster ω U r x).mp hxR).2.trans
    (((mem_finiteBoxCluster ω U s x).mp hxS).2.symm)
  exact hn ((mem_finiteBoxCluster ω U r s).mpr ⟨hs, hrs⟩)

private lemma component_subset_of_induced_eq {d : ℕ} (ω η : Configuration d)
    (U : Finset (Vertex d)) (root : Vertex d) (hr : root ∈ U)
    (hg : restrictedGraph ω (finiteBoxCluster ω U root : Set (Vertex d)) =
      restrictedGraph η (finiteBoxCluster ω U root : Set (Vertex d))) :
    finiteBoxCluster ω U root ⊆ finiteBoxCluster η U root := by
  intro x hx
  have hreach := finiteBoxCluster_induced_reachable ω U root
    (root_mem_finiteBoxCluster ω U hr) hx
  rw [hg] at hreach
  exact (mem_finiteBoxCluster η U root x).mpr
    ⟨finiteBoxCluster_subset ω U root hx, hreach.mono
      (restrictedGraph_mono η (show (finiteBoxCluster ω U root : Set (Vertex d)) ⊆
        (U : Set (Vertex d)) from finiteBoxCluster_subset ω U root))⟩

/-- Unless the new component collides with the revealed component, the original
and replacement components of a second root are exactly equal. -/
theorem clusterResample_component_eq_of_no_collision {d : ℕ}
    (U : Finset (Vertex d)) (r s : Vertex d) (hs : s ∈ U)
    (ω ζ : Configuration d) (hn : s ∉ finiteBoxCluster ω U r)
    (hc : Disjoint (finiteBoxCluster (clusterResample U r ω ζ) U s)
      (finiteBoxCluster ω U r)) :
    finiteBoxCluster (clusterResample U r ω ζ) U s = finiteBoxCluster ω U s := by
  have hd := finiteBoxCluster_disjoint_of_root_not_mem ω U r s hs hn
  apply Finset.Subset.antisymm
  · exact component_subset_of_induced_eq _ _ U s hs
      (clusterResample_graph_away U _ r ω ζ hc)
  · exact component_subset_of_induced_eq _ _ U s hs
      (clusterResample_graph_away U _ r ω ζ hd).symm

/-- Nonmonotone intrinsic-graph properties are preserved too, because every
internal bond of the unchanged second component retains its original value. -/
theorem clusterResample_property_of_no_collision {d : ℕ}
    (U : Finset (Vertex d)) (r s : Vertex d) (hs : s ∈ U)
    (ω ζ : Configuration d) (hn : s ∉ finiteBoxCluster ω U r)
    (hc : Disjoint (finiteBoxCluster (clusterResample U r ω ζ) U s)
      (finiteBoxCluster ω U r))
    (P : SimpleGraph (Vertex d) → Finset (Vertex d) → Prop) :
    P (restrictedGraph (clusterResample U r ω ζ)
      (finiteBoxCluster (clusterResample U r ω ζ) U s : Set (Vertex d)))
      (finiteBoxCluster (clusterResample U r ω ζ) U s) ↔
    P (restrictedGraph ω (finiteBoxCluster ω U s : Set (Vertex d)))
      (finiteBoxCluster ω U s) := by
  rw [clusterResample_component_eq_of_no_collision U r s hs ω ζ hn hc,
    clusterResample_graph_away U _ r ω ζ
      (finiteBoxCluster_disjoint_of_root_not_mem ω U r s hs hn)]

/-- Actual rooted cluster predicate, including its full induced open graph. -/
def rootedClusterProperty {d : ℕ} (U : Finset (Vertex d)) (root : Vertex d)
    (P : SimpleGraph (Vertex d) → Finset (Vertex d) → Prop) (ω : Configuration d) : Prop :=
  P (restrictedGraph ω (finiteBoxCluster ω U root : Set (Vertex d)))
    (finiteBoxCluster ω U root)

/-- Literal deterministic source comparison: property and nonconnection are
bounded by the replacement property plus a replacement collision. -/
theorem clusterResample_indicator_le {d : ℕ}
    (U : Finset (Vertex d)) (r s : Vertex d) (hs : s ∈ U)
    (ω ζ : Configuration d)
    (P : SimpleGraph (Vertex d) → Finset (Vertex d) → Prop) :
    (if rootedClusterProperty U s P ω ∧ s ∉ finiteBoxCluster ω U r then (1:ℝ) else 0) ≤
      (if rootedClusterProperty U s P (clusterResample U r ω ζ) then (1:ℝ) else 0) +
      (if ¬Disjoint (finiteBoxCluster (clusterResample U r ω ζ) U s)
        (finiteBoxCluster ω U r) then (1:ℝ) else 0) := by
  by_cases hn : s ∉ finiteBoxCluster ω U r
  · by_cases hc : Disjoint (finiteBoxCluster (clusterResample U r ω ζ) U s)
        (finiteBoxCluster ω U r)
    · have hp := clusterResample_property_of_no_collision U r s hs ω ζ hn hc P
      change rootedClusterProperty U s P (clusterResample U r ω ζ) ↔
        rootedClusterProperty U s P ω at hp
      by_cases hw : rootedClusterProperty U s P ω
      · have hr := hp.mpr hw
        simp [hn, hc, hw, hr]
      · have hr : ¬rootedClusterProperty U s P (clusterResample U r ω ζ) :=
          fun h => hw (hp.mp h)
        simp [hn, hc, hw, hr]
    · by_cases hw : rootedClusterProperty U s P ω <;>
        by_cases hr : rootedClusterProperty U s P (clusterResample U r ω ζ) <;>
        simp [hn, hc, hw, hr]
  · by_cases hc : Disjoint (finiteBoxCluster (clusterResample U r ω ζ) U s)
        (finiteBoxCluster ω U r) <;>
      by_cases hr : rootedClusterProperty U s P (clusterResample U r ω ζ) <;>
      simp [hn, hc, hr]

/-- The collision error is exactly a union of genuine restricted connection
events from the second root to vertices of the first component. -/
theorem clusterResample_collision_iff {d : ℕ}
    (U : Finset (Vertex d)) (r s : Vertex d) (ω ζ : Configuration d) :
    ¬Disjoint (finiteBoxCluster (clusterResample U r ω ζ) U s)
      (finiteBoxCluster ω U r) ↔
    ∃ u ∈ finiteBoxCluster ω U r,
      (restrictedGraph (clusterResample U r ω ζ) (U : Set (Vertex d))).Reachable s u := by
  rw [Finset.not_disjoint_iff]
  constructor
  · rintro ⟨u, hu, hk⟩
    exact ⟨u, hk, ((mem_finiteBoxCluster _ U s u).mp hu).2⟩
  · rintro ⟨u, hk, hu⟩
    exact ⟨u, (mem_finiteBoxCluster _ U s u).mpr
      ⟨finiteBoxCluster_subset ω U r hk, hu⟩, hk⟩

end NearCritical
