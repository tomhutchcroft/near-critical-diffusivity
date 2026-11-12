module

public import NearCritical.Section9Pivotal
public import NearCritical.ClusterRevealSupport

/-! Finite coordinate support of the actual Section 9 deleted graphs and pivots. -/
@[expose] public section
noncomputable section
namespace NearCritical
open scoped Classical

/-- Exactly the internal tube bonds left after the explored-edge deletion. -/
def sprinklingAvailableBonds {d : ℕ} (T Q F : Finset (Vertex d)) : Finset (Bond d) :=
  internalBondSet T \ clusterRevealBonds Q F

theorem sprinklingUnexploredGraph_eq_of_available_agree {d : ℕ}
    (T Q F : Finset (Vertex d)) (ω η : Configuration d)
    (hagree : ∀ e ∈ sprinklingAvailableBonds T Q F, ω e = η e) :
    sprinklingUnexploredGraph ω T Q F = sprinklingUnexploredGraph η T Q F := by
  have hle : ∀ α β : Configuration d,
      (∀ e ∈ sprinklingAvailableBonds T Q F, α e = β e) →
      sprinklingUnexploredGraph α T Q F ≤ sprinklingUnexploredGraph β T Q F := by
    intro α β hab x y hxy
    obtain ⟨⟨e, he, hends⟩, hx, hy, hnot⟩ := hxy
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
    have heA : e ∈ sprinklingAvailableBonds T Q F := Finset.mem_sdiff.mpr ⟨heT, hen⟩
    exact ⟨⟨e, (hab e heA).symm.trans he, hends⟩, hx, hy, hnot⟩
  exact le_antisymm (hle ω η hagree) (hle η ω (fun e he => (hagree e he).symm))

theorem sprinklingUnexploredCluster_eq_of_available_agree {d : ℕ}
    (T Q F : Finset (Vertex d)) (ω η : Configuration d)
    (hagree : ∀ e ∈ sprinklingAvailableBonds T Q F, ω e = η e) (root : Vertex d) :
    sprinklingUnexploredCluster ω T Q F root = sprinklingUnexploredCluster η T Q F root := by
  unfold sprinklingUnexploredCluster
  rw [sprinklingUnexploredGraph_eq_of_available_agree T Q F ω η hagree]

/-- Full-cluster disjointness, not just the two connection arms, has finite
available-coordinate support. No increasingness of the pivot is asserted. -/
theorem sprinklingPivotalPair_iff_of_available_agree {d : ℕ}
    (L R Q₁ F₁ Q₃ F₃ A B : Finset (Vertex d)) (ω η : Configuration d)
    (hL : ∀ e ∈ sprinklingAvailableBonds L Q₁ F₁, ω e = η e)
    (hR : ∀ e ∈ sprinklingAvailableBonds R Q₃ F₃, ω e = η e)
    (e : Vertex d × Vertex d) :
    sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ A B e ↔
      sprinklingPivotalPair η L R Q₁ F₁ Q₃ F₃ A B e := by
  unfold sprinklingPivotalPair
  rw [sprinklingUnexploredCluster_eq_of_available_agree L Q₁ F₁ ω η hL,
    sprinklingUnexploredCluster_eq_of_available_agree R Q₃ F₃ ω η hR]

/-- Each tube avoids the opposite revealed cube, so both pivot-side available
blocks jointly avoid both explored masks. Same-side exclusion is by definition. -/
theorem sprinklingAvailableBonds_disjoint_reveals {d : ℕ}
    (L R Q₁ F₁ Q₃ F₃ : Finset (Vertex d))
    (hLQ₃ : Disjoint L Q₃) (hRQ₁ : Disjoint R Q₁) :
    Disjoint (clusterRevealBonds Q₁ F₁ ∪ clusterRevealBonds Q₃ F₃)
      (sprinklingAvailableBonds L Q₁ F₁ ∪ sprinklingAvailableBonds R Q₃ F₃) := by
  apply Finset.disjoint_left.mpr
  intro e he hf
  rcases Finset.mem_union.mp he with he₁ | he₃
  · rcases Finset.mem_union.mp hf with hfL | hfR
    · exact (Finset.mem_sdiff.mp hfL).2 he₁
    · have heR := (mem_internalBondSet R e).mp (Finset.mem_sdiff.mp hfR).1
      have heQ := (mem_clusterRevealBonds Q₁ F₁ e).mp he₁
      exact Finset.disjoint_left.mp hRQ₁ heR.1 heQ.1
  · rcases Finset.mem_union.mp hf with hfL | hfR
    · have heL := (mem_internalBondSet L e).mp (Finset.mem_sdiff.mp hfL).1
      have heQ := (mem_clusterRevealBonds Q₃ F₃ e).mp he₃
      exact Finset.disjoint_left.mp hLQ₃ heL.1 heQ.1
    · exact (Finset.mem_sdiff.mp hfR).2 he₃

end NearCritical
