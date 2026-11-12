module

public import NearCritical.Section9Pivotal

/-! Literal vertex-set sprinkling cluster and coalescence count from Section9.
Graph/path structure and quantitative coalescence rates remain separate. -/
@[expose] public section
noncomputable section
namespace NearCritical
open scoped Classical

/-- Source def.skl: both full critical components over actual opened pivots. -/
def section9SprinklingCluster {d : ℕ} (ω η : Configuration d)
    (E : Finset (Vertex d × Vertex d)) (L R Q₁ F₁ Q₃ F₃ A B : Finset (Vertex d)) :
    Finset (Vertex d) :=
  (sprinkledPivotalPairs ω η E L R Q₁ F₁ Q₃ F₃ A B).biUnion fun e =>
    sprinklingUnexploredCluster ω L Q₁ F₁ e.1 ∪ sprinklingUnexploredCluster ω R Q₃ F₃ e.2

lemma mem_section9SprinklingCluster {d : ℕ} (ω η : Configuration d)
    (E : Finset (Vertex d × Vertex d)) (L R Q₁ F₁ Q₃ F₃ A B : Finset (Vertex d)) (z : Vertex d) :
    z ∈ section9SprinklingCluster ω η E L R Q₁ F₁ Q₃ F₃ A B ↔
      ∃ e ∈ sprinkledPivotalPairs ω η E L R Q₁ F₁ Q₃ F₃ A B,
        z ∈ sprinklingUnexploredCluster ω L Q₁ F₁ e.1 ∨
          z ∈ sprinklingUnexploredCluster ω R Q₃ F₃ e.2 := by
  simp only [section9SprinklingCluster, Finset.mem_biUnion, Finset.mem_union]

lemma section9SprinklingCluster_subset {d : ℕ} (ω η : Configuration d)
    (E : Finset (Vertex d × Vertex d)) (L R Q₁ F₁ Q₃ F₃ A B : Finset (Vertex d)) :
    section9SprinklingCluster ω η E L R Q₁ F₁ Q₃ F₃ A B ⊆ L ∪ R := by
  intro z hz
  obtain ⟨e,_,hzL | hzR⟩ := (mem_section9SprinklingCluster ω η E L R Q₁ F₁ Q₃ F₃ A B z).mp hz
  · exact Finset.mem_union.mpr (Or.inl (sprinklingUnexploredCluster_subset ω L Q₁ F₁ e.1 hzL))
  · exact Finset.mem_union.mpr (Or.inr (sprinklingUnexploredCluster_subset ω R Q₃ F₃ e.2 hzR))

/-- No left cluster is included when no pivot opens. -/
theorem section9SprinklingCluster_nonempty_iff {d : ℕ} (ω η : Configuration d)
    (E : Finset (Vertex d × Vertex d)) (L R Q₁ F₁ Q₃ F₃ A B : Finset (Vertex d)) :
    (section9SprinklingCluster ω η E L R Q₁ F₁ Q₃ F₃ A B).Nonempty ↔
      (sprinkledPivotalPairs ω η E L R Q₁ F₁ Q₃ F₃ A B).Nonempty := by
  constructor
  · rintro ⟨z,hz⟩
    obtain ⟨e,he,_⟩ := (mem_section9SprinklingCluster ω η E L R Q₁ F₁ Q₃ F₃ A B z).mp hz
    exact ⟨e,he⟩
  · rintro ⟨e,he⟩
    have heP := (Finset.mem_filter.mp he).1
    have hpiv := (Finset.mem_filter.mp heP).2
    refine ⟨e.1,(mem_section9SprinklingCluster ω η E L R Q₁ F₁ Q₃ F₃ A B e.1).mpr ?_⟩
    exact ⟨e,he,Or.inl (root_mem_sprinklingUnexploredCluster ω L Q₁ F₁ hpiv.2.1)⟩

/-- Actual ordered root pairs whose singleton-root sprinkling clusters meet. -/
def section9CoalescencePairs {d : ℕ} (ω η : Configuration d)
    (E : Finset (Vertex d × Vertex d)) (L R Q₁ F₁ Q₃ F₃ A A' B : Finset (Vertex d)) :
    Finset (Vertex d × Vertex d) :=
  (A.product A').filter fun xy =>
    (section9SprinklingCluster ω η E L R Q₁ F₁ Q₃ F₃ {xy.1} B ∩
      section9SprinklingCluster ω η E L R Q₁ F₁ Q₃ F₃ {xy.2} B).Nonempty

def section9CoalescenceCount {d : ℕ} (ω η : Configuration d)
    (E : Finset (Vertex d × Vertex d)) (L R Q₁ F₁ Q₃ F₃ A A' B : Finset (Vertex d)) : ℕ :=
  (section9CoalescencePairs ω η E L R Q₁ F₁ Q₃ F₃ A A' B).card

lemma mem_section9CoalescencePairs {d : ℕ} (ω η : Configuration d)
    (E : Finset (Vertex d × Vertex d)) (L R Q₁ F₁ Q₃ F₃ A A' B : Finset (Vertex d))
    (x x' : Vertex d) :
    (x,x') ∈ section9CoalescencePairs ω η E L R Q₁ F₁ Q₃ F₃ A A' B ↔
      x ∈ A ∧ x' ∈ A' ∧
        (section9SprinklingCluster ω η E L R Q₁ F₁ Q₃ F₃ {x} B ∩
          section9SprinklingCluster ω η E L R Q₁ F₁ Q₃ F₃ {x'} B).Nonempty := by
  simp only [section9CoalescencePairs, Finset.mem_filter]
  rw [Finset.product_eq_sprod, Finset.mem_product, and_assoc]

/-- Finite domination only, not the quantitative source coalescence rate. -/
lemma section9CoalescenceCount_le {d : ℕ} (ω η : Configuration d)
    (E : Finset (Vertex d × Vertex d)) (L R Q₁ F₁ Q₃ F₃ A A' B : Finset (Vertex d)) :
    section9CoalescenceCount ω η E L R Q₁ F₁ Q₃ F₃ A A' B ≤ A.card*A'.card := by
  unfold section9CoalescenceCount section9CoalescencePairs
  exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (Finset.card_product _ _)

end NearCritical
