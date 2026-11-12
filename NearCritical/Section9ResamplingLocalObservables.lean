module

public import NearCritical.Section9AdaptiveResampling

@[expose] public section
noncomputable section
namespace NearCritical
open scoped Classical

theorem section9TwoClusterFiberMask_subset_available {d : ℕ}
    (L R Q₁ F₁ Q₃ F₃ C₁ C₃ : Finset (Vertex d)) :
    section9TwoClusterFiberMask L R Q₁ F₁ Q₃ F₃ C₁ C₃ ⊆
      sprinklingAvailableBonds L Q₁ F₁ ∪ sprinklingAvailableBonds R Q₃ F₃ := by
  intro b hb
  rcases Finset.mem_union.mp hb with hL | hR
  · exact Finset.mem_union_left _ (Finset.mem_filter.mp hL).1
  · exact Finset.mem_union_right _ (Finset.mem_filter.mp hR).1

/-- Both explored-data observables and their adaptive mask depend only on
the available tube coordinates, which avoid the outer heart reveal. -/
theorem section9TwoClusterRevealWeight_local {d : ℕ}
    (L R Q₁ F₁ Q₃ F₃ : Finset (Vertex d)) (e : Vertex d × Vertex d)
    (F : ∀ C₁ C₃ : Finset (Vertex d),
      (section9TwoClusterFiberMask L R Q₁ F₁ Q₃ F₃ C₁ C₃ → Bool) → ℝ)
    (ω η : Configuration d)
    (hagree : ∀ b ∈ sprinklingAvailableBonds L Q₁ F₁ ∪
      sprinklingAvailableBonds R Q₃ F₃, ω b = η b) :
    section9TwoClusterRevealWeight L R Q₁ F₁ Q₃ F₃ e F ω =
      section9TwoClusterRevealWeight L R Q₁ F₁ Q₃ F₃ e F η := by
  have h₁ := sprinklingUnexploredCluster_eq_of_available_agree L Q₁ F₁ ω η
    (fun b hb => hagree b (Finset.mem_union_left _ hb)) e.1
  have h₃ := sprinklingUnexploredCluster_eq_of_available_agree R Q₃ F₃ ω η
    (fun b hb => hagree b (Finset.mem_union_right _ hb)) e.2
  unfold section9TwoClusterRevealWeight
  rw [h₁, h₃]
  congr 1
  funext b
  exact hagree b.val (section9TwoClusterFiberMask_subset_available L R Q₁ F₁ Q₃ F₃ _ _ b.property)

theorem section9TwoClusterRevealBonds_local {d : ℕ}
    (L R Q₁ F₁ Q₃ F₃ : Finset (Vertex d)) (e : Vertex d × Vertex d)
    (ω η : Configuration d)
    (hagree : ∀ b ∈ sprinklingAvailableBonds L Q₁ F₁ ∪
      sprinklingAvailableBonds R Q₃ F₃, ω b = η b) :
    section9TwoClusterRevealBonds ω L R Q₁ F₁ Q₃ F₃ e =
      section9TwoClusterRevealBonds η L R Q₁ F₁ Q₃ F₃ e := by
  have h₁ := sprinklingUnexploredCluster_eq_of_available_agree L Q₁ F₁ ω η
    (fun b hb => hagree b (Finset.mem_union_left _ hb)) e.1
  have h₃ := sprinklingUnexploredCluster_eq_of_available_agree R Q₃ F₃ ω η
    (fun b hb => hagree b (Finset.mem_union_right _ hb)) e.2
  simp only [section9TwoClusterRevealBonds, sprinklingClusterRevealBonds, h₁, h₃]

end NearCritical
