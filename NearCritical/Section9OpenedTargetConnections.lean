module
public import NearCritical.Section9SprinklingConnection

@[expose] public section
noncomputable section
namespace NearCritical
open scoped Classical

/-- Every target with an opened pivotal pair is reached by a connection
in the union of the two tubes. -/
theorem section9_opened_target_count_le_connection_count {d : ℕ} {ι : Type*}
    {ω η : Configuration d} (hmono : ∀ b, ω b = true → η b = true)
    (I : Finset ι) (targets : ι → Finset (Vertex d))
    (E : Finset (Vertex d × Vertex d)) (L R Q₁ F₁ Q₃ F₃ A : Finset (Vertex d)) :
    (I.filter fun j => (sprinkledPivotalPairs ω η E L R Q₁ F₁ Q₃ F₃ A
      (targets j)).Nonempty).card ≤
    (I.filter fun j => ∃ x ∈ A, η ∈ connectionToSetEvent
      ((L : Set (Vertex d)) ∪ (R : Set (Vertex d))) x (targets j : Set (Vertex d))).card := by
  apply Finset.card_le_card
  intro j hj
  obtain ⟨hjI, hjPivot⟩ := Finset.mem_filter.mp hj
  exact Finset.mem_filter.mpr ⟨hjI,
    sprinkledPivotalPairs_nonempty_connection hmono E L R Q₁ F₁ Q₃ F₃ A
      (targets j) hjPivot⟩

end NearCritical
