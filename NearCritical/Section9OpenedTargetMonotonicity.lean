module
public import NearCritical.Section9Pivotal

@[expose] public section
noncomputable section
namespace NearCritical
open scoped Classical

/-- With the critical configuration fixed, opening more enriched bonds
can only increase the number of targets with a sprinkled pivotal pair. -/
theorem section9_opened_target_count_mono {d : ℕ} {ι : Type*}
    (ω : Configuration d) {η θ : Configuration d}
    (h : ∀ b, η b = true → θ b = true)
    (I : Finset ι) (targets : ι → Finset (Vertex d))
    (E : Finset (Vertex d × Vertex d)) (L R Q₁ F₁ Q₃ F₃ A : Finset (Vertex d)) :
    (I.filter fun j => (sprinkledPivotalPairs ω η E L R Q₁ F₁ Q₃ F₃ A
      (targets j)).Nonempty).card ≤
    (I.filter fun j => (sprinkledPivotalPairs ω θ E L R Q₁ F₁ Q₃ F₃ A
      (targets j)).Nonempty).card := by
  apply Finset.card_le_card
  intro j hj
  obtain ⟨hjI, e, he⟩ := Finset.mem_filter.mp hj
  obtain ⟨heP, heOpen⟩ := Finset.mem_filter.mp he
  exact Finset.mem_filter.mpr ⟨hjI, e,
    Finset.mem_filter.mpr ⟨heP, openGraph_mono h heOpen⟩⟩

end NearCritical
