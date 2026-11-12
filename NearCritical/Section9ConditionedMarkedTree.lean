module

public import NearCritical.Section9MarkedPivotalTree
public import NearCritical.Section9FreshEvent
public import NearCritical.Section9PivotalSupport

@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory
open scoped Classical BigOperators

theorem section9_conditioned_marked_pivotal_tree_bound {d : ℕ} (p : unitInterval)
    (L R Q₁ H₁ F₁ Q₃ H₃ F₃ A B : Finset (Vertex d))
    (hH₁ : H₁ ⊆ Q₁) (hH₃ : H₃ ⊆ Q₃)
    (hpos : percolation d p (section9RevealEvent Q₁ H₁ Q₃ H₃ F₁ F₃) ≠ 0)
    (hLQ₃ : Disjoint L Q₃) (hRQ₁ : Disjoint R Q₁)
    (e : Vertex d × Vertex d) (w : Vertex d) :
    let ν := section9RevealedLaw p Q₁ H₁ Q₃ H₃ F₁ F₃
    let P := fun a b => (percolation d p).real
      (connectionToSetEvent (L : Set (Vertex d)) a {b})
    ν.real {ω | sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ A B e ∧
      w ∈ sprinklingUnexploredCluster ω L Q₁ F₁ e.1} ≤
      (∑ x ∈ A, ∑ u ∈ L, P e.1 u * (P u w * P x u)) *
        (percolation d p).real
          (connectionToSetEvent (R : Set (Vertex d)) e.2 (B : Set (Vertex d))) := by
  intro ν P
  let U := sprinklingAvailableBonds L Q₁ F₁ ∪ sprinklingAvailableBonds R Q₃ F₃
  let E := {ω : Configuration d | sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ A B e ∧
    w ∈ sprinklingUnexploredCluster ω L Q₁ F₁ e.1}
  have hE : MeasurableSet E := by
    have hm := (measurableSet_sprinklingPivotalPair L R Q₁ F₁ Q₃ F₃ A B e).inter
      (measurableSet_sprinklingUnexploredCluster_mem L Q₁ F₁ e.1 w)
    have he : ({ω | sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ A B e} ∩
        {ω | w ∈ sprinklingUnexploredCluster ω L Q₁ F₁ e.1} : Set (Configuration d)) = E := by
      ext ω
      simp [E]
    rwa [he] at hm
  have hlocal : ∀ ω η : Configuration d, (∀ b ∈ U, ω b = η b) →
      (ω ∈ E ↔ η ∈ E) := by
    intro ω η hagree
    have hL := fun b hb => hagree b (Finset.mem_union_left _ hb)
    have hR := fun b hb => hagree b (Finset.mem_union_right _ hb)
    have hp := sprinklingPivotalPair_iff_of_available_agree L R Q₁ F₁ Q₃ F₃ A B ω η hL hR e
    have hc := sprinklingUnexploredCluster_eq_of_available_agree L Q₁ F₁ ω η hL e.1
    simp only [E, Set.mem_setOf_eq, hp, hc]
  have he := section9RevealedLaw_fresh_probability p Q₁ H₁ Q₃ H₃ F₁ F₃ hH₁ hH₃ hpos U
    (sprinklingAvailableBonds_disjoint_reveals L R Q₁ F₁ Q₃ F₃ hLQ₃ hRQ₁) E hE hlocal
  change ν.real E ≤ _
  rw [he]
  exact section9_marked_pivotal_tree_bound p L R Q₁ F₁ Q₃ F₃ A B e w

end NearCritical
