module

public import NearCritical.Section10NextNestOccupation
public import NearCritical.Section9TwoLayerTransfer
public import NearCritical.Section10UnconditionalStep

/-! Transfer from the two-heart conditional law to the fresh coordinates
used by the Section 10 step kernel. -/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open MeasureTheory Set
open scoped Classical

/-- Every event determined by the actual read set has the same probability
under the two-heart reveal and the unconditional product law with those
revealed vertex sets held fixed in the event definition. -/
theorem stepReadSet_revealed_probability_eq {d : ℕ} (p q : unitInterval)
    (M L R Q₁ H₁ F₁ Q₃ H₃ F₃ : Finset (Vertex d))
    (hH₁ : H₁ ⊆ Q₁) (hH₃ : H₃ ⊆ Q₃)
    (hpos : percolation d p (section9RevealEvent Q₁ H₁ Q₃ H₃ F₁ F₃) ≠ 0)
    (hdis : Disjoint (clusterRevealBonds Q₁ F₁ ∪ clusterRevealBonds Q₃ F₃)
      ((sprinklingAvailableBonds L Q₁ F₁ ∪ sprinklingAvailableBonds R Q₃ F₃) ∪ internalBondSet M))
    (P : Configuration d × Configuration d → Prop)
    (hP : ReadsOnly (stepReadSet M L R Q₁ F₁ Q₃ F₃) P) :
    ((section9RevealedLaw p Q₁ H₁ Q₃ H₃ F₁ F₃).prod (percolation d q)).real {z | P z} =
      ((percolation d p).prod (percolation d q)).real {z | P z} := by
  refine section9_revealed_prod_eq p q Q₁ H₁ Q₃ H₃ F₁ F₃ hH₁ hH₃ hpos _ hdis _ hP.measurableSet ?_
  intro ω θ h η
  change P (ω, η) ↔ P (θ, η)
  have he : P (ω, η) = P (θ, η) := by
    refine hP (ω, η) (θ, η) ?_
    intro e he
    unfold stepReadSet at he
    rcases Finset.mem_union.mp he with hcrit | hspr
    · obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hcrit
      exact h b hb
    · obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hspr
      rfl
  rw [he]

/-- A next-nest occupation event is local on the tube read set and transfers
to the product law used in the joint exploration. -/
theorem svNext_occupation_revealed_probability_eq {d : ℕ} (p q : unitInterval)
    (M L R Q₁ H₁ F₁ Q₃ H₃ F₃ : Finset (Vertex d))
    (hH₁ : H₁ ⊆ Q₁) (hH₃ : H₃ ⊆ Q₃)
    (hpos : percolation d p (section9RevealEvent Q₁ H₁ Q₃ H₃ F₁ F₃) ≠ 0)
    (hdis : Disjoint (clusterRevealBonds Q₁ F₁ ∪ clusterRevealBonds Q₃ F₃)
      ((sprinklingAvailableBonds L Q₁ F₁ ∪ sprinklingAvailableBonds R Q₃ F₃) ∪ internalBondSet M))
    (nest cand : Finset (Finset (Vertex d))) (src tgt : Finset (Vertex d) → Finset (Vertex d))
    (k : ℕ) (P : Finset (Finset (Finset (Vertex d)))) (c : Finset (Vertex d)) :
    let A := {z | ∃ N' ∈ svNext (stepView M L R Q₁ F₁ Q₃ F₃ z) nest cand src tgt k P, c ∈ N'.val}
    ((section9RevealedLaw p Q₁ H₁ Q₃ H₃ F₁ F₃).prod (percolation d q)).real A =
      ((percolation d p).prod (percolation d q)).real A := by
  intro A
  exact stepReadSet_revealed_probability_eq p q M L R Q₁ H₁ F₁ Q₃ H₃ F₃ hH₁ hH₃ hpos hdis _
    ((stepView_readsOnly M L R Q₁ F₁ Q₃ F₃).comp
      (fun v => ∃ N' ∈ svNext v nest cand src tgt k P, c ∈ N'.val))

end NearCritical.Section10
