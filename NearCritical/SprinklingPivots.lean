module

public import NearCritical.Section9Pivotal

/-! Section9 middle-box oriented candidate set and geometric closedness adapter.
The canonical critical/open pivot definitions are in Section9Pivotal. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Set
open scoped Classical

/-- Both physical orientations of every nearest-neighbor pair inside S2. -/
def orientedLatticePairs {d : ℕ} (S : Finset (Vertex d)) : Finset (Vertex d × Vertex d) :=
  (S.product S).filter (fun e => (openGraph (fun _ => true)).Adj e.1 e.2)

lemma mem_orientedLatticePairs {d : ℕ} (S : Finset (Vertex d)) (a b : Vertex d) :
    (a,b) ∈ orientedLatticePairs S ↔
      a ∈ S ∧ b ∈ S ∧ (openGraph (fun _ => true)).Adj a b := by
  simp [orientedLatticePairs, and_assoc]

/-- Middle-box separation supplies the joining-edge availability required by
canonical pivotal closedness. No closed-edge condition is assumed. -/
theorem middle_sprinklingPivotalPairs_closed {d : ℕ} {ω : Configuration d}
    (S L R Q₁ F₁ Q₃ F₃ A B : Finset (Vertex d))
    (hSL : S ⊆ L) (hsep : Disjoint (S : Set (Vertex d)) (Q₁ : Set (Vertex d)))
    {e : Vertex d × Vertex d}
    (he : e ∈ sprinklingPivotalPairs ω (orientedLatticePairs S) L R Q₁ F₁ Q₃ F₃ A B) :
    ¬ (openGraph ω).Adj e.1 e.2 := by
  obtain ⟨hE, hpiv⟩ := Finset.mem_filter.mp he
  obtain ⟨ha, hb, _⟩ := (mem_orientedLatticePairs S e.1 e.2).mp hE
  apply sprinklingPivotalPair_not_open L R Q₁ F₁ Q₃ F₃ A B hpiv (hSL hb)
  intro hex
  exact Set.disjoint_left.mp hsep ha ((pair_mem_exploredEdgeSet _ _ _ _).mp hex).1

end NearCritical
