module
public import NearCritical.Section9ConditionalLaw
public import NearCritical.SprinklingPivots

/-! Literal left/right symmetry for the pivotal and revealed-law interfaces. -/
@[expose] public section
noncomputable section
namespace NearCritical
open scoped Classical

/-- Reversing a pivotal candidate exchanges its two domains, revealed
heart data, and target families, including the nonmonotone disjointness clause. -/
theorem sprinklingPivotalPair_swap_iff {d : ℕ} (ω : Configuration d)
    (L R Q₁ F₁ Q₃ F₃ A B : Finset (Vertex d)) (e : Vertex d × Vertex d) :
    sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ A B e ↔
      sprinklingPivotalPair ω R L Q₃ F₃ Q₁ F₁ B A e.swap := by
  constructor
  · rintro ⟨hadj,hL,hR,hA,hB,hdis⟩
    exact ⟨hadj.symm,hR,hL,hB,hA,hdis.symm⟩
  · rintro ⟨hadj,hR,hL,hB,hA,hdis⟩
    exact ⟨hadj.symm,hL,hR,hA,hB,hdis.symm⟩

/-- The same two heart reveals may be recorded in either order. -/
theorem section9RevealEvent_swap {d : ℕ}
    (Q₁ H₁ Q₃ H₃ F₁ F₃ : Finset (Vertex d)) :
    section9RevealEvent Q₁ H₁ Q₃ H₃ F₁ F₃ =
      section9RevealEvent Q₃ H₃ Q₁ H₁ F₃ F₁ := by
  ext ω
  exact and_comm

/-- Conditional configuration laws are unchanged by exchanging the two
revealed heart records; this equality needs no positive-atom premise. -/
theorem section9RevealedLaw_swap {d : ℕ} (p : unitInterval)
    (Q₁ H₁ Q₃ H₃ F₁ F₃ : Finset (Vertex d)) :
    section9RevealedLaw p Q₁ H₁ Q₃ H₃ F₁ F₃ =
      section9RevealedLaw p Q₃ H₃ Q₁ H₁ F₃ F₁ := by
  unfold section9RevealedLaw
  rw [section9RevealEvent_swap Q₁ H₁ Q₃ H₃ F₁ F₃]

/-- Both orientations of every enumerated middle candidate are retained. -/
theorem mem_orientedLatticePairs_swap_iff {d : ℕ} (S : Finset (Vertex d))
    (e : Vertex d × Vertex d) :
    e.swap ∈ orientedLatticePairs S ↔ e ∈ orientedLatticePairs S := by
  rcases e with ⟨x,y⟩
  change (y,x) ∈ orientedLatticePairs S ↔ (x,y) ∈ orientedLatticePairs S
  rw [mem_orientedLatticePairs,mem_orientedLatticePairs]
  constructor
  · rintro ⟨hy,hx,hadj⟩
    exact ⟨hx,hy,hadj.symm⟩
  · rintro ⟨hx,hy,hadj⟩
    exact ⟨hy,hx,hadj.symm⟩

end NearCritical
