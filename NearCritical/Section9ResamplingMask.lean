module

public import NearCritical.Section9ResamplingCollision
public import NearCritical.FiniteBlockResampling

@[expose] public section
noncomputable section
namespace NearCritical
open scoped Classical

/-- Resampling bonds incident to C preserves every open adjacency outside C. -/
theorem resampleBonds_open_adj_away {d : ℕ} (S : Finset (Bond d))
    (C : Finset (Vertex d))
    (htouch : ∀ e ∈ S, e.1 ∈ C ∨ bondTip e ∈ C)
    (ω ζ : Configuration d) (a b : Vertex d) (ha : a ∉ C) (hb : b ∉ C) :
    (openGraph (resampleBonds S ω ζ)).Adj a b ↔ (openGraph ω).Adj a b := by
  have hbits (e : Bond d) (he₁ : e.1 ∉ C) (he₂ : bondTip e ∉ C) :
      resampleBonds S ω ζ e = ω e := by
    have he : e ∉ S := fun h => (htouch e h).elim he₁ he₂
    simp [resampleBonds, extendConfiguration, he]
  constructor
  · rintro ⟨e, hopen, he | he⟩
    · obtain ⟨rfl, rfl⟩ := he
      exact ⟨e, (hbits e ha hb).symm.trans hopen, Or.inl ⟨rfl, rfl⟩⟩
    · obtain ⟨rfl, rfl⟩ := he
      exact ⟨e, (hbits e hb ha).symm.trans hopen, Or.inr ⟨rfl, rfl⟩⟩
  · rintro ⟨e, hopen, he | he⟩
    · obtain ⟨rfl, rfl⟩ := he
      exact ⟨e, (hbits e ha hb).trans hopen, Or.inl ⟨rfl, rfl⟩⟩
    · obtain ⟨rfl, rfl⟩ := he
      exact ⟨e, (hbits e hb ha).trans hopen, Or.inr ⟨rfl, rfl⟩⟩

/-- The source no-collision comparison for the literal bond replacement map.
The mask may depend on the original configuration before this pointwise use. -/
theorem resampleBonds_sprinkling_cluster_eq {d : ℕ}
    (S : Finset (Bond d)) (C T Q F : Finset (Vertex d))
    (htouch : ∀ e ∈ S, e.1 ∈ C ∨ bondTip e ∈ C)
    (ω ζ : Configuration d) (root : Vertex d)
    (hω : Disjoint (sprinklingUnexploredCluster ω T Q F root) C)
    (hζ : Disjoint (sprinklingUnexploredCluster (resampleBonds S ω ζ) T Q F root) C) :
    sprinklingUnexploredCluster (resampleBonds S ω ζ) T Q F root =
      sprinklingUnexploredCluster ω T Q F root := by
  apply sprinkling_cluster_eq_of_no_resampling_collision _ _ T Q F C root ?_ hζ hω
  intro a b ha hb
  change ((openGraph (resampleBonds S ω ζ)).Adj a b ∧ a ∈ T ∧ b ∈ T ∧
      s(a,b) ∈ (exploredEdgeSet (Q : Set (Vertex d)) (F : Set (Vertex d)))ᶜ) ↔
    ((openGraph ω).Adj a b ∧ a ∈ T ∧ b ∈ T ∧
      s(a,b) ∈ (exploredEdgeSet (Q : Set (Vertex d)) (F : Set (Vertex d)))ᶜ)
  rw [resampleBonds_open_adj_away S C htouch ω ζ a b ha hb]

end NearCritical
