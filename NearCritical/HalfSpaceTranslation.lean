module

public import NearCritical.ConnectionToSet
public import NearCritical.TranslationInvariance

/-! Exact restricted-domain translations used in the new half-space argument.
Translation and endpoint symmetry suffice; no reflection law is assumed. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Set MeasureTheory

/-- Restrict the actual translation graph isomorphism to translated domains. -/
def restrictedTranslationGraphIso {d : ℕ} (a : Vertex d) (ω : Configuration d)
    (S : Set (Vertex d)) : restrictedGraph (translateConfiguration a ω) S ≃g
      restrictedGraph ω ((fun z ↦ a + z) '' S) where
  toEquiv := Equiv.addLeft a
  map_rel_iff' := by
    intro x y
    change ((openGraph ω).Adj (a + x) (a + y) ∧
      a + x ∈ (fun z ↦ a + z) '' S ∧ a + y ∈ (fun z ↦ a + z) '' S) ↔
      ((openGraph (translateConfiguration a ω)).Adj x y ∧ x ∈ S ∧ y ∈ S)
    rw [← openGraph_translate_adj]
    simp

/-- Exact translation of actual domain-to-target connection events. -/
lemma connectionToSetEvent_translation {d : ℕ} (a x : Vertex d)
    (S B : Set (Vertex d)) :
    translateConfiguration a ⁻¹' connectionToSetEvent S x B =
      connectionToSetEvent ((fun z ↦ a + z) '' S) (a + x) ((fun z ↦ a + z) '' B) := by
  ext ω
  constructor
  · rintro ⟨hx, y, hy, hyS, hp⟩
    exact ⟨⟨x, hx, rfl⟩, a + y, ⟨y, hy, rfl⟩, ⟨y, hyS, rfl⟩,
      (restrictedTranslationGraphIso a ω S).reachable_iff.mpr hp⟩
  · rintro ⟨hx, z, ⟨y, hy, rfl⟩, hyS, hp⟩
    exact ⟨by simpa using hx, y, hy, by simpa using hyS,
      (restrictedTranslationGraphIso a ω S).reachable_iff.mp hp⟩

/-- Full-law stationarity for restricted connections, not merely unrestricted paths. -/
theorem connectionToSet_probability_translation {d : ℕ} (p : unitInterval)
    (a x : Vertex d) (S B : Set (Vertex d)) :
    percolation d p (connectionToSetEvent ((fun z ↦ a + z) '' S)
      (a + x) ((fun z ↦ a + z) '' B)) =
      percolation d p (connectionToSetEvent S x B) := by
  rw [← connectionToSetEvent_translation, ← Measure.map_apply
    (measurable_translateConfiguration a) (measurableSet_connectionToSetEvent S x B),
    percolation_map_translation]

/-- Endpoint symmetry includes both domain memberships and zero-length paths. -/
lemma connectionToSetEvent_singleton_symm {d : ℕ} (S : Set (Vertex d)) (x y : Vertex d) :
    connectionToSetEvent S x {y} = connectionToSetEvent S y {x} := by
  ext ω
  constructor <;> rintro ⟨hx, z, hz, hzS, hp⟩
  · have hzy : z = y := hz
    subst z
    exact ⟨hzS, x, rfl, hx, hp.symm⟩
  · have hzx : z = x := hz
    subst z
    exact ⟨hzS, y, rfl, hx, hp.symm⟩

lemma translate_halfSpace {d : ℕ} (a : Vertex d) (i : Fin d) (b : ℤ) :
    (fun z ↦ a + z) '' {z : Vertex d | b ≤ z i} = {z | b + a i ≤ z i} := by
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    change b ≤ y i at hy
    change b + a i ≤ a i + y i
    omega
  · intro hz
    refine ⟨-a + z, ?_, by simp⟩
    change b ≤ -a i + z i
    change b + a i ≤ z i at hz
    omega

/-- Translate both the domain and the upper half-space target exactly. -/
theorem halfSpace_arm_probability_translation {d : ℕ} (p : unitInterval)
    (a : Vertex d) (i : Fin d) (b n : ℤ) (x : Vertex d) :
    percolation d p (connectionToSetEvent {z | b + a i ≤ z i}
      (a + x) {z | n + a i ≤ z i}) =
      percolation d p (connectionToSetEvent {z | b ≤ z i} x {z | n ≤ z i}) := by
  simpa only [translate_halfSpace] using connectionToSet_probability_translation p a x
    {z | b ≤ z i} {z | n ≤ z i}

/-- A last-visit suffix has the boundary-origin arm law at the remaining height. -/
theorem halfSpace_suffix_probability {d : ℕ} (p : unitInterval)
    (i : Fin d) (l n : ℤ) (u : Vertex d) (hu : u i = l) :
    percolation d p (connectionToSetEvent {z | l ≤ z i} u {z | n ≤ z i}) =
      percolation d p (connectionToSetEvent {z | 0 ≤ z i} 0 {z | n - l ≤ z i}) := by
  have h := halfSpace_arm_probability_translation p (-u) i l n u
  simpa only [Pi.neg_apply, hu, add_neg_cancel, neg_add_cancel, sub_eq_add_neg] using h.symm

/-- The prefix probability reindexes to the source pioneer half-space by
translation by -u and endpoint symmetry; no reflection law is required. -/
theorem halfSpace_prefix_probability {d : ℕ} (p : unitInterval)
    (i : Fin d) (u : Vertex d) :
    percolation d p (connectionToSetEvent {z | 0 ≤ z i} 0 {u}) =
      percolation d p (connectionToSetEvent {z | -u i ≤ z i} 0 {-u}) := by
  have h := connectionToSet_probability_translation p (-u) 0 {z | 0 ≤ z i} {u}
  rw [translate_halfSpace] at h
  simp only [Pi.neg_apply, zero_add, add_zero, Set.image_singleton, neg_add_cancel] at h
  rw [connectionToSetEvent_singleton_symm] at h
  exact h.symm

end NearCritical
