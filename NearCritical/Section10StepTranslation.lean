module

public import NearCritical.Section10StepLocality
public import NearCritical.TranslationInvariance
public import NearCritical.ConductivityTranslation

/-! Translation covariance of the sprinkling objects of one step.

The Section 9 theorems are stated for the cube at the origin. A lattice step
starts from a cube at `a`. With `ω' = translateConfiguration a ω`
(`ω' e = ω (a + e)`), every object of the step at `a` in `ω` is the translate by
`a` of the same object at the origin in `ω'`:

* `sprinklingUnexploredGraph_translate_adj`, `sprinklingUnexploredCluster_translate`;
* `sprinklingPivotalPair_translate`;
* `sprinkledPivotalPairs_translate` (the opened pivotal pairs, as a set);
* `sprinkledPivotalPairs_nonempty_translate` (so counts of opened targets agree).
-/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open scoped Classical

lemma translateSites_injective {d : ℕ} (a : Vertex d) :
    Function.Injective (fun x : Vertex d => a + x) := add_right_injective a

lemma mem_translateSites_iff {d : ℕ} (a : Vertex d) (U : Finset (Vertex d)) (x : Vertex d) :
    x ∈ translateSites a U ↔ ∃ y ∈ U, a + y = x := by
  unfold translateSites
  exact Finset.mem_image

/-- Shift of an ordered pair of vertices. -/
def shiftPair {d : ℕ} (a : Vertex d) (e : Vertex d × Vertex d) : Vertex d × Vertex d :=
  (a + e.1, a + e.2)

lemma shiftPair_injective {d : ℕ} (a : Vertex d) : Function.Injective (shiftPair a) := by
  intro e e' h
  have h1 := add_right_injective a (Prod.mk.inj h).1
  have h2 := add_right_injective a (Prod.mk.inj h).2
  exact Prod.ext h1 h2

theorem sprinklingUnexploredGraph_translate_adj {d : ℕ} (a : Vertex d) (ω : Configuration d)
    (T Q F : Finset (Vertex d)) (x y : Vertex d) :
    (sprinklingUnexploredGraph (translateConfiguration a ω) T Q F).Adj x y ↔
      (sprinklingUnexploredGraph ω (translateSites a T) (translateSites a Q)
        (translateSites a F)).Adj (a + x) (a + y) := by
  show ((openGraph (translateConfiguration a ω)).Adj x y ∧ x ∈ (T : Set (Vertex d)) ∧
      y ∈ (T : Set (Vertex d)) ∧
      s(x, y) ∈ (exploredEdgeSet (Q : Set (Vertex d)) (F : Set (Vertex d)))ᶜ) ↔
    ((openGraph ω).Adj (a + x) (a + y) ∧ a + x ∈ (translateSites a T : Set (Vertex d)) ∧
      a + y ∈ (translateSites a T : Set (Vertex d)) ∧
      s(a + x, a + y) ∈ (exploredEdgeSet (translateSites a Q : Set (Vertex d))
        (translateSites a F : Set (Vertex d)))ᶜ)
  simp only [Set.mem_compl_iff, pair_mem_exploredEdgeSet, Finset.mem_coe, mem_translateSites,
    openGraph_translate_adj]

/-- The graph isomorphism of the unexplored graphs. -/
def unexploredTranslateIso {d : ℕ} (a : Vertex d) (ω : Configuration d)
    (T Q F : Finset (Vertex d)) :
    sprinklingUnexploredGraph (translateConfiguration a ω) T Q F ≃g
      sprinklingUnexploredGraph ω (translateSites a T) (translateSites a Q)
        (translateSites a F) where
  toEquiv := Equiv.addLeft a
  map_rel_iff' := (sprinklingUnexploredGraph_translate_adj a ω T Q F _ _).symm

theorem sprinklingUnexploredCluster_translate {d : ℕ} (a : Vertex d) (ω : Configuration d)
    (T Q F : Finset (Vertex d)) (root : Vertex d) :
    sprinklingUnexploredCluster ω (translateSites a T) (translateSites a Q)
        (translateSites a F) (a + root) =
      translateSites a
        (sprinklingUnexploredCluster (translateConfiguration a ω) T Q F root) := by
  ext x
  unfold sprinklingUnexploredCluster
  rw [mem_translateSites_iff]
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hxT, hreach⟩
    obtain ⟨y, hy, rfl⟩ := (mem_translateSites_iff a T x).mp hxT
    refine ⟨y, ⟨hy, ?_⟩, rfl⟩
    exact ((unexploredTranslateIso a ω T Q F).reachable_iff (u := root) (v := y)).mp hreach
  · rintro ⟨y, ⟨hy, hreach⟩, rfl⟩
    refine ⟨(mem_translateSites a T y).mpr hy, ?_⟩
    exact ((unexploredTranslateIso a ω T Q F).reachable_iff (u := root) (v := y)).mpr hreach

lemma translateSites_inter_nonempty {d : ℕ} (a : Vertex d) (C A : Finset (Vertex d)) :
    (translateSites a C ∩ translateSites a A).Nonempty ↔ (C ∩ A).Nonempty := by
  unfold translateSites
  rw [← Finset.image_inter _ _ (translateSites_injective a), Finset.image_nonempty]

lemma translateSites_disjoint {d : ℕ} (a : Vertex d) (C A : Finset (Vertex d)) :
    Disjoint (translateSites a C) (translateSites a A) ↔ Disjoint C A := by
  unfold translateSites
  exact Finset.disjoint_image (translateSites_injective a)

lemma latticeAdj_translate {d : ℕ} (a x y : Vertex d) :
    (openGraph (fun _ : Bond d => true)).Adj (a + x) (a + y) ↔
      (openGraph (fun _ : Bond d => true)).Adj x y :=
  (openGraph_translate_adj a (fun _ : Bond d => true) x y).symm

theorem sprinklingPivotalPair_translate {d : ℕ} (a : Vertex d) (ω : Configuration d)
    (L R Q₁ F₁ Q₃ F₃ A B : Finset (Vertex d)) (e : Vertex d × Vertex d) :
    sprinklingPivotalPair ω (translateSites a L) (translateSites a R) (translateSites a Q₁)
        (translateSites a F₁) (translateSites a Q₃) (translateSites a F₃)
        (translateSites a A) (translateSites a B) (shiftPair a e) ↔
      sprinklingPivotalPair (translateConfiguration a ω) L R Q₁ F₁ Q₃ F₃ A B e := by
  unfold sprinklingPivotalPair shiftPair
  simp only [sprinklingUnexploredCluster_translate, translateSites_inter_nonempty,
    translateSites_disjoint, latticeAdj_translate, mem_translateSites]

end NearCritical.Section10
