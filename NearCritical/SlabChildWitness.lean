module

public import NearCritical.SlabStepOffspring
public import NearCritical.NestRepresentative

/-! Choose a full child nest reached from one parent cluster, using the same
opened pivots as the offspring event. -/
@[expose] public section
noncomputable section

namespace NearCritical

open Section10
open scoped Classical

/-- Membership in the offspring computed from a fixed set of opened pivots
gives a path in the sprinkled configuration. -/
theorem slabStep_child_path {d : ℕ} (M L R Q₁ F₁ Q₃ F₃ S : Finset (Vertex d))
    (cand : Finset (Finset (Vertex d))) (patch : Finset (Vertex d) → Finset (Vertex d))
    (z : Configuration d × Configuration d) (T : Set (Vertex d))
    (hL : (L : Set (Vertex d)) ⊆ T) (hR : (R : Set (Vertex d)) ⊆ T)
    (hM : (M : Set (Vertex d)) ⊆ T)
    (U : Finset (Vertex d)) {C : Finset (Vertex d)}
    (hC : let v := stepView M L R Q₁ F₁ Q₃ F₃ z
      C ∈ sprinklingOffspring v.1 v.2.1 U cand patch (v.2.2.1 S (sprinklingTargetBoundary cand patch))) :
    ∃ x ∈ U, ∃ y ∈ patch C,
      (restrictedGraph (sprinkleOrConfiguration z.1 z.2) T).Reachable x y := by
  let v := stepView M L R Q₁ F₁ Q₃ F₃ z
  obtain ⟨_, x, hx, y, hy, e, he, hxe, hey⟩ :=
    (mem_sprinklingOffspring v.1 v.2.1 U cand patch
      (v.2.2.1 S (sprinklingTargetBoundary cand patch)) C).mp hC
  have hmono (b : Bond d) (hb : z.1 b = true) : sprinkleOrConfiguration z.1 z.2 b = true := by
    simp [sprinkleOrConfiguration, hb]
  have hLeft : v.1 ≤ restrictedGraph (sprinkleOrConfiguration z.1 z.2) T := by
    rintro u w ⟨hadj, hu, hw, _⟩
    exact ⟨openGraph_mono hmono hadj, hL hu, hL hw⟩
  have hRight : v.2.1 ≤ restrictedGraph (sprinkleOrConfiguration z.1 z.2) T := by
    rintro u w ⟨hadj, hu, hw, _⟩
    exact ⟨openGraph_mono hmono hadj, hR hu, hR hw⟩
  change e ∈ sprinkledPivotalPairs z.1 (sprinkleOrConfiguration z.1 z.2)
    (orientedLatticePairs M) L R Q₁ F₁ Q₃ F₃ S (sprinklingTargetBoundary cand patch) at he
  obtain ⟨hpiv, heOpen⟩ := Finset.mem_filter.mp he
  obtain ⟨heM, _⟩ := Finset.mem_filter.mp hpiv
  obtain ⟨he₁, he₂, _⟩ := (mem_orientedLatticePairs M e.1 e.2).mp heM
  have hPivot : (restrictedGraph (sprinkleOrConfiguration z.1 z.2) T).Adj e.1 e.2 :=
    ⟨heOpen, hM he₁, hM he₂⟩
  exact ⟨x, hx, y, hy, (SimpleGraph.Reachable.mono hLeft hxe.symm).trans
    (hPivot.reachable.trans (SimpleGraph.Reachable.mono hRight hey))⟩

/-- If the full parent nest reaches at least (k^2) clusters, a single
parent cluster has a (k)-element child nest. -/
theorem slabStep_exists_childNest {d : ℕ} (M L R Q₁ F₁ Q₃ F₃ : Finset (Vertex d))
    (nest cand : Finset (Finset (Vertex d))) (source patch : Finset (Vertex d) → Finset (Vertex d))
    (z : Configuration d × Configuration d) {k : ℕ} (hk : 0 < k) (hcard : nest.card = k)
    (hcount : k * k ≤ (slabStepOffspring M L R Q₁ F₁ Q₃ F₃
      (sprinklingTargetBoundary nest source) cand patch z).card) :
    let S := sprinklingTargetBoundary nest source
    let v := stepView M L R Q₁ F₁ Q₃ F₃ z
    let pivots := v.2.2.1 S (sprinklingTargetBoundary cand patch)
    ∃ C ∈ nest, ∃ child : Finset (Finset (Vertex d)),
      child.card = k ∧ child ⊆ sprinklingOffspring v.1 v.2.1 (source C) cand patch pivots := by
  intro S v pivots
  let children := fun C => sprinklingOffspring v.1 v.2.1 (source C) cand patch pivots
  have hsub : slabStepOffspring M L R Q₁ F₁ Q₃ F₃ S cand patch z ⊆ nest.biUnion children := by
    intro E hE
    obtain ⟨hEc, x, hx, y, hy, e, he, h₁, h₂⟩ :=
      (mem_sprinklingOffspring v.1 v.2.1 S cand patch pivots E).mp hE
    obtain ⟨C, hC, hxC⟩ := Finset.mem_biUnion.mp hx
    exact Finset.mem_biUnion.mpr ⟨C, hC,
      (mem_sprinklingOffspring v.1 v.2.1 (source C) cand patch pivots E).mpr
        ⟨hEc, x, hxC, y, hy, e, he, h₁, h₂⟩⟩
  obtain ⟨C, hC, hchildren⟩ := nest_exists_large_offspring nest children hk hcard
    (hcount.trans (Finset.card_le_card hsub))
  obtain ⟨child, hsub, hsize⟩ := Finset.exists_subset_card_eq hchildren
  exact ⟨C, hC, child, hsize, hsub⟩

/-- Select the representative and child nest when the offspring count meets
the threshold of the slab step. -/
def slabStepChildNest {d : ℕ} (M L R Q₁ F₁ Q₃ F₃ : Finset (Vertex d))
    (nest cand : Finset (Finset (Vertex d))) (source patch : Finset (Vertex d) → Finset (Vertex d))
    (z : Configuration d × Configuration d) {k : ℕ} (hk : 0 < k) (hcard : nest.card = k) :
    Option (Finset (Vertex d) × Finset (Finset (Vertex d))) :=
  if h : k * k ≤ (slabStepOffspring M L R Q₁ F₁ Q₃ F₃
      (sprinklingTargetBoundary nest source) cand patch z).card then
    let hchild := slabStep_exists_childNest M L R Q₁ F₁ Q₃ F₃ nest cand source patch z hk hcard h
    some (Classical.choose hchild, Classical.choose (Classical.choose_spec hchild).2)
  else none

theorem slabStepChildNest_spec {d : ℕ} (M L R Q₁ F₁ Q₃ F₃ : Finset (Vertex d))
    (nest cand : Finset (Finset (Vertex d))) (source patch : Finset (Vertex d) → Finset (Vertex d))
    (z : Configuration d × Configuration d) {k : ℕ} (hk : 0 < k) (hcard : nest.card = k)
    {C : Finset (Vertex d)} {child : Finset (Finset (Vertex d))}
    (h : slabStepChildNest M L R Q₁ F₁ Q₃ F₃ nest cand source patch z hk hcard = some (C, child)) :
    let S := sprinklingTargetBoundary nest source
    let v := stepView M L R Q₁ F₁ Q₃ F₃ z
    C ∈ nest ∧ child.card = k ∧
      child ⊆ sprinklingOffspring v.1 v.2.1 (source C) cand patch
        (v.2.2.1 S (sprinklingTargetBoundary cand patch)) := by
  unfold slabStepChildNest at h
  split at h
  · rename_i hcount
    let hchild := slabStep_exists_childNest M L R Q₁ F₁ Q₃ F₃ nest cand source patch z hk hcard hcount
    change some (Classical.choose hchild, Classical.choose (Classical.choose_spec hchild).2) =
      some (C, child) at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    exact ⟨(Classical.choose_spec hchild).1, Classical.choose_spec (Classical.choose_spec hchild).2⟩
  · simp at h

theorem slabStepChildNest_isSome_iff {d : ℕ} (M L R Q₁ F₁ Q₃ F₃ : Finset (Vertex d))
    (nest cand : Finset (Finset (Vertex d))) (source patch : Finset (Vertex d) → Finset (Vertex d))
    (z : Configuration d × Configuration d) {k : ℕ} (hk : 0 < k) (hcard : nest.card = k) :
    (slabStepChildNest M L R Q₁ F₁ Q₃ F₃ nest cand source patch z hk hcard).isSome = true ↔
      k * k ≤ (slabStepOffspring M L R Q₁ F₁ Q₃ F₃
        (sprinklingTargetBoundary nest source) cand patch z).card := by
  unfold slabStepChildNest
  split_ifs with h <;> simp [h]

end NearCritical
