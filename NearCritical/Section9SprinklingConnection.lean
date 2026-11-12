module

public import NearCritical.SprinklingPivots
public import NearCritical.ConnectionToSet

/-! Section9, def.skl: an actual open sprinkled pivot connects its two critical
boundary sets. Critical side graphs delete only the specified explored edges;
configuration monotonicity transports the side paths, not the pivot predicate. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Set
open scoped Classical

/-- The same fixed explored-edge deletion respects monotone bond coupling. -/
lemma sprinklingUnexploredGraph_mono {d : ℕ} {ω η : Configuration d}
    (hmono : ∀ e, ω e = true → η e = true) (T Q F : Finset (Vertex d)) :
    sprinklingUnexploredGraph ω T Q F ≤ sprinklingUnexploredGraph η T Q F := by
  rintro x y ⟨hxy, hx, hy, hav⟩
  exact ⟨openGraph_mono hmono hxy, hx, hy, hav⟩

/-- An open joining pair creates a literal actual connection inside the two
source tubes. Neither a pre-existing A-B connection nor a completed path is
assumed; both critical boundary arms are extracted from the pivot definition. -/
theorem sprinkledPivotalPairs_connection {d : ℕ} {ω η : Configuration d}
    (hmono : ∀ e, ω e = true → η e = true)
    (E : Finset (Vertex d × Vertex d)) (L R Q₁ F₁ Q₃ F₃ A B : Finset (Vertex d))
    {e : Vertex d × Vertex d}
    (he : e ∈ sprinkledPivotalPairs ω η E L R Q₁ F₁ Q₃ F₃ A B) :
    ∃ x ∈ A, η ∈ connectionToSetEvent ((L : Set (Vertex d)) ∪ (R : Set (Vertex d)))
      x (B : Set (Vertex d)) := by
  obtain ⟨hcrit, hopen⟩ := Finset.mem_filter.mp he
  obtain ⟨_, hpiv⟩ := Finset.mem_filter.mp hcrit
  obtain ⟨_, haL, hbR, hleft, hright, _⟩ := hpiv
  obtain ⟨x, hx⟩ := hleft
  obtain ⟨y, hy⟩ := hright
  obtain ⟨hxC, hxA⟩ := Finset.mem_inter.mp hx
  obtain ⟨hyC, hyB⟩ := Finset.mem_inter.mp hy
  obtain ⟨hxL, hax⟩ := (mem_sprinklingUnexploredCluster ω L Q₁ F₁ e.1 x).mp hxC
  obtain ⟨hyR, hby⟩ := (mem_sprinklingUnexploredCluster ω R Q₃ F₃ e.2 y).mp hyC
  have hGL : sprinklingUnexploredGraph ω L Q₁ F₁ ≤
      restrictedGraph η ((L : Set (Vertex d)) ∪ (R : Set (Vertex d))) := by
    rintro u v ⟨huv, hu, hv, _⟩
    exact ⟨openGraph_mono hmono huv, Or.inl hu, Or.inl hv⟩
  have hGR : sprinklingUnexploredGraph ω R Q₃ F₃ ≤
      restrictedGraph η ((L : Set (Vertex d)) ∪ (R : Set (Vertex d))) := by
    rintro u v ⟨huv, hu, hv, _⟩
    exact ⟨openGraph_mono hmono huv, Or.inr hu, Or.inr hv⟩
  have hjoin : (restrictedGraph η ((L : Set (Vertex d)) ∪ (R : Set (Vertex d)))).Adj e.1 e.2 :=
    ⟨hopen, Or.inl haL, Or.inr hbR⟩
  refine ⟨x, hxA, Or.inl hxL, y, hyB, Or.inr hyR, ?_⟩
  exact (SimpleGraph.Reachable.mono hGL hax.symm).trans
    (hjoin.reachable.trans (SimpleGraph.Reachable.mono hGR hby))

/-- Nonempty pivo supplies an actual boundary-to-boundary sprinkled connection. -/
theorem sprinkledPivotalPairs_nonempty_connection {d : ℕ} {ω η : Configuration d}
    (hmono : ∀ e, ω e = true → η e = true)
    (E : Finset (Vertex d × Vertex d)) (L R Q₁ F₁ Q₃ F₃ A B : Finset (Vertex d))
    (h : (sprinkledPivotalPairs ω η E L R Q₁ F₁ Q₃ F₃ A B).Nonempty) :
    ∃ x ∈ A, η ∈ connectionToSetEvent ((L : Set (Vertex d)) ∪ (R : Set (Vertex d)))
      x (B : Set (Vertex d)) := by
  obtain ⟨e, he⟩ := h
  exact sprinkledPivotalPairs_connection hmono E L R Q₁ F₁ Q₃ F₃ A B he

end NearCritical
