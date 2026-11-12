module

public import NearCritical.Section9SprinklingCluster
public import NearCritical.Section9PivotOpening
public import NearCritical.SprinklingIntrinsic

/-! A short offspring bridge with support in the two actual pivotal components. -/

@[expose] public section
noncomputable section
namespace NearCritical.Section10

open scoped Classical

/-- A selected offspring has a short bridge inside the actual sprinkling
cluster of the whole nest. Its edges avoid both explored end cubes. -/
theorem offspring_short_bridge_trace {d : ℕ} {ι : Type*}
    (ω η : Configuration d) (D : Set (Vertex d))
    (L R Q₁ F₁ Q₃ F₃ : Finset (Vertex d))
    (hLD : (L : Set (Vertex d)) ⊆ D) (hRD : (R : Set (Vertex d)) ⊆ D)
    (hLQ : Disjoint (L : Set (Vertex d)) (Q₃ : Set (Vertex d)))
    (hRQ : Disjoint (R : Set (Vertex d)) (Q₁ : Set (Vertex d)))
    (E : Finset (Vertex d × Vertex d)) (A Aall : Finset (Vertex d))
    (candidates : Finset ι) (boundary : ι → Finset (Vertex d))
    {c : ι} {K : ℝ} :
    let Gₗ := sprinklingUnexploredGraph ω L Q₁ F₁
    let Gᵣ := sprinklingUnexploredGraph ω R Q₃ F₃
    let Ω := sprinkleOrConfiguration ω η
    let B := sprinklingTargetBoundary candidates boundary
    let P := sprinkledPivotalPairs ω Ω E L R Q₁ F₁ Q₃ F₃ Aall B
    c ∈ sprinklingOffspring Gₗ Gᵣ A candidates boundary P →
    (sprinklingIntrinsicDiameter Gₗ Gᵣ A B P : ℝ) ≤ K →
    ∃ x ∈ A, ∃ y ∈ boundary c, ∃ w : (restrictedGraph Ω D).Walk x y,
      (w.length : ℝ) ≤ K ∧
      (∀ v ∈ w.support, v ∈ section9SprinklingCluster ω Ω E L R Q₁ F₁ Q₃ F₃ Aall B) ∧
      (∀ e ∈ w.edges, e ∉ exploredEdgeSet Q₁ F₁ ∪ exploredEdgeSet Q₃ F₃) := by
  intro Gₗ Gᵣ Ω B P hc hdiam
  obtain ⟨hcand,x,hx,y,hy,⟨a,b⟩,he,hleft,hright⟩ :=
    (mem_sprinklingOffspring Gₗ Gᵣ A candidates boundary P c).mp hc
  have he' : (a,b) ∈ sprinkledPivotalPairs ω Ω E L R Q₁ F₁ Q₃ F₃ Aall B := he
  obtain ⟨hpiv, hopen⟩ := Finset.mem_filter.mp he'
  have hdata := (Finset.mem_filter.mp hpiv).2
  have ha : a ∈ L := hdata.2.1
  have hb : b ∈ R := hdata.2.2.1
  have hyB : y ∈ B := mem_sprinklingTargetBoundary _ _ hcand hy
  obtain ⟨wl, hwl⟩ := (show BoundedIntrinsicConnection Gₗ a x
      (intrinsicBoundaryRadius Gₗ a A : ℝ) from
    ⟨hleft, by
      change (Gₗ.dist a x : ℝ) ≤ _
      rw [SimpleGraph.dist_comm]
      exact_mod_cast dist_le_intrinsicBoundaryRadius Gₗ a A hx hleft⟩).exists_walk
  obtain ⟨wr, hwr⟩ := (show BoundedIntrinsicConnection Gᵣ b y
      (intrinsicBoundaryRadius Gᵣ b B : ℝ) from
    ⟨hright, by
      change (Gᵣ.dist b y : ℝ) ≤ _
      rw [SimpleGraph.dist_comm]
      exact_mod_cast dist_le_intrinsicBoundaryRadius Gᵣ b B hyB hright⟩).exists_walk
  let H := microscopicPieceGraph Ω D (exploredEdgeSet Q₁ F₁ ∪ exploredEdgeSet Q₃ F₃)ᶜ
  have hmono : ∀ e, ω e = true → Ω e = true := by
    intro e h
    change (ω e || η e) = true
    simp [h]
  have hGL : Gₗ ≤ microscopicPieceGraph Ω L (exploredEdgeSet Q₁ F₁)ᶜ :=
    sprinklingUnexploredGraph_mono hmono _ _ _
  have hGR : Gᵣ ≤ microscopicPieceGraph Ω R (exploredEdgeSet Q₃ F₃)ᶜ :=
    sprinklingUnexploredGraph_mono hmono _ _ _
  have hL : Gₗ ≤ H := hGL.trans (microscopicPieceGraph_avoid_opposite hLD hLQ)
  have hR : Gᵣ ≤ H := hGR.trans (by
    simpa only [H, Set.union_comm] using
      (microscopicPieceGraph_avoid_opposite (ω := Ω) (Q₁ := (Q₃ : Set (Vertex d)))
        (F₁ := (F₃ : Set (Vertex d))) (Q₂ := (Q₁ : Set (Vertex d)))
        (F₂ := (F₁ : Set (Vertex d))) hRD hRQ))
  have hP : H.Adj a b := by
    refine ⟨hopen, hLD ha, hRD hb, ?_⟩
    rintro (h | h)
    · exact Set.disjoint_left.mp hRQ hb ((pair_mem_exploredEdgeSet _ _ _ _).mp h).2.1
    · exact Set.disjoint_left.mp hLQ ha ((pair_mem_exploredEdgeSet _ _ _ _).mp h).1
  let raw : H.Walk x y := ((wl.reverse.mapLe hL).concat hP).append (wr.mapLe hR)
  have hgraph : H ≤ restrictedGraph Ω D := fun _ _ h => ⟨h.1, h.2.1, h.2.2.1⟩
  let walk := raw.mapLe hgraph
  refine ⟨x, hx, y, hy, walk, ?_, ?_, ?_⟩
  · have hsum : (intrinsicBoundaryRadius Gₗ a A : ℝ) + 1 + intrinsicBoundaryRadius Gᵣ b B ≤ K := by
      refine le_trans ?_ hdiam
      exact_mod_cast sprinklingIntrinsicDiameter_join_bound Gₗ Gᵣ A B P he
    have hlen : (walk.length : ℝ) = (wl.length : ℝ) + 1 + wr.length := by
      simp only [walk, raw, SimpleGraph.Walk.length_mapLe, SimpleGraph.Walk.length_append,
        SimpleGraph.Walk.length_concat, SimpleGraph.Walk.length_reverse, Nat.cast_add, Nat.cast_one]
    rw [hlen]
    linarith
  · intro v hv
    have hparts : (v ∈ wl.support ∨ v = b) ∨ v ∈ wr.support := by
      simpa only [walk, raw, SimpleGraph.Walk.support_mapLe_eq_support,
        SimpleGraph.Walk.mem_support_append_iff, SimpleGraph.Walk.support_concat,
        SimpleGraph.Walk.support_reverse, List.mem_append, List.mem_singleton, List.mem_reverse] using hv
    apply (mem_section9SprinklingCluster ω Ω E L R Q₁ F₁ Q₃ F₃ Aall B v).mpr
    refine ⟨(a,b), he, ?_⟩
    rcases hparts with (h | rfl) | h
    · exact Or.inl ((mem_sprinklingUnexploredCluster ω L Q₁ F₁ a v).mpr
        ⟨microscopicWalk_support wl ha v h, ⟨wl.takeUntil v h⟩⟩)
    · exact Or.inr (root_mem_sprinklingUnexploredCluster ω R Q₃ F₃ hb)
    · exact Or.inr ((mem_sprinklingUnexploredCluster ω R Q₃ F₃ b v).mpr
        ⟨microscopicWalk_support wr hb v h, ⟨wr.takeUntil v h⟩⟩)
  · intro e he
    have he' : e ∈ raw.edges := by
      simpa only [walk, SimpleGraph.Walk.edges_mapLe_eq_edges] using he
    exact microscopicWalk_edges raw e he'

end NearCritical.Section10
