module

public import NearCritical.SplitCrossDirectLayout

/-! Crossing walks on the realised event (item C of the direct proof of
`SplitCrossInput`, deterministic part R2).

On `θ ∈ L.Real β y`:
* `Layout.real_edge_conn`: every tree edge is realised in its tube (inside the
  outside domain);
* `Layout.real_arm_open`: every arm bond is open;
* `Layout.Linked C β`: two ports are linked inside a region `C` if they are the
  two ends of an edge whose tube lies in `C`, or two tips of a node whose two
  arms lie in `C`;
* `Layout.real_reachable_of_linked`: ports joined by a chain of links inside
  `C` have positions joined by a `θ`-open walk inside `C`;
* `Layout.real_conn_of_chain`: hence `θ ∈ {x ↔ y s inside C}` for a terminal
  `s` reached from the root by such a chain.
-/
@[expose] public section
noncomputable section
namespace NearCritical.SplitCrossDirect
open MeasureTheory SimpleGraph
open scoped Classical BigOperators

variable {d : ℕ}

namespace Layout

variable {Node Term : Type} [Fintype Node] (L : Layout d Node Term)

theorem real_edge_conn {β : Node → Vertex d} {y : Term → Vertex d}
    {hpos : ∀ e ∈ L.edges, L.pos β y e.1 ∈ L.Uout β} {θ : Configuration d}
    (hθ : θ ∈ L.Real β y hpos) {e : Port Node Term × Port Node Term} (he : e ∈ L.edges) :
    θ ∈ connectionToSetEvent (L.tube e ∩ (L.Uout β : Set (Vertex d)))
      (L.pos β y e.1) {L.pos β y e.2} := by
  have hmem : ({ T := L.tube e ∩ (L.Uout β : Set (Vertex d))
                 hT := Set.inter_subset_right
                 a := L.pos β y e.1
                 b := L.pos β y e.2
                 ha := hpos e he } : TEdge d (L.Uout β)) ∈ L.tedges β y hpos :=
    List.mem_pmap.mpr ⟨e, he, rfl⟩
  exact hθ.2.1 _ (List.mem_map_of_mem hmem)

theorem real_arm_open {β : Node → Vertex d} {y : Term → Vertex d}
    {hpos : ∀ e ∈ L.edges, L.pos β y e.1 ∈ L.Uout β} {θ : Configuration d}
    (hθ : θ ∈ L.Real β y hpos) (v : Node) (j : Fin 3) {k : ℕ} (hk : k < L.R) :
    θ (rayPt (β v) (L.ax j) k, L.ax j) = true := by
  have harm : rayPt (β v) (L.ax j) k ∈ L.Rm β :=
    Finset.mem_biUnion.mpr ⟨v, Finset.mem_univ _, Finset.mem_biUnion.mpr
      ⟨j, Finset.mem_univ _, Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr hk, rfl⟩⟩⟩
  have hst : ((rayPt (β v) (L.ax j) k, L.ax j) : Bond d) ∈ L.St β :=
    Finset.mem_biUnion.mpr ⟨v, Finset.mem_univ _, Finset.mem_biUnion.mpr
      ⟨j, Finset.mem_univ _, Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr hk, rfl⟩⟩⟩
  have h := hθ.1 (rayPt (β v) (L.ax j) k, L.ax j)
    ((mem_touchBonds _ _).mpr (Or.inl harm))
  rw [h]
  exact decide_eq_true hst

/-- Links between ports inside a region `C`. -/
inductive Linked (C : Set (Vertex d)) (β : Node → Vertex d) :
    Port Node Term → Port Node Term → Prop
  | edge (e : Port Node Term × Port Node Term) (he : e ∈ L.edges) (hC : L.tube e ⊆ C) :
      Linked C β e.1 e.2
  | edgeRev (e : Port Node Term × Port Node Term) (he : e ∈ L.edges) (hC : L.tube e ⊆ C) :
      Linked C β e.2 e.1
  | arms (v : Node) (j j' : Fin 3)
      (hj : ∀ k ≤ L.R, rayPt (β v) (L.ax j) k ∈ C)
      (hj' : ∀ k ≤ L.R, rayPt (β v) (L.ax j') k ∈ C) :
      Linked C β (Port.tip v j) (Port.tip v j')

theorem real_reachable_of_link {β : Node → Vertex d} {y : Term → Vertex d}
    {hpos : ∀ e ∈ L.edges, L.pos β y e.1 ∈ L.Uout β} {θ : Configuration d}
    (hθ : θ ∈ L.Real β y hpos) {C : Set (Vertex d)} {P Q : Port Node Term}
    (h : L.Linked C β P Q) :
    (restrictedGraph θ C).Reachable (L.pos β y P) (L.pos β y Q) := by
  cases h with
  | edge e he hC =>
    obtain ⟨_, z, hz, _, hreach⟩ := L.real_edge_conn hθ he
    rw [Set.mem_singleton_iff] at hz
    subst hz
    exact Reachable.mono (restrictedGraph_mono θ (Set.inter_subset_left.trans hC)) hreach
  | edgeRev e he hC =>
    obtain ⟨_, z, hz, _, hreach⟩ := L.real_edge_conn hθ he
    rw [Set.mem_singleton_iff] at hz
    subst hz
    exact (Reachable.mono (restrictedGraph_mono θ (Set.inter_subset_left.trans hC)) hreach).symm
  | arms v j j' hj hj' =>
    have h1 := arm_reachable (ω := θ) (S := C) (β v) (L.ax j) L.R
      (fun k hk => L.real_arm_open hθ v j hk) hj
    have h2 := arm_reachable (ω := θ) (S := C) (β v) (L.ax j') L.R
      (fun k hk => L.real_arm_open hθ v j' hk) hj'
    exact h1.symm.trans h2

theorem real_reachable_of_linked {β : Node → Vertex d} {y : Term → Vertex d}
    {hpos : ∀ e ∈ L.edges, L.pos β y e.1 ∈ L.Uout β} {θ : Configuration d}
    (hθ : θ ∈ L.Real β y hpos) {C : Set (Vertex d)} {P Q : Port Node Term}
    (h : Relation.ReflTransGen (L.Linked C β) P Q) :
    (restrictedGraph θ C).Reachable (L.pos β y P) (L.pos β y Q) := by
  induction h with
  | refl => exact Reachable.refl _
  | tail _ hstep ih => exact ih.trans (L.real_reachable_of_link hθ hstep)

/-- **Crossing on the realised event.** -/
theorem real_conn_of_chain {β : Node → Vertex d} {y : Term → Vertex d}
    {hpos : ∀ e ∈ L.edges, L.pos β y e.1 ∈ L.Uout β} {θ : Configuration d}
    (hθ : θ ∈ L.Real β y hpos) {C : Set (Vertex d)} (hx : L.x ∈ C) (s : Term) (hy : y s ∈ C)
    (h : Relation.ReflTransGen (L.Linked C β) Port.root (Port.term s)) :
    θ ∈ connectionToSetEvent C L.x {y s} :=
  ⟨hx, y s, rfl, hy, L.real_reachable_of_linked hθ h⟩

end Layout

end NearCritical.SplitCrossDirect
end
