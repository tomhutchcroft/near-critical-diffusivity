module

public import NearCritical.Events
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.DeleteEdges

/-! Deterministic overcount (item E of the direct proof of `SplitCrossInput`),
abstract graph-theoretic core.

`G` is the open graph of a configuration, `F` a set of edges (the star of a
second realised tuple at one node).

* From the FIRST tuple: an index graph `T` (the tree on root, nodes and
  terminals; only connectedness is used), representatives `r : I → V`, and one
  exceptional index edge `e₀` (the tree edge whose outside-cluster contains
  `F`, if any). If every other tree edge lifts to a connection in `G - F`
  (`hlift`), then among any three indices two have representatives connected
  in `G - F` (`two_of_three_reachable`).
* From the SECOND tuple: a labelling of the vertices constant along the edges
  of `G - F` (`reachable_label_eq`).

`overcount_contradiction`: three indices whose representatives carry pairwise
different labels cannot exist. The concrete lattice instantiation (stars,
moats, outside-clusters, the side labelling) is a later file.
-/
@[expose] public section
namespace NearCritical.SplitCrossDirect

variable {I V : Type*}

/-- In a connected graph, after deleting one edge `s(u,v)` every vertex is
still joined to `u` or to `v`. -/
theorem reachable_endpoint_of_deleteEdge (T : SimpleGraph I) (hT : T.Preconnected) (u v z : I) :
    (T.deleteEdges {s(u, v)}).Reachable z u ∨ (T.deleteEdges {s(u, v)}).Reachable z v := by
  have key : ∀ {a b : I} (p : T.Walk a b),
      ((T.deleteEdges {s(u, v)}).Reachable b u ∨ (T.deleteEdges {s(u, v)}).Reachable b v) →
      ((T.deleteEdges {s(u, v)}).Reachable a u ∨ (T.deleteEdges {s(u, v)}).Reachable a v) := by
    intro a b p
    induction p with
    | nil => exact fun h => h
    | @cons a c b hac p ih =>
      intro hb
      by_cases he : s(a, c) = s(u, v)
      · rcases Sym2.eq_iff.mp he with ⟨rfl, _⟩ | ⟨rfl, _⟩
        · exact Or.inl (SimpleGraph.Reachable.refl _)
        · exact Or.inr (SimpleGraph.Reachable.refl _)
      · have hadj : (T.deleteEdges {s(u, v)}).Adj a c :=
          (SimpleGraph.deleteEdges_adj).mpr ⟨hac, fun hmem => he (Set.mem_singleton_iff.mp hmem)⟩
        rcases ih hb with h | h
        · exact Or.inl (hadj.reachable.trans h)
        · exact Or.inr (hadj.reachable.trans h)
  obtain ⟨p⟩ := hT z u
  exact key p (Or.inl (SimpleGraph.Reachable.refl _))

/-- Lifting connections of the index graph (minus the exceptional edge) to the
vertex graph. -/
theorem lift_reachable (T : SimpleGraph I) (G' : SimpleGraph V) (r : I → V) (u v : I)
    (hlift : ∀ i j, T.Adj i j → s(i, j) ≠ s(u, v) → G'.Reachable (r i) (r j)) {a b : I}
    (h : (T.deleteEdges {s(u, v)}).Reachable a b) : G'.Reachable (r a) (r b) := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact SimpleGraph.Reachable.refl _
  | @cons a c b hac p ih =>
    obtain ⟨hT, hne⟩ := (SimpleGraph.deleteEdges_adj).mp hac
    exact (hlift a c hT (fun he => hne (Set.mem_singleton_iff.mpr he))).trans ih

/-- Among any three indices, two have representatives joined in `G'`. -/
theorem two_of_three_reachable (T : SimpleGraph I) (hT : T.Preconnected) (G' : SimpleGraph V)
    (r : I → V) (u v : I)
    (hlift : ∀ i j, T.Adj i j → s(i, j) ≠ s(u, v) → G'.Reachable (r i) (r j))
    (i₁ i₂ i₃ : I) :
    G'.Reachable (r i₁) (r i₂) ∨ G'.Reachable (r i₁) (r i₃) ∨ G'.Reachable (r i₂) (r i₃) := by
  have L := fun {a b : I} (h : (T.deleteEdges {s(u, v)}).Reachable a b) =>
    lift_reachable T G' r u v hlift h
  rcases reachable_endpoint_of_deleteEdge T hT u v i₁ with h1 | h1 <;>
  rcases reachable_endpoint_of_deleteEdge T hT u v i₂ with h2 | h2 <;>
  rcases reachable_endpoint_of_deleteEdge T hT u v i₃ with h3 | h3
  · exact Or.inl (L (h1.trans h2.symm))
  · exact Or.inl (L (h1.trans h2.symm))
  · exact Or.inr (Or.inl (L (h1.trans h3.symm)))
  · exact Or.inr (Or.inr (L (h2.trans h3.symm)))
  · exact Or.inr (Or.inr (L (h2.trans h3.symm)))
  · exact Or.inr (Or.inl (L (h1.trans h3.symm)))
  · exact Or.inl (L (h1.trans h2.symm))
  · exact Or.inl (L (h1.trans h2.symm))

/-- A labelling constant along edges is constant along connections. -/
theorem reachable_label_eq {Lab : Type*} (G' : SimpleGraph V) (lab : V → Lab)
    (hlab : ∀ z w, G'.Adj z w → lab z = lab w) {a b : V} (h : G'.Reachable a b) :
    lab a = lab b := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => rfl
  | @cons a c b hac p ih => exact (hlab a c hac).trans ih

/-- **Overcount core.** The two structures are incompatible. -/
theorem overcount_contradiction {Lab : Type*} (T : SimpleGraph I) (hT : T.Preconnected)
    (G' : SimpleGraph V) (r : I → V) (u v : I)
    (hlift : ∀ i j, T.Adj i j → s(i, j) ≠ s(u, v) → G'.Reachable (r i) (r j))
    (lab : V → Lab) (hlab : ∀ z w, G'.Adj z w → lab z = lab w) (i₁ i₂ i₃ : I)
    (h12 : lab (r i₁) ≠ lab (r i₂)) (h13 : lab (r i₁) ≠ lab (r i₃))
    (h23 : lab (r i₂) ≠ lab (r i₃)) : False := by
  rcases two_of_three_reachable T hT G' r u v hlift i₁ i₂ i₃ with h | h | h
  · exact h12 (reachable_label_eq G' lab hlab h)
  · exact h13 (reachable_label_eq G' lab hlab h)
  · exact h23 (reachable_label_eq G' lab hlab h)

end NearCritical.SplitCrossDirect
