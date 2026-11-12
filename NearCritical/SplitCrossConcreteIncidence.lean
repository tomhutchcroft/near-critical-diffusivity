module

public import NearCritical.SplitCrossConcreteLayout
public import NearCritical.SplitCrossDirectOvercountLattice

/-! The concrete port graph is connected, and every tip is used. Removing
one branch leaves a root port and two terminal ports on the three sides. -/
@[expose] public section
noncomputable section

namespace NearCritical.SplitCrossDirect

open SplitTreeNode SimpleGraph
open scoped Classical

theorem crossingBranch_has_child {L : ℕ} (hL : 2 ≤ L) (v : CrossingBranch L) (s : Bool) :
    ∃ u : SplitTreeNode L, u ≠ root ∧ parent hL u = v.val ∧ childSlot u = s := by
  obtain ⟨v, hv⟩ := v
  cases v with
  | root | cubeDummy _ | exteriorDummy _ | face _ => simp [isCrossingBranch] at hv
  | entry k =>
    cases s
    · exact ⟨exterior k, by simp, rfl, rfl⟩
    · exact ⟨cubeDummy k, by simp, rfl, rfl⟩
  | exterior k =>
    cases s
    · exact ⟨exteriorDummy k, by simp, rfl, rfl⟩
    · exact ⟨face k, by simp, rfl, rfl⟩
  | spine k =>
    cases s
    · by_cases hn : k.val + 1 < L - 1
      · refine ⟨spine ⟨k.val + 1, hn⟩, by simp, ?_, rfl⟩
        simp [parent]
      · let last : Fin L := ⟨L - 1, by omega⟩
        have hk := k.isLt
        have hlast : k.val = L - 2 := by omega
        have hle : L - 2 ≤ L - 1 := by omega
        refine ⟨entry last, by simp, ?_, by simp [childSlot, last]⟩
        simp [parent, last, min_eq_right hle, Fin.ext_iff, hlast]
    · let here : Fin L := ⟨k.val, by have := k.isLt; omega⟩
      have hle : k.val ≤ L - 2 := by have := k.isLt; omega
      have hne : k.val ≠ L - 1 := by have := k.isLt; omega
      exact ⟨entry here, by simp, by simp [parent, here, min_eq_left hle],
        by simp [childSlot, here, hne]⟩

theorem concreteCrossingLayout_tip_edge {d : ℕ} (hd : 3 ≤ d) (hL : 2 ≤ 4 * d)
    (t : ℕ) (x : Vertex d) (R : ℕ) (v : CrossingBranch (4 * d)) (j : Fin 3) :
    ∃ e ∈ (concreteCrossingLayout hd hL t x R).edges, e.1 = Port.tip v j ∨ e.2 = Port.tip v j := by
  have hv : v.val ≠ root := by
    intro h
    have := v.property
    simp [h, isCrossingBranch] at this
  have hchild (s : Bool) :
      ∃ e ∈ (concreteCrossingLayout hd hL t x R).edges, e.1 = Port.tip v (childPortSlot s) := by
    obtain ⟨u, hu, hp, hs⟩ := crossingBranch_has_child hL v s
    refine ⟨crossingPortEdge hL u, (mem_concreteCrossingLayout_edges hd hL t x R _).mpr
      ⟨u, hu, rfl⟩, ?_⟩
    change crossingPortAt (parent hL u) (childPortSlot (childSlot u)) = _
    rw [hp, hs, crossingPortAt_branch]
  fin_cases j
  · exact ⟨crossingPortEdge hL v.val,
      (mem_concreteCrossingLayout_edges hd hL t x R _).mpr ⟨v.val, hv, rfl⟩,
      Or.inr (crossingPortAt_branch v 0)⟩
  · obtain ⟨e, he, hs⟩ := hchild false
    exact ⟨e, he, Or.inl hs⟩
  · obtain ⟨e, he, hs⟩ := hchild true
    exact ⟨e, he, Or.inl hs⟩

private theorem portAt_reachable {d : ℕ} (hd : 3 ≤ d) (hL : 2 ≤ 4 * d)
    (t : ℕ) (x : Vertex d) (R : ℕ) (v : SplitTreeNode (4 * d)) (i j : Fin 3) :
    (concreteCrossingLayout hd hL t x R).portGraph.Reachable
      (crossingPortAt v i) (crossingPortAt v j) := by
  by_cases hb : isCrossingBranch v = true
  · let u : CrossingBranch (4 * d) := ⟨v, hb⟩
    change _root_.SimpleGraph.Reachable _
      (crossingPortAt u.val i) (crossingPortAt u.val j)
    rw [crossingPortAt_branch u, crossingPortAt_branch u]
    by_cases he : (Port.tip u i : CrossingPort (4 * d)) = Port.tip u j
    · rw [he]
    · apply Adj.reachable
      exact ⟨he, Or.inl (Or.inr ⟨u, i, j, rfl, rfl⟩)⟩
  · have he : crossingPortAt v i = crossingPortAt v j := by simp [crossingPortAt, hb]
    rw [he]

theorem concreteCrossingLayout_preconnected {d : ℕ} (hd : 3 ≤ d) (hL : 2 ≤ 4 * d)
    (t : ℕ) (x : Vertex d) (R : ℕ) :
    (concreteCrossingLayout hd hL t x R).portGraph.Preconnected := by
  let G := (concreteCrossingLayout hd hL t x R).portGraph
  have step (v : SplitTreeNode (4 * d)) (hv : v ≠ root) :
      G.Reachable (crossingPortAt (parent hL v) 0) (crossingPortAt v 0) := by
    refine (portAt_reachable hd hL t x R (parent hL v) 0
      (childPortSlot (childSlot v))).trans (Adj.reachable ?_)
    have heq : crossingPortAt (parent hL v) (childPortSlot (childSlot v)) ≠ crossingPortAt v 0 := by
      intro h
      exact (parent_adj hL v hv).ne (by simpa using congrArg crossingPortNode h)
    exact ⟨heq, Or.inl (Or.inl ((mem_concreteCrossingLayout_edges hd hL t x R _).mpr ⟨v, hv, rfl⟩))⟩
  have fromRoot (n : ℕ) (v : SplitTreeNode (4 * d)) (hn : rank v = n) :
      G.Reachable Port.root (crossingPortAt v 0) := by
    induction n using Nat.strong_induction_on generalizing v with
    | h n ih =>
      by_cases hv : v = root
      · subst v
        simp
      · have hlt : rank (parent hL v) < n := hn ▸ parent_rank_lt hL v hv
        exact (ih _ hlt _ rfl).trans (step v hv)
  have allPorts (P : CrossingPort (4 * d)) : G.Reachable Port.root P := by
    cases P with
    | root => exact Reachable.refl _
    | tip v j =>
      rw [← crossingPortAt_branch v j]
      exact (fromRoot _ v.val rfl).trans (portAt_reachable hd hL t x R v.val 0 j)
    | term v =>
      rw [← crossingPortAt_terminal v 0]
      exact fromRoot _ v.val rfl
  exact fun P Q => (allPorts P).symm.trans (allPorts Q)

def crossingSideCode : Option Bool → Fin 3
  | none => 0
  | some false => 1
  | some true => 2

theorem concreteCrossingLayout_side_compatible {d : ℕ} (hd : 3 ≤ d) (hL : 2 ≤ 4 * d)
    (t : ℕ) (x : Vertex d) (R : ℕ) (cut : CrossingBranch (4 * d))
    (e : CrossingPort (4 * d) × CrossingPort (4 * d))
    (he : e ∈ (concreteCrossingLayout hd hL t x R).edges)
    (u : CrossingBranch (4 * d)) (j : Fin 3)
    (hport : e.1 = Port.tip u j ∨ e.2 = Port.tip u j) (hne : u ≠ cut) :
    crossingSideCode (crossingSide hL cut.val (crossingPortNode e.2)) =
      crossingSideCode (crossingSide hL cut.val u.val) := by
  obtain ⟨v, hv, rfl⟩ := (mem_concreteCrossingLayout_edges hd hL t x R e).mp he
  rcases hport with h | h
  · have hp : parent hL v = u.val := by
      have hh := congrArg crossingPortNode h
      rw [crossingPortNode_edge_fst] at hh
      exact hh
    have hpc : parent hL v ≠ cut.val := fun h => hne (Subtype.ext (hp.symm.trans h))
    rw [crossingPortNode_edge_snd, crossingSide_of_parent_ne hL hv hpc, hp]
  · have hp : v = u.val := by
      have hh := congrArg crossingPortNode h
      rw [crossingPortNode_edge_snd] at hh
      exact hh
    rw [crossingPortNode_edge_snd, hp]

theorem concreteCrossingLayout_side_witnesses {d : ℕ} (hd : 3 ≤ d) (hL : 2 ≤ 4 * d)
    (t : ℕ) (x : Vertex d) (R : ℕ) (cut : CrossingBranch (4 * d)) :
    ∃ (P : Fin 3 → CrossingPort (4 * d))
      (E : Fin 3 → CrossingPort (4 * d) × CrossingPort (4 * d)),
      (∀ k, E k ∈ (concreteCrossingLayout hd hL t x R).edges ∧
        ((E k).1 = P k ∨ (E k).2 = P k) ∧
        crossingSideCode (crossingSide hL cut.val (crossingPortNode (E k).2)) = k) ∧
      (∀ k, P k = Port.root ∨ ∃ v, P k = Port.term v) := by
  obtain ⟨u, v, hu, hv, hsu, hsv⟩ := crossingSide_terminal_witnesses hL cut.val cut.property
  have hur : u ≠ root := by intro h; simp [h, isCrossingTerminal] at hu
  have hvr : v ≠ root := by intro h; simp [h, isCrossingTerminal] at hv
  have hcr : root ≠ cut.val := by
    intro h
    have hc := cut.property
    simp [← h, isCrossingBranch] at hc
  let first : SplitTreeNode (4 * d) := spine ⟨0, by omega⟩
  have hfirst : parent hL first = root := by simp [first, parent]
  let P : Fin 3 → CrossingPort (4 * d) := ![Port.root, Port.term ⟨u, hu⟩, Port.term ⟨v, hv⟩]
  let E : Fin 3 → CrossingPort (4 * d) × CrossingPort (4 * d) :=
    ![crossingPortEdge hL first, crossingPortEdge hL u, crossingPortEdge hL v]
  refine ⟨P, E, ?_, ?_⟩
  · intro k
    fin_cases k
    · change crossingPortEdge hL first ∈ _ ∧
        ((crossingPortEdge hL first).1 = Port.root ∨ (crossingPortEdge hL first).2 = Port.root) ∧
        crossingSideCode (crossingSide hL cut.val (crossingPortNode (crossingPortEdge hL first).2)) = 0
      refine ⟨(mem_concreteCrossingLayout_edges hd hL t x R _).mpr
        ⟨first, by simp [first], rfl⟩, Or.inl ?_, ?_⟩
      · change crossingPortAt (parent hL first) (childPortSlot (childSlot first)) = Port.root
        rw [hfirst, crossingPortAt_root]
      · rw [crossingPortNode_edge_snd,
          crossingSide_of_parent_ne hL (v := first) (cut := cut.val)
            (by simp [first]) (by rw [hfirst]; exact hcr), hfirst]
        simp [crossingSideCode]
    · change crossingPortEdge hL u ∈ _ ∧
        ((crossingPortEdge hL u).1 = Port.term ⟨u, hu⟩ ∨ (crossingPortEdge hL u).2 = Port.term ⟨u, hu⟩) ∧
        crossingSideCode (crossingSide hL cut.val (crossingPortNode (crossingPortEdge hL u).2)) = 1
      exact ⟨(mem_concreteCrossingLayout_edges hd hL t x R _).mpr ⟨u, hur, rfl⟩,
        Or.inr (crossingPortAt_terminal ⟨u, hu⟩ 0), by simp [hsu, crossingSideCode]⟩
    · change crossingPortEdge hL v ∈ _ ∧
        ((crossingPortEdge hL v).1 = Port.term ⟨v, hv⟩ ∨ (crossingPortEdge hL v).2 = Port.term ⟨v, hv⟩) ∧
        crossingSideCode (crossingSide hL cut.val (crossingPortNode (crossingPortEdge hL v).2)) = 2
      exact ⟨(mem_concreteCrossingLayout_edges hd hL t x R _).mpr ⟨v, hvr, rfl⟩,
        Or.inr (crossingPortAt_terminal ⟨v, hv⟩ 0), by simp [hsv, crossingSideCode]⟩
  · intro k
    fin_cases k
    · exact Or.inl rfl
    · exact Or.inr ⟨⟨u, hu⟩, rfl⟩
    · exact Or.inr ⟨⟨v, hv⟩, rfl⟩

end NearCritical.SplitCrossDirect
