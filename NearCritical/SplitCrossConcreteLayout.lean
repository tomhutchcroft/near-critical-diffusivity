module

public import NearCritical.SplitCrossBranchSides
public import NearCritical.SplitCrossDirectLayout
public import NearCritical.SplitCrossTreeRealization

/-! A port of the concrete crossing tree is either its root, a branch tip,
or a terminal. Each tube region depends only on the child node of its edge. -/
@[expose] public section
noncomputable section

namespace NearCritical.SplitCrossDirect

open SplitTreeNode
open scoped Classical

abbrev CrossingBranch (L : ℕ) := {v : SplitTreeNode L // isCrossingBranch v = true}
abbrev CrossingTerminal (L : ℕ) := {v : SplitTreeNode L // isCrossingTerminal v = true}
abbrev CrossingPort (L : ℕ) := Port (CrossingBranch L) (CrossingTerminal L)

def crossingPortNode {L : ℕ} : CrossingPort L → SplitTreeNode L
  | .root => root
  | .tip v _ => v.val
  | .term v => v.val

def crossingPortAt {L : ℕ} (v : SplitTreeNode L) (j : Fin 3) : CrossingPort L :=
  if hv : isCrossingBranch v = true then .tip ⟨v, hv⟩ j
  else if ht : isCrossingTerminal v = true then .term ⟨v, ht⟩
  else .root

@[simp] theorem crossingPortNode_portAt {L : ℕ} (v : SplitTreeNode L) (j : Fin 3) :
    crossingPortNode (crossingPortAt v j) = v := by
  cases v <;> simp [crossingPortAt, crossingPortNode, isCrossingBranch, isCrossingTerminal]

@[simp] theorem crossingPortAt_root {L : ℕ} (j : Fin 3) :
    crossingPortAt (root : SplitTreeNode L) j = .root := by
  simp [crossingPortAt, isCrossingBranch, isCrossingTerminal]

theorem crossingPortAt_branch {L : ℕ} (v : CrossingBranch L) (j : Fin 3) :
    crossingPortAt v.val j = .tip v j := by
  simp [crossingPortAt, v.property]

theorem crossingPortAt_terminal {L : ℕ} (v : CrossingTerminal L) (j : Fin 3) :
    crossingPortAt v.val j = .term v := by
  have h : ¬isCrossingBranch v.val = true := by
    obtain ⟨v, hv⟩ := v
    cases v <;> simp [isCrossingBranch, isCrossingTerminal] at hv ⊢
  simp [crossingPortAt, h, v.property]

def crossingPortAxis {d : ℕ} (hd : 3 ≤ d) (j : Fin 3) : Fin d :=
  ⟨j.val, j.isLt.trans_le hd⟩

def childPortSlot (s : Bool) : Fin 3 := if s then 2 else 1

@[simp] theorem crossingPortAxis_zero {d : ℕ} (hd : 3 ≤ d) :
    crossingPortAxis hd 0 = parentAxis hd := rfl

@[simp] theorem crossingPortAxis_child {d : ℕ} (hd : 3 ≤ d) (s : Bool) :
    crossingPortAxis hd (childPortSlot s) = childAxis hd s := by
  cases s <;> rfl

def crossingPortEdge {L : ℕ} (hL : 2 ≤ L) (v : SplitTreeNode L) :
    CrossingPort L × CrossingPort L :=
  (crossingPortAt (parent hL v) (childPortSlot (childSlot v)), crossingPortAt v 0)

@[simp] theorem crossingPortNode_edge_fst {L : ℕ} (hL : 2 ≤ L) (v : SplitTreeNode L) :
    crossingPortNode (crossingPortEdge hL v).1 = parent hL v :=
  crossingPortNode_portAt _ _

@[simp] theorem crossingPortNode_edge_snd {L : ℕ} (hL : 2 ≤ L) (v : SplitTreeNode L) :
    crossingPortNode (crossingPortEdge hL v).2 = v :=
  crossingPortNode_portAt _ _

def concreteCrossingLayout {d : ℕ} (hd : 3 ≤ d) (hL : 2 ≤ 4 * d)
    (t : ℕ) (x : Vertex d) (R : ℕ) :
    Layout d (CrossingBranch (4 * d)) (CrossingTerminal (4 * d)) where
  Λ := splitEnvelope d t
  x := x
  ax := crossingPortAxis hd
  R := R + 1
  edges := ((Finset.univ.erase (root : SplitTreeNode (4 * d))).attach.toList).map
    (fun v => crossingPortEdge hL v.val)
  tube := fun e => crossingEdgeRegion t (crossingPortNode e.2)

theorem mem_concreteCrossingLayout_edges {d : ℕ} (hd : 3 ≤ d) (hL : 2 ≤ 4 * d)
    (t : ℕ) (x : Vertex d) (R : ℕ)
    (e : CrossingPort (4 * d) × CrossingPort (4 * d)) :
    e ∈ (concreteCrossingLayout hd hL t x R).edges ↔
      ∃ v : SplitTreeNode (4 * d), v ≠ root ∧ crossingPortEdge hL v = e := by
  change e ∈ List.map _ _ ↔ _
  constructor
  · intro he
    obtain ⟨v, _, rfl⟩ := List.mem_map.mp he
    exact ⟨v.val, (Finset.mem_erase.mp v.property).1, rfl⟩
  · rintro ⟨v, hv, rfl⟩
    have hmem : v ∈ (Finset.univ.erase root : Finset (SplitTreeNode (4 * d))) := by simp [hv]
    exact List.mem_map.mpr ⟨⟨v, hmem⟩, by simp, rfl⟩

theorem rayPt_eq_starTip {d : ℕ} (b : Vertex d) (i : Fin d) (n : ℕ) :
    rayPt b i n = starTip b i n := by
  ext j
  rw [rayPt_apply]
  by_cases h : j = i <;> simp [starTip, coordinateRay, h]

theorem concreteCrossingLayout_pos {d : ℕ} (hd : 3 ≤ d) (hL : 2 ≤ 4 * d)
    (t : ℕ) (x : Vertex d) (R : ℕ) (b : SplitTreeNode (4 * d) → Vertex d)
    (hx : b root = x) (v : SplitTreeNode (4 * d)) (j : Fin 3) :
    (concreteCrossingLayout hd hL t x R).pos (fun v => b v.val) (fun v => b v.val)
      (crossingPortAt v j) =
      crossingTip b v (crossingPortAxis hd j) (R + 1) := by
  cases v <;>
    simp [crossingPortAt, Layout.pos, concreteCrossingLayout, crossingTip, isCrossingBranch,
      isCrossingTerminal, rayPt_eq_starTip, hx]

end NearCritical.SplitCrossDirect
