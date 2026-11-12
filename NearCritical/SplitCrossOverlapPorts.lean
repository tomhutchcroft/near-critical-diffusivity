module

public import NearCritical.SplitCrossConcreteLayout
public import NearCritical.SplitCrossConcreteMoatEstimates

/-! Distinct parent edges use distinct ports, including at a shared branch. -/
@[expose] public section
noncomputable section

namespace NearCritical.SplitCrossDirect

open SplitTreeNode

private theorem childPortSlot_injective : Function.Injective childPortSlot := by
  intro a b h
  cases a <;> cases b <;> simp_all [childPortSlot]

private theorem childPortSlot_ne_zero (s : Bool) : childPortSlot s ≠ 0 := by
  cases s <;> decide

private theorem parent_branch_or_root {L : ℕ} (hL : 2 ≤ L) (v : SplitTreeNode L) :
    parent hL v = root ∨ isCrossingBranch (parent hL v) = true := by
  cases v with
  | root => exact Or.inl rfl
  | spine k =>
    by_cases hk : k.val = 0 <;> simp [parent, hk, isCrossingBranch]
  | entry _ | exterior _ | cubeDummy _ | exteriorDummy _ | face _ => exact Or.inr rfl

private theorem root_child_slot {L : ℕ} (hL : 2 ≤ L) {v : SplitTreeNode L}
    (hv : v ≠ root) (hp : parent hL v = root) : childSlot v = false := by
  have h := childAt_parent_slot hL v hv
  rw [hp] at h
  cases hs : childSlot v
  · rfl
  · simp [childAt, hs] at h

theorem crossingPortEdge_source_injective {L : ℕ} (hL : 2 ≤ L) {u v : SplitTreeNode L}
    (hu : u ≠ root) (hv : v ≠ root)
    (h : (crossingPortEdge hL u).1 = (crossingPortEdge hL v).1) : u = v := by
  have hp : parent hL u = parent hL v := by
    simpa only [crossingPortNode_edge_fst] using congrArg crossingPortNode h
  apply same_parent_same_slot_eq hL hu hv hp
  rcases parent_branch_or_root hL u with hr | hb
  · rw [root_child_slot hL hu hr, root_child_slot hL hv (hp.symm.trans hr)]
  · let w : CrossingBranch L := ⟨parent hL u, hb⟩
    change crossingPortAt (parent hL u) (childPortSlot (childSlot u)) =
      crossingPortAt (parent hL v) (childPortSlot (childSlot v)) at h
    rw [← hp] at h
    change crossingPortAt w.val _ = crossingPortAt w.val _ at h
    rw [crossingPortAt_branch w, crossingPortAt_branch w] at h
    injection h with _ hj
    exact childPortSlot_injective hj

theorem crossingPortEdge_target_injective {L : ℕ} (hL : 2 ≤ L) :
    Function.Injective (fun v : SplitTreeNode L => (crossingPortEdge hL v).2) := by
  intro u v h
  simpa only [crossingPortNode_edge_snd] using congrArg crossingPortNode h

theorem crossingPortEdge_source_ne_target {L : ℕ} (hL : 2 ≤ L) (u v : SplitTreeNode L)
    (hv : v ≠ root) : (crossingPortEdge hL u).1 ≠ (crossingPortEdge hL v).2 := by
  intro h
  have hp : parent hL u = v := by
    simpa only [crossingPortNode_edge_fst, crossingPortNode_edge_snd] using congrArg crossingPortNode h
  rcases parent_branch_or_root hL u with hr | hb
  · exact hv (hp.symm.trans hr)
  · let w : CrossingBranch L := ⟨parent hL u, hb⟩
    change crossingPortAt (parent hL u) (childPortSlot (childSlot u)) =
      crossingPortAt v 0 at h
    rw [← hp] at h
    change crossingPortAt w.val _ = crossingPortAt w.val _ at h
    rw [crossingPortAt_branch w, crossingPortAt_branch w] at h
    injection h with _ hj
    exact childPortSlot_ne_zero _ hj

private def crossingPortIndex {L : ℕ} : CrossingPort L → Fin 3
  | .tip _ j => j
  | _ => 0

private theorem crossingPortAt_node_index {L : ℕ} (P : CrossingPort L) :
    crossingPortAt (crossingPortNode P) (crossingPortIndex P) = P := by
  cases P with
  | root => exact crossingPortAt_root 0
  | tip v j => exact crossingPortAt_branch v j
  | term v => exact crossingPortAt_terminal v 0

private theorem concrete_port_pos_eq {d : ℕ} (hd : 3 ≤ d) (hL : 2 ≤ 4 * d)
    (t : ℕ) (x : Vertex d) (R : ℕ) (b : SplitTreeNode (4 * d) → Vertex d) (hx : b root = x)
    (P : CrossingPort (4 * d)) :
    (concreteCrossingLayout hd hL t x R).pos (fun v => b v.val) (fun v => b v.val) P =
      crossingTip b (crossingPortNode P) (crossingPortAxis hd (crossingPortIndex P)) (R + 1) := by
  conv_lhs => rw [← crossingPortAt_node_index P]
  exact concreteCrossingLayout_pos hd hL t x R b hx _ _

/-- Different ports remain separated even at a common branch. -/
theorem concreteCrossingLayout_distinct_ports_gap {d t : ℕ} (hd : 3 ≤ d) (hL : 2 ≤ 4 * d)
    (ht : 4096 ≤ t) (x : Vertex d) (hx : x ∈ centeredBox d ((t - 1) / 32)) (axis : Fin d) (R : ℕ)
    (hgap : 3 * ((R + 1 : ℕ) : ℝ) ≤ (spineRadius (4 * d - 1) t : ℝ))
    (b : SplitTreeNode (4 * d) → Vertex d) (hb : ∀ v, b v ∈ nodeSites t x axis v)
    (P Q : CrossingPort (4 * d)) (hne : P ≠ Q) :
    let L := concreteCrossingLayout hd hL t x R
    ((R + 1 : ℕ) : ℝ) ≤ latticeDistance
      (L.pos (fun v => b v.val) (fun v => b v.val) P)
      (L.pos (fun v => b v.val) (fun v => b v.val) Q) := by
  intro L
  have hroot : b root = x := Finset.mem_singleton.mp (hb root)
  rw [concrete_port_pos_eq hd hL t x R b hroot, concrete_port_pos_eq hd hL t x R b hroot]
  by_cases hnode : crossingPortNode P = crossingPortNode Q
  · have hb' : crossingPortNode P ∈ crossingBranches (4 * d) := by
      by_contra hn
      apply hne
      rw [← crossingPortAt_node_index P, ← crossingPortAt_node_index Q, ← hnode]
      have hnb : ¬isCrossingBranch (crossingPortNode P) = true :=
        fun h => hn ((mem_crossingBranches _).mpr h)
      simp only [crossingPortAt, dite_eq_right hnb]
    have hj : crossingPortIndex P ≠ crossingPortIndex Q := by
      intro h
      apply hne
      calc
        P = crossingPortAt (crossingPortNode P) (crossingPortIndex P) :=
          (crossingPortAt_node_index P).symm
        _ = crossingPortAt (crossingPortNode Q) (crossingPortIndex Q) := by rw [hnode, h]
        _ = Q := crossingPortAt_node_index Q
    have hax : crossingPortAxis hd (crossingPortIndex P) ≠ crossingPortAxis hd (crossingPortIndex Q) :=
      fun h => hj (Fin.ext (congrArg (fun i : Fin d => i.val) h))
    rw [← hnode]
    simp only [crossingTip, hb', ite_true]
    exact starTip_other_ray_gap _ hax _ _
  · rw [latticeDistance_eq_vertex_dist]
    have h := crossingTips_dist_lower (n := R + 1) (m := R + 1) (by omega : 2 ≤ d) ht
      x hx axis b hb hnode (crossingPortAxis hd (crossingPortIndex P))
      (crossingPortAxis hd (crossingPortIndex Q))
    linarith

/-- Along an edge the two ports belong to different nodes, so their
separation also grows with the box scale. -/
theorem concreteCrossingLayout_edge_gap {d t : ℕ} (hd : 3 ≤ d) (hL : 2 ≤ 4 * d)
    (ht : 4096 ≤ t) (x : Vertex d) (hx : x ∈ centeredBox d ((t - 1) / 32)) (axis : Fin d) (R : ℕ)
    (b : SplitTreeNode (4 * d) → Vertex d) (hb : ∀ v, b v ∈ nodeSites t x axis v)
    (v : SplitTreeNode (4 * d)) (hv : v ≠ root) :
    let L := concreteCrossingLayout hd hL t x R
    let e := crossingPortEdge hL v
    (spineRadius (4 * d - 1) t : ℝ) ≤ 2 * ((R + 1 : ℕ) : ℝ) +
      latticeDistance (L.pos (fun v => b v.val) (fun v => b v.val) e.1)
        (L.pos (fun v => b v.val) (fun v => b v.val) e.2) := by
  intro L e
  have hroot : b root = x := Finset.mem_singleton.mp (hb root)
  rw [concrete_port_pos_eq hd hL t x R b hroot, concrete_port_pos_eq hd hL t x R b hroot,
    latticeDistance_eq_vertex_dist]
  have he1 : crossingPortNode e.1 = parent hL v := crossingPortNode_edge_fst hL v
  have he2 : crossingPortNode e.2 = v := crossingPortNode_edge_snd hL v
  rw [he1, he2]
  have h := crossingTips_dist_lower (n := R + 1) (m := R + 1) (by omega : 2 ≤ d) ht
    x hx axis b hb (parent_adj hL v hv).ne (crossingPortAxis hd (crossingPortIndex e.1))
      (crossingPortAxis hd (crossingPortIndex e.2))
  linarith

end NearCritical.SplitCrossDirect
