module

public import NearCritical.SplitCrossNodeSites
public import NearCritical.SplitCrossLegSeparation

/-! Distinct tree nodes are separated at a scale proportional to the box side. -/
@[expose] public section
noncomputable section

namespace NearCritical.SplitCrossDirect

open Section10 SplitTreeNode
open scoped Classical

private inductive CubePlacement {d : ℕ} (t : ℕ) (x : Vertex d) (axis : Fin d) :
    SplitTreeNode (4 * d) → Vertex d → Prop
  | atRoot : CubePlacement t x axis root x
  | atSpine {z} (k) : z ∈ spineBox t axis k → CubePlacement t x axis (spine k) z
  | atLeg {z} (k : Fin (4 * d)) (s : Bool) :
      z ∈ entryLegBox t (splitLegEquiv d k).1 (splitLegEquiv d k).2 s →
      CubePlacement t x axis (if s then entry k else cubeDummy k) z

private inductive LegPlacement {d : ℕ} (t : ℕ) :
    SplitTreeNode (4 * d) → Vertex d → Fin (4 * d) → Prop
  | atBranch {z} (k : Fin (4 * d)) :
      z ∈ legBranchBox t (splitLegEquiv d k).1 (splitLegEquiv d k).2 false →
      LegPlacement t (exterior k) z k
  | atDummy {z} (k : Fin (4 * d)) :
      z ∈ translateSites (interiorLegBoxCenter t (splitLegEquiv d k).1 (splitLegEquiv d k).2)
        (centeredBox d (legBoxRadius t)) → LegPlacement t (exteriorDummy k) z k
  | atFace {z} (k : Fin (4 * d)) :
      z ∈ farLegFaceCore t (splitLegEquiv d k).1 (splitLegEquiv d k).2 →
      LegPlacement t (face k) z k

private theorem placement_cases {d t : ℕ} {x z : Vertex d} {axis : Fin d}
    {v : SplitTreeNode (4 * d)} (hz : z ∈ nodeSites t x axis v) :
    CubePlacement t x axis v z ∨ ∃ k, LegPlacement t v z k := by
  cases v with
  | root =>
    have heq : z = x := Finset.mem_singleton.mp hz
    subst z
    exact Or.inl .atRoot
  | spine k => exact Or.inl (.atSpine k (spineBranchCore_subset_spine t axis k hz))
  | entry k => exact Or.inl (.atLeg k true (legBranchCore_inside_subset_entry t _ _ hz))
  | cubeDummy k => exact Or.inl (.atLeg k false hz)
  | exterior k => exact Or.inr ⟨k, .atBranch k (legBranchCore_subset_branch t _ _ false hz)⟩
  | exteriorDummy k => exact Or.inr ⟨k, .atDummy k hz⟩
  | face k => exact Or.inr ⟨k, .atFace k hz⟩

private theorem CubePlacement.mem_inner {d t : ℕ} (ht : 64 ≤ t)
    {x z : Vertex d} (hx : x ∈ centeredBox d ((t - 1) / 32)) {axis : Fin d}
    {v : SplitTreeNode (4 * d)} (h : CubePlacement t x axis v z) :
    z ∈ centeredBox d (7 * t / 16) := by
  cases h with
  | atRoot => exact root_mem_innerCube hx
  | atSpine k h =>
    apply mem_centeredBox.mpr
    intro j
    have hj := mem_centeredBox.mp (spineBox_subset_inner_cube ht axis k h) j
    omega
  | atLeg k s h => exact entryLegBox_subset_inner_cube ht _ _ s h

private theorem farBox_mem_of_branchBox {d t : ℕ} {f : Fin d × Bool} {s : Bool}
    {z : Vertex d} (hz : z ∈ legBranchBox t f s false) :
    z ∈ translateSites (farLegBoxCenter t f s) (centeredBox d (legBoxRadius t)) := by
  have hhalf := legBranchBox_exterior_subset_halfBox f s hz
  have hzero : (0 : Vertex d) ∈ centeredBox d 0 := by simp [mem_centeredBox]
  simpa using translatedBox_add_mem (by omega : legBoxRadius t / 2 + 0 ≤ legBoxRadius t)
    hhalf hzero

private theorem LegPlacement.mem_beyond {d t : ℕ} (ht : 64 ≤ t)
    {z : Vertex d} {v : SplitTreeNode (4 * d)} {k : Fin (4 * d)}
    (h : LegPlacement t v z k) :
    z ∈ splitBeyond t (splitLegEquiv d k).1 (splitLegEquiv d k).2 t := by
  cases h with
  | atBranch k h => exact farLegBox_subset_beyond ht _ _ (farBox_mem_of_branchBox h)
  | atDummy k h => exact interiorLegBox_subset_beyond ht _ _ h
  | atFace k h => exact farLegBox_subset_beyond ht _ _ (farLegFaceCore_subset_farBox t _ _ h)

private theorem cube_placements_dist {d t : ℕ} (hd : 2 ≤ d) (ht : 128 ≤ t)
    {x a b : Vertex d} (hx : x ∈ centeredBox d ((t - 1) / 32)) {axis : Fin d}
    {u v : SplitTreeNode (4 * d)} (hne : u ≠ v)
    (ha : CubePlacement t x axis u a) (hb : CubePlacement t x axis v b) {s : ℝ}
    (hs : s ≤ ((t / 128 : ℕ) : ℝ)) (hsp : s ≤ (spineRadius (4 * d - 1) t : ℝ)) :
    s ≤ dist a b := by
  have h64 : s ≤ ((t / 64 : ℕ) : ℝ) := hs.trans (by exact_mod_cast (show t / 128 ≤ t / 64 by omega))
  have h16 : s ≤ ((t / 16 : ℕ) : ℝ) := hs.trans (by exact_mod_cast (show t / 128 ≤ t / 16 by omega))
  have h8 : s ≤ ((t / 8 : ℕ) : ℝ) := hs.trans (by exact_mod_cast (show t / 128 ≤ t / 8 by omega))
  cases ha with
  | atRoot =>
    cases hb with
    | atRoot => exact (hne rfl).elim
    | atSpine j hb => exact h64.trans (spineBox_dist_root (by omega) axis j hx hb)
    | atLeg l sl hb => exact h8.trans (entryLegBox_dist_root (by omega) hx hb)
  | atSpine k ha =>
    cases hb with
    | atRoot =>
      rw [dist_comm]
      exact h64.trans (spineBox_dist_root (by omega) axis k hx ha)
    | atSpine j hb =>
      have hk : k ≠ j := fun h => hne (congrArg spine h)
      have hs2 : s ≤ 2 * (spineRadius (4 * d - 1) t : ℝ) := by
        have hn : (0 : ℝ) ≤ spineRadius (4 * d - 1) t := by positivity
        linarith
      rcases lt_or_gt_of_ne hk with hk | hk
      · exact hs2.trans (spineBoxes_dist_of_lt axis hk ha hb)
      · rw [dist_comm]
        exact hs2.trans (spineBoxes_dist_of_lt axis hk hb ha)
    | atLeg l sl hb => exact h16.trans (spineBox_dist_entryBox (by omega) axis k ha hb)
  | atLeg k sk ha =>
    cases hb with
    | atRoot =>
      rw [dist_comm]
      exact h8.trans (entryLegBox_dist_root (by omega) hx ha)
    | atSpine j hb =>
      rw [dist_comm]
      exact h16.trans (spineBox_dist_entryBox (by omega) axis j hb ha)
    | atLeg l sl hb =>
      apply h64.trans (entryLegBoxes_separated hd ht ?_ ha hb)
      intro he
      obtain ⟨hface, hrest⟩ := Prod.mk.inj he
      obtain ⟨hhalf, hsl⟩ := Prod.mk.inj hrest
      have hkl : k = l := (splitLegEquiv d).injective (Prod.ext hface hhalf)
      exact hne (by rw [hkl, hsl])

private theorem leg_placements_dist {d t : ℕ} (hd : 2 ≤ d) (ht : 4096 ≤ t)
    {a b : Vertex d} {u v : SplitTreeNode (4 * d)} (hne : u ≠ v)
    {k l : Fin (4 * d)} (ha : LegPlacement t u a k) (hb : LegPlacement t v b l)
    {s : ℝ} (hs : s ≤ ((t / 128 : ℕ) : ℝ)) :
    s ≤ dist a b := by
  have h8 : s ≤ ((t / 8 : ℕ) : ℝ) := hs.trans (by exact_mod_cast (show t / 128 ≤ t / 8 by omega))
  have h4 : s ≤ ((t / 4 : ℕ) : ℝ) := hs.trans (by exact_mod_cast (show t / 128 ≤ t / 4 by omega))
  have h128 : s ≤ (t : ℝ) / 128 :=
    hs.trans (Nat.cast_div_le (α := ℝ) (m := t) (n := 128))
  have ht64 : 64 ≤ t := by omega
  by_cases hkl : k = l
  · subst l
    cases ha with
    | atBranch k ha =>
      cases hb with
      | atBranch _ hb => exact (hne rfl).elim
      | atDummy _ hb =>
        rw [dist_comm]
        exact h4.trans (exteriorBoxes_dist ht64 hb (farBox_mem_of_branchBox ha))
      | atFace _ hb =>
        exact h128.trans (exteriorBranch_dist_target ht ha (farLegFaceCore_subset_target ht64 _ _ hb))
    | atDummy k ha =>
      cases hb with
      | atBranch _ hb => exact h4.trans (exteriorBoxes_dist ht64 ha (farBox_mem_of_branchBox hb))
      | atDummy _ hb => exact (hne rfl).elim
      | atFace _ hb => exact h4.trans (exteriorBoxes_dist ht64 ha (farLegFaceCore_subset_farBox t _ _ hb))
    | atFace k ha =>
      cases hb with
      | atBranch _ hb =>
        rw [dist_comm]
        exact h128.trans (exteriorBranch_dist_target ht hb (farLegFaceCore_subset_target ht64 _ _ ha))
      | atDummy _ hb =>
        rw [dist_comm]
        exact h4.trans (exteriorBoxes_dist ht64 hb (farLegFaceCore_subset_farBox t _ _ ha))
      | atFace _ hb => exact (hne rfl).elim
  · exact h8.trans (splitBeyond_separated hd ht64
      (fun h => hkl ((splitLegEquiv d).injective h))
      (ha.mem_beyond ht64) (hb.mem_beyond ht64))

theorem nodeSites_dist_of_ne {d t : ℕ} (hd : 2 ≤ d) (ht : 4096 ≤ t) {x : Vertex d}
    (hx : x ∈ centeredBox d ((t - 1) / 32)) (axis : Fin d)
    {u v : SplitTreeNode (4 * d)} (hne : u ≠ v) {a b : Vertex d}
    (ha : a ∈ nodeSites t x axis u) (hb : b ∈ nodeSites t x axis v) :
    (spineRadius (4 * d - 1) t : ℝ) ≤ dist a b := by
  have hN : spineRadius (4 * d - 1) t ≤ t / 128 := by
    unfold spineRadius
    exact Nat.div_le_div_left (by omega) (by norm_num)
  have hs : (spineRadius (4 * d - 1) t : ℝ) ≤ ((t / 128 : ℕ) : ℝ) := by exact_mod_cast hN
  have h32 : (spineRadius (4 * d - 1) t : ℝ) ≤ ((t / 32 : ℕ) : ℝ) :=
    hs.trans (by exact_mod_cast (show t / 128 ≤ t / 32 by omega))
  rcases placement_cases ha with ha | ⟨k, ha⟩ <;> rcases placement_cases hb with hb | ⟨l, hb⟩
  · exact cube_placements_dist hd (by omega) hx hne ha hb hs le_rfl
  · exact h32.trans (innerCube_splitBeyond_separated (by omega)
      (ha.mem_inner (by omega) hx) (hb.mem_beyond (by omega)))
  · rw [dist_comm]
    exact h32.trans (innerCube_splitBeyond_separated (by omega)
      (hb.mem_inner (by omega) hx) (ha.mem_beyond (by omega)))
  · exact leg_placements_dist hd ht hne ha hb hs

end NearCritical.SplitCrossDirect
