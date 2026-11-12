module

public import NearCritical.SplitCrossIndexTree

/-! The two child slots at each branch give a concrete assignment of the
three lattice rays: one toward the parent and one for each child. -/
@[expose] public section
noncomputable section

namespace NearCritical.SplitCrossDirect.SplitTreeNode

def childSlot {L : ℕ} : SplitTreeNode L → Bool
  | root | spine _ | exterior _ | exteriorDummy _ => false
  | entry leg => decide (leg.val ≠ L - 1)
  | cubeDummy _ | face _ => true

def childAt {L : ℕ} (hL : 2 ≤ L) : SplitTreeNode L → Bool → Option (SplitTreeNode L)
  | root, false => some (spine ⟨0, by omega⟩)
  | root, true => none
  | spine k, false =>
    if hk : k.val + 1 < L - 1 then some (spine ⟨k.val + 1, hk⟩)
    else some (entry ⟨L - 1, by omega⟩)
  | spine k, true => some (entry ⟨k.val, by have := k.isLt; omega⟩)
  | entry leg, false => some (exterior leg)
  | entry leg, true => some (cubeDummy leg)
  | exterior leg, false => some (exteriorDummy leg)
  | exterior leg, true => some (face leg)
  | cubeDummy _, _ | exteriorDummy _, _ | face _, _ => none

theorem childAt_parent_slot {L : ℕ} (hL : 2 ≤ L) (v : SplitTreeNode L) (hv : v ≠ root) :
    childAt hL (parent hL v) (childSlot v) = some v := by
  cases v with
  | root => exact (hv rfl).elim
  | spine k =>
    by_cases hk : k.val = 0
    · simp [parent, childAt, childSlot, hk, Fin.ext_iff]
    · have hprev : k.val - 1 + 1 = k.val := by omega
      simp [parent, childAt, childSlot, hk, hprev]
  | entry leg =>
    by_cases hlast : leg.val = L - 1
    · have hmin : min (L - 1) (L - 2) = L - 2 := by omega
      have hnext : ¬(L - 2 + 1 < L - 1) := by omega
      simp [parent, childAt, childSlot, hlast, hmin, hnext]
      exact Fin.ext hlast.symm
    · have hmin : min leg.val (L - 2) = leg.val := by have := leg.isLt; omega
      simp [parent, childAt, childSlot, hlast, hmin]
  | exterior _ | cubeDummy _ | exteriorDummy _ | face _ => rfl

theorem same_parent_same_slot_eq {L : ℕ} (hL : 2 ≤ L) {u v : SplitTreeNode L}
    (hu : u ≠ root) (hv : v ≠ root) (hp : parent hL u = parent hL v)
    (hs : childSlot u = childSlot v) : u = v := by
  apply Option.some.inj
  rw [← childAt_parent_slot hL u hu, hp, hs, childAt_parent_slot hL v hv]

end NearCritical.SplitCrossDirect.SplitTreeNode
