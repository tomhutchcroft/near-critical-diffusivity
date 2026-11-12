module

public import NearCritical.SplitCrossIndexChildren
public import NearCritical.SplitCrossOutwardGeometry

/-! The three coordinate rays at a branch represent its parent and two children. -/
@[expose] public section
noncomputable section

namespace NearCritical.SplitCrossDirect

open SplitTreeNode
open scoped Classical

def parentAxis {d : ℕ} (hd : 3 ≤ d) : Fin d := ⟨0, by omega⟩

def childAxis {d : ℕ} (hd : 3 ≤ d) (s : Bool) : Fin d :=
  if s then ⟨2, by omega⟩ else ⟨1, by omega⟩

def branchAxes {d : ℕ} (hd : 3 ≤ d) : Finset (Fin d) :=
  {parentAxis hd, childAxis hd false, childAxis hd true}

theorem parentAxis_ne_childAxis {d : ℕ} (hd : 3 ≤ d) (s : Bool) :
    parentAxis hd ≠ childAxis hd s := by
  cases s <;> simp [parentAxis, childAxis, Fin.ext_iff]

theorem childAxis_injective {d : ℕ} (hd : 3 ≤ d) : Function.Injective (childAxis hd) := by
  intro s s' h
  cases s <;> cases s' <;> simp_all [childAxis, Fin.ext_iff]

theorem parentAxis_mem_branchAxes {d : ℕ} (hd : 3 ≤ d) :
    parentAxis hd ∈ branchAxes hd := by simp [branchAxes]

theorem childAxis_mem_branchAxes {d : ℕ} (hd : 3 ≤ d) (s : Bool) :
    childAxis hd s ∈ branchAxes hd := by cases s <;> simp [branchAxes]

theorem branchAxes_card {d : ℕ} (hd : 3 ≤ d) : (branchAxes hd).card = 3 := by
  have hne : childAxis hd false ≠ childAxis hd true := by
    intro h
    have := childAxis_injective hd h
    contradiction
  simp [branchAxes, parentAxis_ne_childAxis, hne]

theorem parent_child_ray_gap {d L : ℕ} (hd : 3 ≤ d) (b : Vertex d) (n : ℕ)
    (u : SplitTreeNode L) :
    (n : ℝ) ≤ latticeDistance
      (starTip b (parentAxis hd) n) (starTip b (childAxis hd (childSlot u)) n) :=
  starTip_other_ray_gap b (parentAxis_ne_childAxis hd _) n n

theorem children_ray_gap {d L : ℕ} (hd : 3 ≤ d) (hL : 2 ≤ L) (b : Vertex d) (n : ℕ)
    {u v : SplitTreeNode L} (hu : u ≠ root) (hv : v ≠ root)
    (hp : parent hL u = parent hL v) (hne : u ≠ v) :
    (n : ℝ) ≤ latticeDistance
      (starTip b (childAxis hd (childSlot u)) n) (starTip b (childAxis hd (childSlot v)) n) := by
  apply starTip_other_ray_gap
  intro h
  exact hne (same_parent_same_slot_eq hL hu hv hp (childAxis_injective hd h))

end NearCritical.SplitCrossDirect
