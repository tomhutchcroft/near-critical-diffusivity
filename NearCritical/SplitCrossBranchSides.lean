module

public import NearCritical.SplitCrossCorridorStars

/-! After deleting a branch, the root and two terminal nodes witness all
three sides of the index tree. Sides can be read from the parent pointers. -/
@[expose] public section
noncomputable section

namespace NearCritical.SplitCrossDirect

open SplitTreeNode

def isCrossingTerminal {L : ℕ} : SplitTreeNode L → Bool
  | cubeDummy _ | exteriorDummy _ | face _ => true
  | _ => false

/-- `none` denotes the root side, and `some s` the subtree of child slot `s`. -/
def crossingSide {L : ℕ} (hL : 2 ≤ L) (cut v : SplitTreeNode L) : Option Bool :=
  if hv : v = root then none
  else if parent hL v = cut then some (childSlot v)
  else crossingSide hL cut (parent hL v)
termination_by rank v
decreasing_by exact parent_rank_lt hL v hv

@[simp] theorem crossingSide_root {L : ℕ} (hL : 2 ≤ L) (cut : SplitTreeNode L) :
    crossingSide hL cut root = none := by
  rw [crossingSide, dif_pos rfl]

theorem crossingSide_of_parent_eq {L : ℕ} (hL : 2 ≤ L) {cut v : SplitTreeNode L}
    (hv : v ≠ root) (hp : parent hL v = cut) :
    crossingSide hL cut v = some (childSlot v) := by
  rw [crossingSide, dif_neg hv, if_pos hp]

theorem crossingSide_of_parent_ne {L : ℕ} (hL : 2 ≤ L) {cut v : SplitTreeNode L}
    (hv : v ≠ root) (hp : parent hL v ≠ cut) :
    crossingSide hL cut v = crossingSide hL cut (parent hL v) := by
  conv_lhs => rw [crossingSide]
  rw [dif_neg hv, if_neg hp]

private theorem later_spine_side {L : ℕ} (hL : 2 ≤ L) (k : Fin (L - 1)) :
    ∀ j : Fin (L - 1), k.val < j.val → crossingSide hL (spine k) (spine j) = some false := by
  have h : ∀ n (j : Fin (L - 1)), j.val = n → k.val < j.val →
      crossingSide hL (spine k) (spine j) = some false := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro j hj hkj
      have hj0 : j.val ≠ 0 := by omega
      let p : Fin (L - 1) := ⟨j.val - 1, by have := j.isLt; omega⟩
      have hp : parent hL (spine j) = spine p := by simp [parent, p, hj0]
      by_cases hpk : p = k
      · exact crossingSide_of_parent_eq hL (v := spine j) (by simp)
          (by simpa [hpk] using hp)
      · have hpkv : p.val ≠ k.val := fun he => hpk (Fin.ext he)
        have hlt : p.val < n := by dsimp [p]; omega
        have hklt : k.val < p.val := by dsimp [p] at hpkv ⊢; omega
        rw [crossingSide_of_parent_ne hL (v := spine j) (cut := spine k) (by simp)
          (by simpa [hp] using hpk), hp]
        exact ih p.val hlt p rfl hklt
  exact fun j hj => h j.val j rfl hj

/-- The two downward sides of a branch both reach terminals, one in each
child slot. Together with the root these give three fixed witnesses. -/
theorem crossingSide_terminal_witnesses {L : ℕ} (hL : 2 ≤ L) (cut : SplitTreeNode L)
    (hc : isCrossingBranch cut = true) :
    ∃ u v : SplitTreeNode L, isCrossingTerminal u = true ∧ isCrossingTerminal v = true ∧
      crossingSide hL cut u = some false ∧ crossingSide hL cut v = some true := by
  cases cut with
  | root | cubeDummy _ | exteriorDummy _ | face _ => simp [isCrossingBranch] at hc
  | entry k =>
    refine ⟨exteriorDummy k, cubeDummy k, rfl, rfl, ?_, ?_⟩
    · rw [crossingSide_of_parent_ne hL (v := exteriorDummy k) (cut := entry k)
        (by simp) (by simp [parent])]
      exact crossingSide_of_parent_eq hL (v := exterior k) (by simp) rfl
    · exact crossingSide_of_parent_eq hL (by simp) rfl
  | exterior k =>
    exact ⟨exteriorDummy k, face k, rfl, rfl,
      crossingSide_of_parent_eq hL (by simp) rfl, crossingSide_of_parent_eq hL (by simp) rfl⟩
  | spine k =>
    let last : Fin L := ⟨L - 1, by omega⟩
    let here : Fin L := ⟨k.val, by have := k.isLt; omega⟩
    let stop : Fin (L - 1) := ⟨L - 2, by omega⟩
    have hpLast : parent hL (entry last) = spine stop := by
      have hle : L - 2 ≤ L - 1 := by omega
      simp [parent, last, stop, min_eq_right hle]
    have hpHere : parent hL (entry here) = spine k := by
      have hle : k.val ≤ L - 2 := by have := k.isLt; omega
      simp [parent, here, min_eq_left hle]
    refine ⟨cubeDummy last, cubeDummy here, rfl, rfl, ?_, ?_⟩
    · rw [crossingSide_of_parent_ne hL (v := cubeDummy last) (cut := spine k)
        (by simp) (by simp [parent])]
      change crossingSide hL (spine k) (entry last) = _
      by_cases hstop : stop = k
      · rw [crossingSide_of_parent_eq hL (v := entry last) (cut := spine k) (by simp)
          (by simpa [hstop] using hpLast)]
        simp [childSlot, last]
      · have hlt : k.val < stop.val := by
          have hne : k.val ≠ stop.val := fun he => hstop (Fin.ext he.symm)
          have hk := k.isLt
          dsimp [stop] at hne ⊢
          omega
        rw [crossingSide_of_parent_ne hL (v := entry last) (cut := spine k) (by simp)
          (by simpa [hpLast] using hstop), hpLast]
        exact later_spine_side hL k stop hlt
    · rw [crossingSide_of_parent_ne hL (v := cubeDummy here) (cut := spine k)
        (by simp) (by simp [parent])]
      change crossingSide hL (spine k) (entry here) = _
      rw [crossingSide_of_parent_eq hL (by simp) hpHere]
      have hlt : k.val ≠ L - 1 := by have := k.isLt; omega
      simp [childSlot, here, hlt]

end NearCritical.SplitCrossDirect
