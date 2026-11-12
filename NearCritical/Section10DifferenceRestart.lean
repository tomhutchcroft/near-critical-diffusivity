module

public import NearCritical.Section10DifferenceFourier
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Tactic.Positivity
public import Lean.Elab.Tactic.Omega

/-! Exact restart at a finite history split for the Section 10 difference
walk. A first-hit event depends on the prefix, and the fresh continuation
begins at the hit site. In particular suffix time zero is the hit visit. -/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open scoped Classical

/-- Actual paired increment symbols. -/
abbrev DifferenceSymbol (D : ℕ) := Option (Fin D) × Option (Fin D)

/-- A finite paired history, with one paired increment at each index. -/
abbrev DifferenceHistory (D n : ℕ) := Fin n → DifferenceSymbol D

def differenceHistoryWeight {D n : ℕ} (h : DifferenceHistory D n) : ℝ :=
  ∏ j, differenceStepWeight D (h j)

/-- Displacement after the first `t` increments of the finite history. -/
def differenceDisplacement {D n : ℕ} (h : DifferenceHistory D n) (t : ℕ) :
    Fin D → ℤ :=
  ∑ j, if j.val < t then differenceStep D (h j) else 0

/-- A weighted finite history event under the actual increment product. -/
def differenceEventMass (D n : ℕ) (P : DifferenceHistory D n → Prop) : ℝ := by
  classical
  exact ∑ h, if P h then differenceHistoryWeight h else 0

/-- The first visit to B is at r, including r=0 for a start already in B. -/
def differenceFirstHit {D n : ℕ} (B : Finset (Fin D → ℤ)) (x : Fin D → ℤ)
    (h : DifferenceHistory D n) (r : ℕ) : Prop :=
  x + differenceDisplacement h r ∈ B ∧
    ∀ j < r, x + differenceDisplacement h j ∉ B

private theorem historyWeight_nonneg_restart {D n : ℕ} (h : DifferenceHistory D n) :
    0 ≤ differenceHistoryWeight h := by
  unfold differenceHistoryWeight
  apply Finset.prod_nonneg
  intro j _
  unfold differenceStepWeight
  apply mul_nonneg
  · cases (h j).1 <;> simp only [lazyCoordinateWeight] <;> positivity
  · cases (h j).2 <;> simp only [lazyCoordinateWeight] <;> positivity

private def splitHistory {D n m : ℕ} :
    DifferenceHistory D (n+m) ≃ DifferenceHistory D n × DifferenceHistory D m where
  toFun h := (fun i => h (Fin.castAdd m i), fun j => h (Fin.natAdd n j))
  invFun h := Fin.append h.1 h.2
  left_inv h := Fin.append_castAdd_natAdd
  right_inv h := by
    apply Prod.ext <;> funext i <;> simp

private theorem historyWeight_append {D n m : ℕ}
    (a : DifferenceHistory D n) (b : DifferenceHistory D m) :
    differenceHistoryWeight (Fin.append a b) = differenceHistoryWeight a * differenceHistoryWeight b := by
  simp only [differenceHistoryWeight, Fin.prod_univ_add, Fin.append_left, Fin.append_right]

/-- Every displacement at or before the split depends only on the prefix. -/
theorem differenceDisplacement_append_left {D n m : ℕ}
    (a : DifferenceHistory D n) (b : DifferenceHistory D m) {j : ℕ} (hj : j ≤ n) :
    differenceDisplacement (Fin.append a b) j = differenceDisplacement a j := by
  unfold differenceDisplacement
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]
  have hz (i : Fin m) : ¬ n+i.val < j := by
    omega
  simp [hz]

/-- At the split, the continuation starts from the actual terminal
displacement of the prefix. This includes the continuation time zero. -/
theorem differenceDisplacement_append_right {D n m : ℕ}
    (a : DifferenceHistory D n) (b : DifferenceHistory D m) (j : ℕ) :
    differenceDisplacement (Fin.append a b) (n+j) =
      differenceDisplacement a n + differenceDisplacement b j := by
  unfold differenceDisplacement
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]
  have hl (i : Fin n) : i.val < n+j := by
    omega
  have hr (i : Fin m) : (Fin.natAdd n i).val < n+j ↔ i.val < j := by
    change n+i.val < n+j ↔ i.val < j
    omega
  simp [hl, hr, Fin.isLt]

/-- First hit at the splitting time is measurable with respect to the
prefix. The appended increments play no role in deciding the hit. -/
theorem differenceFirstHit_append {D n m : ℕ} (B : Finset (Fin D → ℤ))
    (x : Fin D → ℤ) (a : DifferenceHistory D n) (b : DifferenceHistory D m) :
    differenceFirstHit B x (Fin.append a b) n ↔ differenceFirstHit B x a n := by
  unfold differenceFirstHit
  rw [differenceDisplacement_append_left a b le_rfl]
  constructor
  · rintro ⟨hh,hbefore⟩
    exact ⟨hh,fun j hj => by
      simpa only [differenceDisplacement_append_left a b hj.le] using hbefore j hj⟩
  · rintro ⟨hh,hbefore⟩
    exact ⟨hh,fun j hj => by
      rw [differenceDisplacement_append_left a b hj.le]
      exact hbefore j hj⟩

/-- An arbitrary prefix event and a fresh continuation event factor
exactly at the split, with the continuation translated to the reached site. -/
theorem differenceEventMass_restart {D n m : ℕ}
    (x : Fin D → ℤ) (P : DifferenceHistory D n → Prop)
    (Q : (Fin D → ℤ) → DifferenceHistory D m → Prop) :
    differenceEventMass D (n+m) (fun h =>
      P (fun i => h (Fin.castAdd m i)) ∧
      Q (x + differenceDisplacement (fun i => h (Fin.castAdd m i)) n)
        (fun j => h (Fin.natAdd n j))) =
      ∑ a : DifferenceHistory D n, if P a then differenceHistoryWeight a *
        differenceEventMass D m (Q (x + differenceDisplacement a n)) else 0 := by
  classical
  let F := fun h : DifferenceHistory D (n+m) =>
    if P (fun i => h (Fin.castAdd m i)) ∧
        Q (x + differenceDisplacement (fun i => h (Fin.castAdd m i)) n)
          (fun j => h (Fin.natAdd n j)) then differenceHistoryWeight h else 0
  have hF : differenceEventMass D (n+m) (fun h =>
      P (fun i => h (Fin.castAdd m i)) ∧
        Q (x + differenceDisplacement (fun i => h (Fin.castAdd m i)) n)
          (fun j => h (Fin.natAdd n j))) = ∑ h, F h := by
    unfold differenceEventMass
    apply Finset.sum_congr rfl
    intro h _
    dsimp only [F]
    split_ifs <;> rfl
  rw [hF]
  unfold differenceEventMass
  rw [← (splitHistory (D := D) (n := n) (m := m)).symm.sum_comp F]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : P a
  · rw [if_pos ha, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    change F (Fin.append a b) = _
    simp only [F, Fin.append_left, Fin.append_right, ha, true_and, historyWeight_append]
    split_ifs <;> simp
  · rw [if_neg ha]
    apply Finset.sum_eq_zero
    intro b _
    change F (Fin.append a b) = 0
    simp only [F, Fin.append_left, ha, false_and, if_false]

/-- If every continuation from a hit site has mass at most r, the joint
first-hit/continuation mass is at most r times the first-hit prefix mass.
The comparison never divides by the probability of the hit. -/
theorem differenceFirstHit_restart_le {D n m : ℕ}
    (B : Finset (Fin D → ℤ)) (x : Fin D → ℤ)
    (Q : (Fin D → ℤ) → DifferenceHistory D m → Prop) (r : ℝ)
    (hQ : ∀ y ∈ B, differenceEventMass D m (Q y) ≤ r) :
    differenceEventMass D (n+m) (fun h =>
      differenceFirstHit B x h n ∧
      Q (x + differenceDisplacement (fun i => h (Fin.castAdd m i)) n)
        (fun j => h (Fin.natAdd n j))) ≤
      r * differenceEventMass D n (fun a => differenceFirstHit B x a n) := by
  classical
  have hprefix (h : DifferenceHistory D (n+m)) :
      differenceFirstHit B x h n ↔
        differenceFirstHit B x (fun i => h (Fin.castAdd m i)) n := by
    have hh := differenceFirstHit_append B x
      (fun i => h (Fin.castAdd m i)) (fun j => h (Fin.natAdd n j))
    simpa only [Fin.append_castAdd_natAdd] using hh
  simp_rw [hprefix]
  rw [differenceEventMass_restart x (fun a => differenceFirstHit B x a n) Q]
  unfold differenceEventMass
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a _
  by_cases ha : differenceFirstHit B x a n
  · simp only [ha, if_true]
    rw [mul_comm r]
    exact mul_le_mul_of_nonneg_left (hQ _ ha.1) (historyWeight_nonneg_restart a)
  · simp [ha]

end NearCritical.Section10
