module

public import NearCritical.Section10SharedTubePredecessor

/-! The two distinct physical arrivals at a common site occur on solo
rows, with a fresh merged gap between them. -/

@[expose] public section
noncomputable section

namespace NearCritical.Section10

open scoped Classical

theorem leftCount_append (s r : List PairMove) :
    leftCount (s ++ r) = leftCount s + leftCount r := by
  induction s with
  | nil => simp [leftCount]
  | cons m s ih => cases m <;> simp [leftCount,ih,Nat.add_right_comm]

theorem rightCount_append (s r : List PairMove) :
    rightCount (s ++ r) = rightCount s + rightCount r := by
  induction s with
  | nil => simp [rightCount]
  | cons m s ih => cases m <;> simp [rightCount,ih,Nat.add_right_comm]

/-- An earlier synchronized clock cuts off a prefix of the later clock. -/
theorem jointRoutePrefix_extends {D M : ℕ} (hM : 1 ≤ M)
    (X Y : ℕ → Fin D → ℤ) {a b : ℕ} (hab : a ≤ b) :
    ∃ r, jointRoutePrefix M X Y b = jointRoutePrefix M X Y a ++ r := by
  refine ⟨mergeSched RouteLabel.rank (routeLab M X) (routeLab M Y) (b-a) (b-a) a a, ?_⟩
  have he : a + (b-a) = b := by omega
  have h := routeMerge_split_clock hM X Y a (b-a) 0
  simpa only [he,Nat.zero_add,jointRoutePrefix] using h

/-- Locate both solo arrivals at a common site inside a synchronized
prefix. The clocks in the result are the clocks before the two arrivals. -/
theorem distinct_arrivals_schedule_split {D M : ℕ} (hM : 1 ≤ M)
    (X Y : ℕ → Fin D → ℤ) {z : RSite D}
    (hX : z ∈ routeSites M X) (hY : z ∈ routeSites M Y) (j : ℕ) :
    let a := routeArrivalRank X z
    let b := routeArrivalRank Y z
    let S := jointRoutePrefix M X Y j
    a < j → b < j →
    routeLab M X a ≠ routeLab M Y b →
    (∃ p gap tail : List PairMove,
      S = ((p ++ [PairMove.left]) ++ gap) ++ PairMove.right :: tail ∧
      leftCount p = a ∧ rightCount ((p ++ [PairMove.left]) ++ gap) = b) ∨
    (∃ p gap tail : List PairMove,
      S = ((p ++ [PairMove.right]) ++ gap) ++ PairMove.left :: tail ∧
      rightCount p = b ∧ leftCount ((p ++ [PairMove.right]) ++ gap) = a) := by
  intro a b S ha hb hne
  let P := jointRoutePrefix M X Y
  have haM : a < 2*M := (routeArrivalRank_arrives X hX).1
  have hbM : b < 2*M := (routeArrivalRank_arrives Y hY).1
  obtain ⟨hl,hr⟩ := distinct_arrival_labels_solo hM X Y hX hY hne
  have haRow : P (a+1) = P a ++ [.left,.right] := by
    exact (jointRoutePrefix_succ hM X Y a).trans (by rw [if_neg (hl a haM)])
  have hbRow : P (b+1) = P b ++ [.left,.right] := by
    exact (jointRoutePrefix_succ hM X Y b).trans (by rw [if_neg (hr b hbM)])
  have hA := jointRoutePrefix_clocks M X Y a
  have hB := jointRoutePrefix_clocks M X Y b
  rcases lt_trichotomy a b with hab | hab | hab
  · obtain ⟨u,hu⟩ := jointRoutePrefix_extends hM X Y (show a+1 ≤ b by omega)
    obtain ⟨v,hv⟩ := jointRoutePrefix_extends hM X Y (show b+1 ≤ j by omega)
    change P b = P (a+1) ++ u at hu
    change S = P (b+1) ++ v at hv
    have hs : (P a ++ [.left]) ++ (PairMove.right :: u) = P b := by
      rw [hu,haRow]
      simp only [List.append_assoc,List.cons_append,List.nil_append]
    have hprefix : (P a ++ [.left]) ++ ((PairMove.right :: u) ++ [.left]) =
        P b ++ [.left] := by rw [← List.append_assoc,hs]
    refine Or.inl ⟨P a,(PairMove.right :: u) ++ [.left],v,?_,hA.1,?_⟩
    · rw [hprefix,hv,hbRow]
      simp only [List.append_assoc,List.cons_append,List.nil_append]
    · rw [hprefix,rightCount_append,hB.2]
      rfl
  · obtain ⟨u,hu⟩ := jointRoutePrefix_extends hM X Y (show a+1 ≤ j by omega)
    change S = P (a+1) ++ u at hu
    refine Or.inl ⟨P a,[],u,?_,hA.1,?_⟩
    · rw [hu,haRow]
      simp only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil]
    · rw [List.append_nil,rightCount_append,hA.2,hab]
      rfl
  · obtain ⟨u,hu⟩ := jointRoutePrefix_extends hM X Y (show b+1 ≤ a by omega)
    obtain ⟨v,hv⟩ := jointRoutePrefix_extends hM X Y (show a+1 ≤ j by omega)
    change P a = P (b+1) ++ u at hu
    change S = P (a+1) ++ v at hv
    have hs : ((P b ++ [.left]) ++ [.right]) ++ u = P a := by
      rw [hu,hbRow,List.append_assoc (P b)]
      rfl
    refine Or.inr ⟨P b ++ [.left],u,PairMove.right :: v,?_,?_,congrArg leftCount hs |>.trans hA.1⟩
    · rw [hs,hv,haRow]
      simp only [List.append_assoc,List.cons_append,List.nil_append]
    · rw [rightCount_append,hB.2]
      rfl

end NearCritical.Section10
