module

public import NearCritical.Section10DistinctArrivalSchedule
public import NearCritical.Section10SoloArrivalOccupation

/-! The occupations at the two solo cuts are exactly the two saved
arrival occupations in the merged history. -/

@[expose] public section
noncomputable section

namespace NearCritical.Section10

open scoped Classical

/-- Read a left arrival from the prefix of an arbitrary later history. -/
theorem routeTraceGet?_left_split {X Y : Type*} (s r : List PairMove)
    (h : NestTrace (X × Y) (s ++ r).length) {j : ℕ} (hj : j < leftCount s) :
    routeTraceGet? (leftCount (s ++ r)) (mergedRouteTraces (s ++ r) h).1 j =
      routeTraceGet? (leftCount s) (mergedRouteTraces s ((mergedTraceAppend (X × Y) s r).symm h).1).1 j := by
  let e := mergedTraceAppend (X × Y) s r
  let f := e.symm h
  have he : e (f.1,f.2) = h := e.apply_symm_apply h
  exact (congrArg (fun g => routeTraceGet? (leftCount (s ++ r)) (mergedRouteTraces (s ++ r) g).1 j)
    he.symm).trans (mergedArrivalGet_left_prefix s r f.1 f.2 j hj)

/-- Read a right arrival from the prefix of an arbitrary later history. -/
theorem routeTraceGet?_right_split {X Y : Type*} (s r : List PairMove)
    (h : NestTrace (X × Y) (s ++ r).length) {j : ℕ} (hj : j < rightCount s) :
    routeTraceGet? (rightCount (s ++ r)) (mergedRouteTraces (s ++ r) h).2 j =
      routeTraceGet? (rightCount s) (mergedRouteTraces s ((mergedTraceAppend (X × Y) s r).symm h).1).2 j := by
  let e := mergedTraceAppend (X × Y) s r
  let f := e.symm h
  have he : e (f.1,f.2) = h := e.apply_symm_apply h
  exact (congrArg (fun g => routeTraceGet? (rightCount (s ++ r)) (mergedRouteTraces (s ++ r) g).2 j)
    he.symm).trans (mergedArrivalGet_right_prefix s r f.1 f.2 j hj)

/-- Two solo cuts with the left arrival first read the two chronological
arrival states at their original local indices. -/
theorem mergedArrivalStates?_left_then_right {X : Type*} (s gap : List PairMove)
    (h : NestTrace (X × X) (((s ++ [PairMove.left]) ++ gap) ++ [PairMove.right]).length) :
    let r := s ++ [PairMove.left]
    let u := r ++ gap
    let v := u ++ [PairMove.right]
    let past := ((mergedTraceAppend (X × X) u [PairMove.right]).symm h).1
    let old := ((mergedTraceAppend (X × X) r gap).symm past).1
    mergedArrivalStates? v (leftCount s) (rightCount u) h =
      (soloArrivalState? s .left old).bind fun x => (soloArrivalState? u .right h).map (x,·) := by
  intro r u v past old
  have hl : leftCount s < leftCount r := by
    change leftCount s < leftCount (s ++ [PairMove.left])
    rw [leftCount_append]
    exact Nat.lt_succ_self _
  have hlu : leftCount s < leftCount u := by
    change leftCount s < leftCount (r ++ gap)
    rw [leftCount_append]
    omega
  have h₀ := routeTraceGet?_left_split u [PairMove.right] h hlu
  have h₁ := routeTraceGet?_left_split r gap past hl
  change routeTraceGet? (leftCount v) (mergedRouteTraces v h).1 (leftCount s) =
    routeTraceGet? (leftCount u) (mergedRouteTraces u past).1 (leftCount s) at h₀
  change routeTraceGet? (leftCount u) (mergedRouteTraces u past).1 (leftCount s) =
    soloArrivalState? s .left old at h₁
  have hr : routeTraceGet? (rightCount v) (mergedRouteTraces v h).2 (rightCount u) =
      soloArrivalState? u .right h := rfl
  dsimp only [mergedArrivalStates?]
  rw [h₀,h₁,hr]
  cases soloArrivalState? s .left old <;> cases soloArrivalState? u .right h <;> rfl

/-- Two solo cuts with the right arrival first read the two chronological
arrival states at their original local indices. -/
theorem mergedArrivalStates?_right_then_left {X : Type*} (s gap : List PairMove)
    (h : NestTrace (X × X) (((s ++ [PairMove.right]) ++ gap) ++ [PairMove.left]).length) :
    let r := s ++ [PairMove.right]
    let u := r ++ gap
    let v := u ++ [PairMove.left]
    let past := ((mergedTraceAppend (X × X) u [PairMove.left]).symm h).1
    let old := ((mergedTraceAppend (X × X) r gap).symm past).1
    mergedArrivalStates? v (leftCount u) (rightCount s) h =
      (soloArrivalState? u .left h).bind fun x => (soloArrivalState? s .right old).map (x,·) := by
  intro r u v past old
  have hr : rightCount s < rightCount r := by
    change rightCount s < rightCount (s ++ [PairMove.right])
    rw [rightCount_append]
    exact Nat.lt_succ_self _
  have hru : rightCount s < rightCount u := by
    change rightCount s < rightCount (r ++ gap)
    rw [rightCount_append]
    omega
  have h₀ := routeTraceGet?_right_split u [PairMove.left] h hru
  have h₁ := routeTraceGet?_right_split r gap past hr
  change routeTraceGet? (rightCount v) (mergedRouteTraces v h).2 (rightCount s) =
    routeTraceGet? (rightCount u) (mergedRouteTraces u past).2 (rightCount s) at h₀
  change routeTraceGet? (rightCount u) (mergedRouteTraces u past).2 (rightCount s) =
    soloArrivalState? s .right old at h₁
  have hl : routeTraceGet? (leftCount v) (mergedRouteTraces v h).1 (leftCount u) =
      soloArrivalState? u .left h := rfl
  dsimp only [mergedArrivalStates?]
  rw [h₀,h₁,hl]
  cases soloArrivalState? s .right old <;> cases soloArrivalState? u .left h <;> rfl

end NearCritical.Section10
