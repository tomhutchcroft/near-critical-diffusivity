module

public import NearCritical.Section10MergedArrival

/-! Local arrival lookups respect the split of a merged history into a
past and a fresh suffix. -/

@[expose] public section
noncomputable section
namespace NearCritical.Section10

theorem mergedArrivalGet_left_prefix {X Y : Type*}
    (s r : List PairMove) (h : NestTrace (X × Y) s.length) (g : NestTrace (X × Y) r.length)
    (j : ℕ) (hj : j < leftCount s) :
    routeTraceGet? (leftCount (s ++ r))
      (mergedRouteTraces (s ++ r) (mergedTraceAppend (X × Y) s r (h,g))).1 j =
    routeTraceGet? (leftCount s) (mergedRouteTraces s h).1 j := by
  induction s generalizing j with
  | nil => simp [leftCount] at hj
  | cons m s ih =>
    cases m
    · cases j with
      | zero => rfl
      | succ j =>
        exact ih h.2 j (Nat.lt_of_succ_lt_succ hj)
    · exact ih h.2 j hj
    · cases j with
      | zero => rfl
      | succ j =>
        exact ih h.2 j (Nat.lt_of_succ_lt_succ hj)

theorem mergedArrivalGet_right_prefix {X Y : Type*}
    (s r : List PairMove) (h : NestTrace (X × Y) s.length) (g : NestTrace (X × Y) r.length)
    (j : ℕ) (hj : j < rightCount s) :
    routeTraceGet? (rightCount (s ++ r))
      (mergedRouteTraces (s ++ r) (mergedTraceAppend (X × Y) s r (h,g))).2 j =
    routeTraceGet? (rightCount s) (mergedRouteTraces s h).2 j := by
  induction s generalizing j with
  | nil => simp [rightCount] at hj
  | cons m s ih =>
    cases m
    · exact ih h.2 j hj
    · cases j with
      | zero => rfl
      | succ j =>
        exact ih h.2 j (Nat.lt_of_succ_lt_succ hj)
    · cases j with
      | zero => rfl
      | succ j =>
        exact ih h.2 j (Nat.lt_of_succ_lt_succ hj)

theorem mergedArrivalGet_left_suffix {X Y : Type*}
    (s r : List PairMove) (h : NestTrace (X × Y) s.length) (g : NestTrace (X × Y) r.length)
    (j : ℕ) :
    routeTraceGet? (leftCount (s ++ r))
      (mergedRouteTraces (s ++ r) (mergedTraceAppend (X × Y) s r (h,g))).1 (j + leftCount s) =
    routeTraceGet? (leftCount r) (mergedRouteTraces r g).1 j := by
  induction s with
  | nil => cases h; rfl
  | cons m s ih =>
    cases m <;> exact ih h.2

theorem mergedArrivalGet_right_suffix {X Y : Type*}
    (s r : List PairMove) (h : NestTrace (X × Y) s.length) (g : NestTrace (X × Y) r.length)
    (j : ℕ) :
    routeTraceGet? (rightCount (s ++ r))
      (mergedRouteTraces (s ++ r) (mergedTraceAppend (X × Y) s r (h,g))).2 (j + rightCount s) =
    routeTraceGet? (rightCount r) (mergedRouteTraces r g).2 j := by
  induction s with
  | nil => cases h; rfl
  | cons m s ih =>
    cases m <;> exact ih h.2

/-- A site mark whose two arrival rows lie in the prefix has the same
recorded nests in every extension of that prefix. -/
theorem mergedArrivalStates?_append_of_present {X Y : Type*}
    (s r : List PairMove) (h : NestTrace (X × Y) s.length) (g : NestTrace (X × Y) r.length)
    (a b : ℕ) (ha : a < leftCount s) (hb : b < rightCount s) :
    mergedArrivalStates? (s ++ r) a b (mergedTraceAppend (X × Y) s r (h,g)) =
    mergedArrivalStates? s a b h := by
  dsimp only [mergedArrivalStates?]
  rw [mergedArrivalGet_left_prefix s r h g a ha, mergedArrivalGet_right_prefix s r h g b hb]

end NearCritical.Section10
