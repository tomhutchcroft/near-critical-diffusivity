module

public import NearCritical.Section10ArrivalPairGeometry
public import NearCritical.Section10MergedArrival
public import NearCritical.Section10MergeSharedLabel

/-! The move at a common site's second arrival determines which stored
arrival states are already in the prefix. -/

@[expose] public section
noncomputable section

namespace NearCritical.Section10

open scoped Classical

/-- At a solo second arrival the other clock has passed its arrival.
At a shared second arrival at least one clock is at its arrival. -/
theorem secondArrival_move_clocks (s r : List PairMove) (m : PairMove) (a b : ℕ)
    (h : isSecondArrival (s ++ m :: r) a b s.length) :
    match m with
    | .left => a = leftCount s ∧ b < rightCount s
    | .right => a < leftCount s ∧ b = rightCount s
    | .both => a ≤ leftCount s ∧ b ≤ rightCount s ∧ (a = leftCount s ∨ b = rightCount s) := by
  have htake : (s ++ m :: r).take (s.length + 1) = s ++ [m] := by
    rw [show s ++ m :: r = (s ++ [m]) ++ r by simp]
    exact List.take_left' (by simp)
  have htake' : (s ++ m :: r).take s.length = s := List.take_left
  have hpost := h.1
  have hpre := h.2
  unfold arrivalsPresent at hpost hpre
  rw [htake] at hpost
  rw [htake'] at hpre
  have hleft (p : List PairMove) : leftCount (p ++ [m]) = leftCount p + leftCount [m] := by
    induction p with
    | nil => simp [leftCount]
    | cons n s ih => cases n <;> simp [leftCount, ih, Nat.add_right_comm]
  have hright (p : List PairMove) : rightCount (p ++ [m]) = rightCount p + rightCount [m] := by
    induction p with
    | nil => simp [rightCount]
    | cons n s ih => cases n <;> simp [rightCount, ih, Nat.add_right_comm]
  rw [hleft s, hright s] at hpost
  cases m <;> simp only [leftCount, rightCount, Nat.add_zero] at hpost ⊢ <;> omega

/-- At a common site's shared second arrival both clocks must be on the
physical arrival row. The shared schedule label determines that row. -/
theorem secondArrival_both_clocks {D M : ℕ} (hM : 1 ≤ M) (X Y : ℕ → Fin D → ℤ)
    {z : RSite D} (hx : z ∈ routeSites M X) (hy : z ∈ routeSites M Y)
    (s r : List PairMove)
    (hm : mergeSched RouteLabel.rank (routeLab M X) (routeLab M Y) (2*M) (2*M) 0 0 =
      s ++ .both :: r)
    (ha : isSecondArrival (s ++ .both :: r) (routeArrivalRank X z) (routeArrivalRank Y z) s.length) :
    leftCount s = routeArrivalRank X z ∧ rightCount s = routeArrivalRank Y z := by
  have hlabel := mergeSched_shared_label RouteLabel.rank (routeLab M X) (routeLab M Y)
    (2*M) (2*M) 0 0 s r hm
  simp only [Nat.zero_add] at hlabel
  have hclocks := congrArg RouteLabel.rank hlabel
  rw [rank_routeLab hM, rank_routeLab hM] at hclocks
  obtain ⟨_,_,h⟩ := secondArrival_move_clocks s r .both _ _ ha
  rcases h with h | h
  · refine ⟨h.symm, match_arrival_label_eq_rank hM X Y hx ?_ ?_⟩
    · rw [← hclocks, ← h]
      exact (routeArrivalRank_arrives X hx).1
    · rw [h]
      exact hlabel
  · refine ⟨match_arrival_label_eq_rank hM Y X hy ?_ ?_, h.symm⟩
    · rw [hclocks, ← h]
      exact (routeArrivalRank_arrives Y hy).1
    · rw [h]
      exact hlabel.symm

/-- At the same local clock, the schedule takes the shared row if the
labels agree, or takes the left row then the right row if they differ. -/
theorem routeMerge_succ {D M : ℕ} (hM : 1 ≤ M) (X Y : ℕ → Fin D → ℤ) (n t : ℕ) :
    mergeSched RouteLabel.rank (routeLab M X) (routeLab M Y) (n+1) (n+1) t t =
      (if routeLab M X t = routeLab M Y t then [.both] else [.left,.right]) ++
      mergeSched RouteLabel.rank (routeLab M X) (routeLab M Y) n n (t+1) (t+1) := by
  classical
  rw [mergeSched]
  by_cases h : routeLab M X t = routeLab M Y t
  · rw [if_pos h, if_pos h]
    rfl
  · have hle : (routeLab M X t).rank ≤ (routeLab M Y t).rank := by
      rw [rank_routeLab hM, rank_routeLab hM]
    rw [if_neg h, if_neg h, if_pos hle]
    cases n with
    | zero =>
      simp only [Nat.zero_add, mergeSched, List.cons_append, List.nil_append]
    | succ n =>
      have hlt : ¬ (routeLab M X (t+1)).rank ≤ (routeLab M Y t).rank := by
        rw [rank_routeLab hM, rank_routeLab hM]
        omega
      have hne : routeLab M X (t+1) ≠ routeLab M Y t := by
        intro he
        exact hlt (congrArg RouteLabel.rank he).le
      rw [mergeSched, if_neg hne, if_neg hlt]
      rfl

/-- One can split the merged schedule at any common local clock before
either route has run out of steps. -/
theorem routeMerge_split_clock {D M : ℕ} (hM : 1 ≤ M) (X Y : ℕ → Fin D → ℤ)
    (a b t : ℕ) :
    mergeSched RouteLabel.rank (routeLab M X) (routeLab M Y) (a+b) (a+b) t t =
      mergeSched RouteLabel.rank (routeLab M X) (routeLab M Y) a a t t ++
      mergeSched RouteLabel.rank (routeLab M X) (routeLab M Y) b b (t+a) (t+a) := by
  classical
  induction a generalizing t with
  | zero =>
    simp only [Nat.zero_add, Nat.add_zero, mergeSched, List.nil_append]
  | succ a ih =>
    rw [Nat.succ_add, routeMerge_succ hM, routeMerge_succ hM, ih]
    simp only [List.append_assoc, Nat.add_assoc, Nat.add_comm 1, Nat.succ_eq_add_one]

/-- A stay at a fixed local clock is determined by its site. -/
theorem routeLab_stay_eq_of_site {D M j : ℕ} (X Y : ℕ → Fin D → ℤ)
    (hx : (routeLab M X j).isStep) (hy : (routeLab M Y j).isStep)
    (hxs : (routeLab M X j).target = (routeLab M X j).site)
    (hys : (routeLab M Y j).target = (routeLab M Y j).site)
    (hsite : (routeLab M X j).site = (routeLab M Y j).site) :
    routeLab M X j = routeLab M Y j := by
  unfold routeLab at hx hy hxs hys hsite ⊢
  split_ifs at hx hy hxs hys hsite ⊢ with h₀ hpad hexit hup
  · exact hx.elim
  · exact hx.elim
  · exact hx.elim
  · simp only [RouteLabel.target, RouteLabel.site, Prod.mk.injEq] at hxs
    omega
  · simp only [RouteLabel.target, RouteLabel.site, Prod.mk.injEq] at hxs hys hsite
    obtain ⟨_,hxs⟩ := hxs
    obtain ⟨_,hys⟩ := hys
    obtain ⟨_,hsite⟩ := hsite
    rw [hxs, hys, hsite]

end NearCritical.Section10
