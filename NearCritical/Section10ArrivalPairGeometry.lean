module

public import NearCritical.Section10TrajectoryArrival

/-! At a common site the physical arrivals are either one shared label
or two labels that occur only on their own routes. -/

@[expose] public section
noncomputable section
namespace NearCritical.Section10

/-- A matching arrival label must be the other route's own arrival at
that site. In particular, the two distinct-arrival rows are both solo. -/
theorem match_arrival_label_eq_rank {D M : ℕ} (hM : 1 ≤ M)
    (X Y : ℕ → Fin D → ℤ) {s : RSite D} {j : ℕ}
    (hs : s ∈ routeSites M X) (hj : j < 2*M)
    (he : routeLab M X (routeArrivalRank X s) = routeLab M Y j) :
    j = routeArrivalRank Y s := by
  have hx := routeArrivalRank_arrives X hs
  apply routeArrives_time_eq Y
  refine ⟨hj, ?_, ?_⟩
  · rw [← he]
    exact hx.2.1
  · rcases hx.2.2 with h0 | hp
    · left
      have h := congrArg RouteLabel.rank he
      rw [rank_routeLab hM, rank_routeLab hM, h0] at h
      exact h.symm
    · right
      rw [← he]
      exact hp

theorem distinct_arrival_labels_solo {D M : ℕ} (hM : 1 ≤ M)
    (X Y : ℕ → Fin D → ℤ) {s : RSite D}
    (hx : s ∈ routeSites M X) (hy : s ∈ routeSites M Y)
    (hd : routeLab M X (routeArrivalRank X s) ≠ routeLab M Y (routeArrivalRank Y s)) :
    (∀ j < 2*M, routeLab M X (routeArrivalRank X s) ≠ routeLab M Y j) ∧
      (∀ j < 2*M, routeLab M X j ≠ routeLab M Y (routeArrivalRank Y s)) := by
  constructor
  · intro j hj h
    have he := match_arrival_label_eq_rank hM X Y hx hj h
    rw [he] at h
    exact hd h
  · intro j hj h
    have he := match_arrival_label_eq_rank hM Y X hy hj h.symm
    rw [he] at h
    exact hd h

/-- If a shared move has a shared arrival at its source, its preceding
arrival is the previous local row or is followed by one stay on each route. -/
theorem shared_move_shared_arrival_lag {D M : ℕ} (hM : 1 ≤ M)
    (X Y : ℕ → Fin D → ℤ) {j : ℕ} (hj₀ : 0 < j) (hj : j < 2*M)
    (hmove : routeLab M X j = routeLab M Y j) :
    let s := (routeLab M X j).site
    let a := routeArrivalRank X s
    let b := routeArrivalRank Y s
    routeLab M X a = routeLab M Y b →
    (a = j-1 ∧ b = j-1) ∨
      (a = j-2 ∧ b = j-2 ∧ 3 ≤ j ∧
        (routeLab M X (j-1)).isStep ∧ (routeLab M X (j-1)).target = (routeLab M X (j-1)).site ∧
        (routeLab M Y (j-1)).isStep ∧ (routeLab M Y (j-1)).target = (routeLab M Y (j-1)).site) := by
  intro s a b ha
  have hab : a = b := by
    have h := congrArg RouteLabel.rank ha
    rwa [rank_routeLab hM, rank_routeLab hM] at h
  have hsite : s = (routeLab M Y j).site := congrArg RouteLabel.site hmove
  have hX := routeLab_source_arrival_or_stay X hj₀ hj
  have hY := routeLab_source_arrival_or_stay Y hj₀ hj
  dsimp only at hY
  change a = j-1 ∨ a = j-2 ∧ 3 ≤ j ∧ _ at hX
  rw [← hsite] at hY
  change b = j-1 ∨ b = j-2 ∧ 3 ≤ j ∧ _ at hY
  rcases hX with hX | ⟨hX,h3,hXstep,hXstay⟩
  · exact Or.inl ⟨hX,hab.symm.trans hX⟩
  · rcases hY with hY | ⟨hY,_,hYstep,hYstay⟩
    · omega
    · exact Or.inr ⟨hX,hY,h3,hXstep,hXstay,hYstep,hYstay⟩

end NearCritical.Section10
