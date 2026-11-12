module

public import NearCritical.Section10SharedTubePredecessor
public import NearCritical.Section10ActualRoute

@[expose] public section
noncomputable section

namespace NearCritical.Section10

/-- A non-root arrival is a physical tube with a destination that can
serve as the source of a later route row. -/
theorem routeArrivalRank_hasTube {D M : ℕ} (γ : SourceRoute D M) {z : RSite D}
    (hz : z ∈ routeSites M γ.position) (ha : 0 < routeArrivalRank γ.position z) :
    HasTube M (routeLab M γ.position (routeArrivalRank γ.position z)) := by
  have h := (routeArrivalRank_arrives γ.position hz).2.2.resolve_left (Nat.ne_of_gt ha)
  exact routeLab_hasTube γ.1.1 γ.2 h.1 h.2

/-- At a common site, either both arrivals are at a common root or both
are physical arrivals. -/
theorem common_site_arrivals_root_or_positive {D M : ℕ} (X Y : ℕ → Fin D → ℤ)
    {z : RSite D} (hX : z ∈ routeSites M X) (hY : z ∈ routeSites M Y) :
    (routeArrivalRank X z = 0 ∧ routeArrivalRank Y z = 0 ∧
      routeLab M X 0 = routeLab M Y 0) ∨
    (0 < routeArrivalRank X z ∧ 0 < routeArrivalRank Y z) := by
  by_cases h₀ : z.1 = 0
  · have ha : routeArrivalRank X z = 0 := if_pos h₀
    have hb : routeArrivalRank Y z = 0 := if_pos h₀
    have h := (routeArrivalRank_arrives X hX).2.1.trans (routeArrivalRank_arrives Y hY).2.1.symm
    rw [ha,hb,routeLab_zero,routeLab_zero] at h
    change (0, X 0) = (0, Y 0) at h
    refine Or.inl ⟨ha,hb,?_⟩
    rw [routeLab_zero,routeLab_zero,h]
  · have hxa := (routeArrivalRank_le_level X z).1
    have hya := (routeArrivalRank_le_level Y z).1
    exact Or.inr ⟨by omega,by omega⟩

/-- An actual tube lies strictly between the initial row and the exit. -/
theorem routeLab_hasTube_clock {D M : ℕ} (hM : 1 ≤ M) (X : ℕ → Fin D → ℤ)
    {j : ℕ} (hj : j < 2*M) (hTube : HasTube M (routeLab M X j)) :
    0 < j ∧ j+1 < 2*M := by
  have hne := hasTube_target_ne hTube
  have h₀ : j ≠ 0 := by
    intro h
    rw [h,routeLab_zero] at hne
    exact hne rfl
  have hlast : j ≠ 2*M-1 := by
    intro h
    rw [h,routeLab_last hM] at hne
    exact hne rfl
  exact ⟨by omega, by omega⟩

end NearCritical.Section10
