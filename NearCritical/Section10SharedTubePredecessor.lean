module

public import NearCritical.Section10SecondArrivalMove
public import NearCritical.Section10ActualLayout
public import NearCritical.Section10FirstGoodUsedHistory

/-! The prefix before a shared physical move. When both arrivals came
through one shared row, the only intervening row is a joint stay. -/

@[expose] public section
noncomputable section

namespace NearCritical.Section10

open scoped Classical

/-- The joint prefix containing the first `j` rows of each route. -/
def jointRoutePrefix {D : ℕ} (M : ℕ) (X Y : ℕ → Fin D → ℤ) (j : ℕ) : List PairMove :=
  mergeSched RouteLabel.rank (routeLab M X) (routeLab M Y) j j 0 0

theorem jointRoutePrefix_clocks {D : ℕ} (M : ℕ) (X Y : ℕ → Fin D → ℤ) (j : ℕ) :
    leftCount (jointRoutePrefix M X Y j) = j ∧ rightCount (jointRoutePrefix M X Y j) = j := by
  exact ⟨mergeSched_leftCount _ _ _ (j+j) j j 0 0 le_rfl,
    mergeSched_rightCount _ _ _ (j+j) j j 0 0 le_rfl⟩

theorem jointRoutePrefix_succ {D M : ℕ} (hM : 1 ≤ M)
    (X Y : ℕ → Fin D → ℤ) (j : ℕ) :
    jointRoutePrefix M X Y (j+1) = jointRoutePrefix M X Y j ++
      (if routeLab M X j = routeLab M Y j then [.both] else [.left,.right]) := by
  unfold jointRoutePrefix
  rw [routeMerge_split_clock hM X Y j 1 0, Nat.zero_add, routeMerge_succ hM X Y 0 j]
  simp only [mergeSched, List.append_nil]

/-- For a shared move, distinct arrival labels give two solo arrivals.
When the arrival label agrees, its row is the last row of the prefix
or is followed only by a shared stay. The common root has arrival row 0. -/
theorem sharedTube_predecessor {D M j : ℕ} (hM : 1 ≤ M)
    (X Y : ℕ → Fin D → ℤ) (hj₀ : 0 < j) (hj : j < 2*M)
    (hm : routeLab M X j = routeLab M Y j) :
    let s := (routeLab M X j).site
    let a := routeArrivalRank X s
    let b := routeArrivalRank Y s
    a < j ∧ b < j ∧
    (((∀ i < 2*M, routeLab M X a ≠ routeLab M Y i) ∧
      (∀ i < 2*M, routeLab M X i ≠ routeLab M Y b)) ∨
     (a = b ∧ routeLab M X a = routeLab M Y a ∧
      ((j = a+1 ∧ jointRoutePrefix M X Y j = jointRoutePrefix M X Y a ++ [.both]) ∨
       (j = a+2 ∧ jointRoutePrefix M X Y j = jointRoutePrefix M X Y a ++ [.both,.both] ∧
        (routeLab M X (a+1)).isStep ∧ (routeLab M X (a+1)).target = (routeLab M X (a+1)).site ∧
        (routeLab M Y (a+1)).isStep ∧ (routeLab M Y (a+1)).target = (routeLab M Y (a+1)).site)))) := by
  intro s a b
  have hs : s = (routeLab M Y j).site := congrArg RouteLabel.site hm
  have hX := (routeLab_site X hj).1
  have hY : s ∈ routeSites M Y := by
    rw [hs]
    exact (routeLab_site Y hj).1
  have ha : a < j := routeArrivalRank_lt_of_source X hj₀ hj
  have hb : b < j := by
    change routeArrivalRank Y s < j
    rw [hs]
    exact routeArrivalRank_lt_of_source Y hj₀ hj
  refine ⟨ha,hb,?_⟩
  by_cases h : routeLab M X a = routeLab M Y b
  · have hab := congrArg RouteLabel.rank h
    rw [rank_routeLab hM, rank_routeLab hM] at hab
    have halabel : routeLab M X a = routeLab M Y a := h.trans (congrArg (routeLab M Y) hab.symm)
    have hp : jointRoutePrefix M X Y (a+1) = jointRoutePrefix M X Y a ++ [.both] := by
      rw [jointRoutePrefix_succ hM, if_pos halabel]
    refine Or.inr ⟨hab,halabel,?_⟩
    rcases shared_move_shared_arrival_lag hM X Y hj₀ hj hm h with
      ⟨hnear,_⟩ | ⟨hfar,_,h3,hxs,hxstay,hys,hystay⟩
    · have he : j = a+1 := by change a = j-1 at hnear; omega
      exact Or.inl ⟨he, by rw [he, hp]⟩
    · have he : j = a+2 := by change a = j-2 at hfar; omega
      have hpred : j-1 = a+1 := by omega
      rw [hpred] at hxs hxstay hys hystay
      have hxnext := routeLab_next_site X (show a+1+1 < 2*M by omega)
      have hynext := routeLab_next_site Y (show a+1+1 < 2*M by omega)
      have hsites : (routeLab M X (a+1)).site = (routeLab M Y (a+1)).site := by
        rw [← hxstay, ← hystay, ← hxnext, ← hynext, ← he]
        exact congrArg RouteLabel.site hm
      have hstay := routeLab_stay_eq_of_site X Y hxs hys hxstay hystay hsites
      have hseg : jointRoutePrefix M X Y j = jointRoutePrefix M X Y a ++ [.both,.both] := by
        rw [he, show a+2 = (a+1)+1 by omega, jointRoutePrefix_succ hM, if_pos hstay, hp]
        simp only [List.append_assoc, List.cons_append, List.nil_append]
      exact Or.inr ⟨he,hseg,hxs,hxstay,hys,hystay⟩
  · exact Or.inl (distinct_arrival_labels_solo hM X Y hX hY h)

/-- A physical tube uses a sign on an interior moving row. -/
theorem routeSignDraw_true_of_hasTube {D M j : ℕ} (hM : 1 ≤ M)
    (γ : SourceRoute D M) (hj : j < 2*M) (h : HasTube M (routeLab M γ.position j)) :
    NestLayout.routeSignDraw γ j = true := by
  have hn := hasTube_target_ne h
  have hpos : j ≠ 0 := by
    intro he
    rw [he, routeLab_zero] at hn
    exact hn rfl
  have hlast : j ≠ 2*M-1 := by
    intro he
    rw [he, routeLab_last hM] at hn
    exact hn rfl
  have hd : j = 0 ∨ (1 ≤ j ∧ j+1 < 2*M ∧
      (routeLab M γ.position j).target ≠ (routeLab M γ.position j).site) :=
    Or.inr ⟨by omega, by omega, hn⟩
  exact decide_eq_true hd

end NearCritical.Section10
