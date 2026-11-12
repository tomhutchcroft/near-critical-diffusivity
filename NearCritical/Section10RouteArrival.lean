module

public import NearCritical.Section10LatticeHelpers
public import NearCritical.Section10PhaseStartBudget
public import NearCritical.Section10MergedRouteTraces

/-! The physical arrival of a route at each of its visited sites. -/

@[expose] public section
noncomputable section

namespace NearCritical.Section10

open scoped Classical

/-- The arrival is the start or a physical move into the given site. -/
def routeArrives {D : ℕ} (M : ℕ) (X : ℕ → Fin D → ℤ) (t : ℕ) (z : RSite D) : Prop :=
  t < 2*M ∧ (routeLab M X t).target = z ∧
    (t = 0 ∨ ((routeLab M X t).isStep ∧ (routeLab M X t).target ≠ (routeLab M X t).site))

theorem routeArrivalRank_arrives {D M : ℕ} (X : ℕ → Fin D → ℤ) {z : RSite D}
    (hz : z ∈ routeSites M X) : routeArrives M X (routeArrivalRank X z) z := by
  obtain ⟨ht, hz', hm⟩ := routeArrivalRank_spec X hz
  refine ⟨ht, hz', ?_⟩
  by_cases h0 : z.1 = 0
  · exact Or.inl (if_pos h0)
  · have hlevel : z.1 < M := (mem_routeSites M X z.1 z.2).mp hz |>.1
    have hr : 1 ≤ routeArrivalRank X z ∧ routeArrivalRank X z < 2*M-1 := by
      unfold routeArrivalRank
      rw [if_neg h0]
      split_ifs <;> omega
    refine Or.inr ⟨routeLab_isStep X hr.1 hr.2, ?_⟩
    intro he
    exact hm h0 (he.symm.trans hz')

theorem routeArrives_time_eq {D M : ℕ} (X : ℕ → Fin D → ℤ) {t : ℕ} {z : RSite D}
    (h : routeArrives M X t z) : t = routeArrivalRank X z := by
  obtain ⟨ht, rfl, hmove⟩ := h
  by_cases h0 : t = 0
  · subst t
    simp [routeLab_zero, RouteLabel.target, routeArrivalRank]
  · obtain ⟨hstep,hchange⟩ := hmove.resolve_left h0
    have hlast : t ≠ 2*M-1 := by
      intro he
      have hM : 1 ≤ M := by omega
      rw [he, routeLab_last hM] at hstep
      exact hstep
    unfold routeLab at hstep hchange ⊢
    rw [if_neg h0, if_neg (not_le.mpr ht), if_neg hlast] at hstep hchange ⊢
    by_cases hodd : t % 2 = 1
    · rw [if_pos hodd]
      change t = routeArrivalRank X ((t-1)/2+1,X ((t-1)/2))
      have hj : (t-1)/2+1 ≠ 0 := by omega
      have hpred : (t-1)/2+1-1 = (t-1)/2 := by omega
      simp only [routeArrivalRank, Prod.fst, Prod.snd, if_neg hj, hpred, if_true]
      omega
    · rw [if_neg hodd] at hchange ⊢
      have hneq : X (t/2) ≠ X (t/2-1) := by
        intro hh
        apply hchange
        simp only [RouteLabel.target, RouteLabel.site, hh]
      change t = routeArrivalRank X (t/2,X (t/2))
      have hj : t/2 ≠ 0 := by omega
      simp only [routeArrivalRank, Prod.fst, Prod.snd, if_neg hj, if_neg hneq]
      omega

theorem routeArrivalRank_le_level {D : ℕ} (X : ℕ → Fin D → ℤ) (z : RSite D) :
    2*z.1-1 ≤ routeArrivalRank X z ∧ routeArrivalRank X z ≤ 2*z.1 := by
  unfold routeArrivalRank
  split_ifs <;> omega

theorem routeArrivalRank_lt_of_source {D M : ℕ} (X : ℕ → Fin D → ℤ) {t : ℕ}
    (ht0 : 0 < t) (ht : t < 2*M) :
    routeArrivalRank X (routeLab M X t).site < t := by
  by_cases he : t % 2 = 1
  · have h := (routeArrivalRank_le_level X (routeLab M X t).site).2
    rw [(routeLab_site X ht).2] at h
    omega
  · have hlast : t ≠ 2*M-1 := by omega
    unfold routeLab
    rw [if_neg ht0.ne', if_neg (not_le.mpr ht), if_neg hlast, if_neg he]
    simp only [RouteLabel.site, routeArrivalRank, if_true]
    have hlev : t/2 ≠ 0 := by omega
    rw [if_neg hlev]
    omega

/-- State immediately after the given zero-based local transition,
when that transition is present in the prefix. -/
def routeTraceGet? {X : Type*} : (n : ℕ) → NestTrace X n → ℕ → Option X
  | 0, _, _ => none
  | _+1, h, 0 => some h.1
  | n+1, h, j+1 => routeTraceGet? n h.2 j

theorem routeTraceGet?_isSome {X : Type*} (n : ℕ) (h : NestTrace X n) (j : ℕ) :
    (routeTraceGet? n h j).isSome ↔ j < n := by
  induction n generalizing j with
  | zero => simp [routeTraceGet?]
  | succ n ih =>
    cases j with
    | zero => simp [routeTraceGet?]
    | succ j => simpa only [routeTraceGet?, Nat.succ_lt_succ_iff] using ih h.2 j

end NearCritical.Section10
