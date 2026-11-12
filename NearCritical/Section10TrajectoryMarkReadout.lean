import NearCritical.Section10ActualTrajectoryOverlap
import NearCritical.Section10TrajectoryTraceEquiv
import NearCritical.Section10SiteCollisionMass
import NearCritical.Section10ArrivalTubeGeometry

noncomputable section

namespace NearCritical.Section10

open scoped Classical

/-- A site mark expressed directly in the two route histories. -/
def traceSiteMark {D d : ℕ} (Λ : NestLayout D d) (n n' : ℕ)
    (f : NestTrace Λ.X n) (g : NestTrace Λ.X n') (a b : ℕ) : Prop :=
  ∃ u v : Λ.X, routeTraceGet? n f a = some u ∧ routeTraceGet? n' g b = some v ∧
    (u.1.val ∩ v.1.val).Nonempty

private def pairOptions {X Y : Type*} (a : Option X) (b : Option Y) : Option (X × Y) :=
  match a,b with
  | some x,some y => some (x,y)
  | _,_ => none

private theorem optionPairMark_iff {X Y : Type*} (P : X → Y → Prop)
    (a : Option X) (b : Option Y) :
    (∃ y, pairOptions a b = some y ∧ P y.1 y.2) ↔
      ∃ u v, a = some u ∧ b = some v ∧ P u v := by
  cases a <;> cases b <;> simp [pairOptions]

theorem mergedSiteMark_iff_traceSiteMark {D d : ℕ} (Λ : NestLayout D d)
    (s : List PairMove) (a b : ℕ) (h : NestTrace (Λ.X × Λ.X) s.length) :
    mergedSiteMark Λ s a b h ↔
      traceSiteMark Λ (leftCount s) (rightCount s) (mergedRouteTraces s h).1 (mergedRouteTraces s h).2 a b := by
  unfold mergedSiteMark mergedArrivalStates? traceSiteMark
  exact optionPairMark_iff (fun (u v : Λ.X) => (u.1.val ∩ v.1.val).Nonempty)
    (routeTraceGet? _ (mergedRouteTraces s h).1 a) (routeTraceGet? _ (mergedRouteTraces s h).2 b)

namespace NestLayout

variable {D d M : ℕ} (Λ : NestLayout D d)

/-- The trajectory site marks are the same marks as the arrival lookups
on the two histories obtained from those trajectories. -/
theorem trajectorySiteMarks_eq_traceSiteMarks
    (X Y : ℕ → Fin D → ℤ) {n n' : ℕ} (hn : n = 2*M) (hn' : n' = 2*M)
    (x x' : Λ.X) (f : Fin n → Λ.X) (g : Fin n' → Λ.X) :
    Λ.trajectorySiteMarks (M := M) X Y (trajectoryState x f) (trajectoryState x' g) =
      (routeSites M X ∩ routeSites M Y).filter (fun s =>
        traceSiteMark Λ n n' (trajectoryTraceEquiv Λ.X n f) (trajectoryTraceEquiv Λ.X n' g)
          (routeArrivalRank X s) (routeArrivalRank Y s)) := by
  unfold trajectorySiteMarks
  apply Finset.filter_congr
  intro s hs
  obtain ⟨hs₁,hs₂⟩ := Finset.mem_inter.mp hs
  have ha : routeArrivalRank X s < n := hn.symm ▸ (routeArrivalRank_arrives X hs₁).1
  have hb : routeArrivalRank Y s < n' := hn'.symm ▸ (routeArrivalRank_arrives Y hs₂).1
  simp only [trajectoryState_of_lt x f ha,trajectoryState_of_lt x' g hb,traceSiteMark,
    routeTraceGet?_trajectory n f _ ha,routeTraceGet?_trajectory n' g _ hb,Option.some.injEq]
  constructor
  · intro h
    exact ⟨_,_,rfl,rfl,h⟩
  · rintro ⟨u,v,hu,hv,h⟩
    cases hu
    cases hv
    exact h

/-- The trajectory tube marks read the incoming states and their pending
signs at the same local indices as the history marks. -/
theorem trajectoryTubeMarks_eq_traceTubeMarks (hM : 1 ≤ M)
    (X Y : ℕ → Fin D → ℤ) {n n' : ℕ} (hn : n = 2*M) (hn' : n' = 2*M)
    (x x' : Λ.X) (f : Fin n → Λ.X) (g : Fin n' → Λ.X) (z : Configuration d × Configuration d) :
    Λ.trajectoryTubeMarks (M := M) X Y (trajectoryState x f) (trajectoryState x' g) z =
      (commonPhysicalTubes M X Y).filter (fun ℓ =>
        Λ.historyTubeMark (refineReveal Λ.ρ₀ Λ.S₀ z) ℓ false n n' (ℓ.rank-1) (ℓ.rank-1)
          (trajectoryTraceEquiv Λ.X n f) (trajectoryTraceEquiv Λ.X n' g) z) := by
  unfold trajectoryTubeMarks
  apply Finset.filter_congr
  intro ℓ hℓ
  obtain ⟨j,hj,hl⟩ := Finset.mem_image.mp ((Finset.mem_inter.mp (Finset.mem_filter.mp hℓ).1).1)
  have hr : ℓ.rank < 2*M := by
    rw [← hl,rank_routeLab hM]
    exact (Finset.mem_Ico.mp hj).2
  have ha : ℓ.rank-1 < n := by omega
  have hb : ℓ.rank-1 < n' := by omega
  simp only [trajectoryState_of_lt x f ha,trajectoryState_of_lt x' g hb,historyTubeMark,
    Bool.false_eq_true,ite_false,routeTraceGet?_trajectory n f _ ha,
    routeTraceGet?_trajectory n' g _ hb,Option.map_some,optionTubeMark]

end NestLayout
end NearCritical.Section10
