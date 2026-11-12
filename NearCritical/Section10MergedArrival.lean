module

public import NearCritical.Section10RouteArrival

/-! A common site's mark is attached to the second arrival in the merged
schedule and reads the two nests at their own arrival steps. -/

@[expose] public section
noncomputable section

namespace NearCritical.Section10

open scoped Classical

/-- Whether both local arrival rows have occurred in the given prefix. -/
def arrivalsPresent (s : List PairMove) (a b u : ℕ) : Prop :=
  a < leftCount (s.take u) ∧ b < rightCount (s.take u)

theorem pairCounts_take_mono (s : List PairMove) {u v : ℕ} (huv : u ≤ v) :
    leftCount (s.take u) ≤ leftCount (s.take v) ∧
      rightCount (s.take u) ≤ rightCount (s.take v) := by
  induction s generalizing u v with
  | nil => simp
  | cons m s ih =>
    cases u with
    | zero => simp [leftCount,rightCount]
    | succ u =>
      cases v with
      | zero => omega
      | succ v =>
        obtain ⟨h₁,h₂⟩ := ih (Nat.le_of_succ_le_succ huv)
        cases m <;> simp [leftCount,rightCount,h₁,h₂]

theorem arrivalsPresent_mono (s : List PairMove) (a b : ℕ) {u v : ℕ} (huv : u ≤ v) :
    arrivalsPresent s a b u → arrivalsPresent s a b v := by
  rintro ⟨ha,hb⟩
  obtain ⟨hl,hr⟩ := pairCounts_take_mono s huv
  exact ⟨ha.trans_le hl,hb.trans_le hr⟩

/-- The zero-based merged step at which the later arrival is recorded. -/
def isSecondArrival (s : List PairMove) (a b u : ℕ) : Prop :=
  arrivalsPresent s a b (u+1) ∧ ¬ arrivalsPresent s a b u

theorem isSecondArrival_unique (s : List PairMove) (a b : ℕ) {u v : ℕ}
    (hu : isSecondArrival s a b u) (hv : isSecondArrival s a b v) : u = v := by
  rcases lt_trichotomy u v with h | h | h
  · exact (hv.2 (arrivalsPresent_mono s a b (by omega : u+1 ≤ v) hu.1)).elim
  · exact h
  · exact (hu.2 (arrivalsPresent_mono s a b (by omega : v+1 ≤ u) hv.1)).elim

theorem isSecondArrival_exists (s : List PairMove) (a b : ℕ)
    (ha : a < leftCount s) (hb : b < rightCount s) :
    ∃ u < s.length, isSecondArrival s a b u := by
  have hfull : arrivalsPresent s a b s.length := by
    simpa [arrivalsPresent] using And.intro ha hb
  have he : ∃ v, arrivalsPresent s a b v := ⟨s.length,hfull⟩
  let v := Nat.find he
  have hv : arrivalsPresent s a b v := Nat.find_spec he
  have hvl : v ≤ s.length := Nat.find_min' he hfull
  have hv0 : v ≠ 0 := by
    intro h0
    rw [h0] at hv
    simpa [arrivalsPresent,leftCount] using hv.1
  refine ⟨v-1,by omega,?_,?_⟩
  · rwa [show v-1+1 = v by omega]
  · intro h
    have hmin : v ≤ v-1 := Nat.find_min' he h
    omega

/-- Read the outgoing states at the two physical arrivals, if both
have occurred. Each lookup uses the local clock of its own route. -/
def mergedArrivalStates? {X Y : Type*} (s : List PairMove)
    (a b : ℕ) (h : NestTrace (X × Y) s.length) : Option (X × Y) :=
  let r := mergedRouteTraces s h
  match routeTraceGet? (leftCount s) r.1 a, routeTraceGet? (rightCount s) r.2 b with
  | some x, some y => some (x,y)
  | _, _ => none

theorem mergedArrivalStates?_isSome {X Y : Type*} (s : List PairMove)
    (a b : ℕ) (h : NestTrace (X × Y) s.length) :
    (mergedArrivalStates? s a b h).isSome ↔ a < leftCount s ∧ b < rightCount s := by
  have ha := routeTraceGet?_isSome (leftCount s) (mergedRouteTraces s h).1 a
  have hb := routeTraceGet?_isSome (rightCount s) (mergedRouteTraces s h).2 b
  rw [← ha, ← hb]
  dsimp only [mergedArrivalStates?]
  cases routeTraceGet? (leftCount s) (mergedRouteTraces s h).1 a <;>
    cases routeTraceGet? (rightCount s) (mergedRouteTraces s h).2 b <;> simp

/-- The schedule index of a common site's second arrival. -/
def secondArrivalIndex (s : List PairMove) (a b : ℕ) : ℕ :=
  if h : ∃ u < s.length, isSecondArrival s a b u then Classical.choose h else 0

theorem secondArrivalIndex_eq (s : List PairMove) (a b u : ℕ)
    (hu : u < s.length) (h : isSecondArrival s a b u) :
    secondArrivalIndex s a b = u := by
  have he : ∃ u < s.length, isSecondArrival s a b u := ⟨u,hu,h⟩
  unfold secondArrivalIndex
  rw [dif_pos he]
  exact isSecondArrival_unique s a b (Classical.choose_spec he).2 h

/-- A concrete site mark uses the two arrival states in the prefix through
step u, and can fire only at the second arrival of a common site. -/
def mergedSiteEntanglement {D : ℕ} {X Y C : Type*}
    (M : ℕ) (A B : ℕ → Fin D → ℤ) (s : List PairMove)
    (nest : X → Finset C) (nest' : Y → Finset C)
    (u : ℕ) (h : NestTrace (X × Y) (s.take (u+1)).length) : Prop :=
  ∃ z ∈ routeSites M A ∩ routeSites M B,
    let a := routeArrivalRank A z
    let b := routeArrivalRank B z
    isSecondArrival s a b u ∧
      ∃ x y, mergedArrivalStates? (s.take (u+1)) a b h = some (x,y) ∧
        (nest x ∩ nest' y).Nonempty

theorem mergedSiteEntanglement_mem_times {D : ℕ} {X Y C : Type*}
    (M : ℕ) (A B : ℕ → Fin D → ℤ) (s : List PairMove)
    (nest : X → Finset C) (nest' : Y → Finset C)
    (u : ℕ) (hu : u < s.length) (h : NestTrace (X × Y) (s.take (u+1)).length)
    (he : mergedSiteEntanglement M A B s nest nest' u h) :
    u ∈ ((routeSites M A ∩ routeSites M B).image
      (fun z => secondArrivalIndex s (routeArrivalRank A z) (routeArrivalRank B z))) := by
  obtain ⟨z,hz,harr,_⟩ := he
  exact Finset.mem_image.mpr ⟨z,hz,secondArrivalIndex_eq _ _ _ _ hu harr⟩

end NearCritical.Section10
