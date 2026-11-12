module

public import NearCritical.Section10MergedTrace

/-! Interleave the two route histories according to the merged schedule.
On a solo move, the other chain's state is carried forward. -/
@[expose] public section
noncomputable section

namespace NearCritical.Section10

open scoped Classical

/-- Read only the states at the moves assigned to each chain. -/
def mergedRouteTraces {X Y : Type*} :
    (s : List PairMove) → NestTrace (X × Y) s.length →
      NestTrace X (leftCount s) × NestTrace Y (rightCount s)
  | [], _ => (PUnit.unit,PUnit.unit)
  | .left :: s, h =>
    let r := mergedRouteTraces s h.2
    ((h.1.1,r.1),r.2)
  | .right :: s, h =>
    let r := mergedRouteTraces s h.2
    (r.1,(h.1.2,r.2))
  | .both :: s, h =>
    let r := mergedRouteTraces s h.2
    ((h.1.1,r.1),(h.1.2,r.2))

/-- Replay both histories in the schedule order. -/
def interleaveRouteTraces {X Y : Type*} :
    (s : List PairMove) → X × Y → NestTrace X (leftCount s) → NestTrace Y (rightCount s) →
      NestTrace (X × Y) s.length
  | [], _, _, _ => PUnit.unit
  | .left :: s, x, l, r =>
    let y := (l.1,x.2)
    (y,interleaveRouteTraces s y l.2 r)
  | .right :: s, x, l, r =>
    let y := (x.1,r.1)
    (y,interleaveRouteTraces s y l r.2)
  | .both :: s, _, l, r =>
    let y := (l.1,r.1)
    (y,interleaveRouteTraces s y l.2 r.2)

theorem mergedRouteTraces_interleave {X Y : Type*} (s : List PairMove) (x : X × Y)
    (l : NestTrace X (leftCount s)) (r : NestTrace Y (rightCount s)) :
    mergedRouteTraces s (interleaveRouteTraces s x l r) = (l,r) := by
  induction s generalizing x with
  | nil => cases l; cases r; rfl
  | cons m s ih =>
    cases m
    · change X × NestTrace X (leftCount s) at l
      change NestTrace Y (rightCount s) at r
      simp only [interleaveRouteTraces, mergedRouteTraces]
      rw [ih (l.1,x.2) l.2 r]
    · change NestTrace X (leftCount s) at l
      change Y × NestTrace Y (rightCount s) at r
      simp only [interleaveRouteTraces, mergedRouteTraces]
      rw [ih (x.1,r.1) l r.2]
    · change X × NestTrace X (leftCount s) at l
      change Y × NestTrace Y (rightCount s) at r
      simp only [interleaveRouteTraces, mergedRouteTraces]
      rw [ih (l.1,r.1) l.2 r.2]

/-- The finite route weight in increasing order of the local clock. -/
def routeTraceMass {Ω X : Type*} (K : ℕ → X → X → Ω → ℝ) (z : Ω) :
    (n : ℕ) → ℕ → X → NestTrace X n → ℝ
  | 0, _, _, _ => 1
  | n+1, t, x, h => K t x h.1 z * routeTraceMass K z n (t+1) h.1 h.2

theorem mergedTraceMass_interleave {Ω X Y : Type*}
    (k : ℕ → X → X → Ω → ℝ) (k' : ℕ → Y → Y → Ω → ℝ)
    (z : Ω) (s : List PairMove) (t t' : ℕ) (x : X × Y)
    (l : NestTrace X (leftCount s)) (r : NestTrace Y (rightCount s)) :
    mergedTraceMass k k' z s t t' x (interleaveRouteTraces s x l r) =
      routeTraceMass k z (leftCount s) t x.1 l *
        routeTraceMass k' z (rightCount s) t' x.2 r := by
  induction s generalizing t t' x with
  | nil => simp [mergedTraceMass, routeTraceMass, leftCount, rightCount]
  | cons m s ih =>
    cases m
    · change X × NestTrace X (leftCount s) at l
      change NestTrace Y (rightCount s) at r
      simp only [mergedTraceMass, pairMoveKernel, PairMove.nextLeft, PairMove.nextRight,
        interleaveRouteTraces, leftCount, rightCount, routeTraceMass, if_true]
      rw [ih (t+1) t' (l.1,x.2) l.2 r]
      ring
    · change NestTrace X (leftCount s) at l
      change Y × NestTrace Y (rightCount s) at r
      simp only [mergedTraceMass, pairMoveKernel, PairMove.nextLeft, PairMove.nextRight,
        interleaveRouteTraces, leftCount, rightCount, routeTraceMass, if_true]
      rw [ih t (t'+1) (x.1,r.1) l r.2]
      ring
    · change X × NestTrace X (leftCount s) at l
      change Y × NestTrace Y (rightCount s) at r
      simp only [mergedTraceMass, pairMoveKernel, PairMove.nextLeft, PairMove.nextRight,
        interleaveRouteTraces, leftCount, rightCount, routeTraceMass]
      rw [ih (t+1) (t'+1) (l.1,r.1) l.2 r.2]
      ring

/-- A nonzero history keeps the inactive chain fixed on every solo move. -/
theorem interleave_mergedRouteTraces_of_nonzero {Ω X Y : Type*}
    (k : ℕ → X → X → Ω → ℝ) (k' : ℕ → Y → Y → Ω → ℝ)
    (z : Ω) (s : List PairMove) (t t' : ℕ) (x : X × Y)
    (h : NestTrace (X × Y) s.length) (hh : mergedTraceMass k k' z s t t' x h ≠ 0) :
    interleaveRouteTraces s x (mergedRouteTraces s h).1 (mergedRouteTraces s h).2 = h := by
  induction s generalizing t t' x with
  | nil => cases h; rfl
  | cons m s ih =>
    change pairMoveKernel k k' m t t' x h.1 z *
      mergedTraceMass k k' z s (m.nextLeft t) (m.nextRight t') h.1 h.2 ≠ 0 at hh
    obtain ⟨hrow, htail⟩ := mul_ne_zero_iff.mp hh
    have hrec := ih _ _ _ h.2 htail
    cases m
    · have he : h.1.2 = x.2 := by
        by_contra hn
        exact hrow (by simp [pairMoveKernel, hn])
      have hp : (h.1.1,x.2) = h.1 := Prod.ext rfl he.symm
      change ((h.1.1,x.2), interleaveRouteTraces s (h.1.1,x.2)
        (mergedRouteTraces s h.2).1 (mergedRouteTraces s h.2).2) = _
      rw [hp, hrec] <;> rfl
    · have he : h.1.1 = x.1 := by
        by_contra hn
        exact hrow (by simp [pairMoveKernel, hn])
      have hp : (x.1,h.1.2) = h.1 := Prod.ext he.symm rfl
      change ((x.1,h.1.2), interleaveRouteTraces s (x.1,h.1.2)
        (mergedRouteTraces s h.2).1 (mergedRouteTraces s h.2).2) = _
      rw [hp, hrec] <;> rfl
    · change (h.1, interleaveRouteTraces s h.1
        (mergedRouteTraces s h.2).1 (mergedRouteTraces s h.2).2) = _
      rw [hrec] <;> rfl

end NearCritical.Section10
