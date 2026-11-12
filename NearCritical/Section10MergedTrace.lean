module

public import NearCritical.NestChainLaw
public import NearCritical.Section10CoupledPairMass

/-! The weighted history of the two chains in the order of the merged
schedule, with the unadvanced chain's state fixed on a solo move. -/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open scoped Classical

/-- The joint row at one position of the merged schedule. -/
def pairMoveKernel {Ω X Y : Type*}
    (k : ℕ → X → X → Ω → ℝ) (k' : ℕ → Y → Y → Ω → ℝ)
    (move : PairMove) (t t' : ℕ) (x y : X × Y) (ω : Ω) : ℝ :=
  match move with
  | .left => if y.2 = x.2 then k t x.1 y.1 ω else 0
  | .right => if y.1 = x.1 then k' t' x.2 y.2 ω else 0
  | .both => k t x.1 y.1 ω * k' t' x.2 y.2 ω

/-- The local clock of each chain advances only when its row is used. -/
def PairMove.nextLeft (m : PairMove) (t : ℕ) : ℕ :=
  match m with
  | .right => t
  | _ => t+1

def PairMove.nextRight (m : PairMove) (t : ℕ) : ℕ :=
  match m with
  | .left => t
  | _ => t+1

/-- Product of the joint rows for a fixed history and configuration. -/
def mergedTraceMass {Ω X Y : Type*}
    (k : ℕ → X → X → Ω → ℝ) (k' : ℕ → Y → Y → Ω → ℝ) (ω : Ω) :
    (s : List PairMove) → ℕ → ℕ → X × Y → NestTrace (X × Y) s.length → ℝ
  | [], _, _, _, _ => 1
  | m::s, t, t', x, h =>
      pairMoveKernel k k' m t t' x h.1 ω *
        mergedTraceMass k k' ω s (m.nextLeft t) (m.nextRight t') h.1 h.2

theorem mergedTraceMass_nonneg {Ω X Y : Type*}
    (k : ℕ → X → X → Ω → ℝ) (k' : ℕ → Y → Y → Ω → ℝ)
    (hk : ∀ t x y ω, 0 ≤ k t x y ω) (hk' : ∀ t x y ω, 0 ≤ k' t x y ω)
    (ω : Ω) (s : List PairMove) (t t' : ℕ) (x : X × Y) (h : NestTrace (X × Y) s.length) :
    0 ≤ mergedTraceMass k k' ω s t t' x h := by
  induction s generalizing t t' x with
  | nil => exact zero_le_one
  | cons m s ih =>
    refine mul_nonneg ?_ (ih _ _ _ h.2)
    cases m
    · dsimp [pairMoveKernel]
      split_ifs
      · exact hk _ _ _ _
      · exact le_rfl
    · dsimp [pairMoveKernel]
      split_ifs
      · exact hk' _ _ _ _
      · exact le_rfl
    · exact mul_nonneg (hk _ _ _ _) (hk' _ _ _ _)

/-- Summing the weighted histories recovers the existing two-chain weight. -/
theorem mergedTraceMass_sum_eq_pairValue {d : ℕ} {X Y : Type*} [Fintype X] [Fintype Y]
    (k : ℕ → X → X → Configuration d × Configuration d → ℝ)
    (k' : ℕ → Y → Y → Configuration d × Configuration d → ℝ)
    (z : Configuration d × Configuration d) (s : List PairMove) (t t' : ℕ) (x : X × Y) :
    (∑ h : NestTrace (X × Y) s.length, mergedTraceMass k k' z s t t' x h) =
      pairValue k k' s t t' x.1 x.2 z := by
  induction s generalizing t t' x with
  | nil =>
    let : Unique (NestTrace (X × Y) ([] : List PairMove).length) := inferInstanceAs (Unique PUnit)
    simp [mergedTraceMass, pairValue]
  | cons m s ih =>
    change (∑ h : (X × Y) × NestTrace (X × Y) s.length,
      pairMoveKernel k k' m t t' x h.1 z *
        mergedTraceMass k k' z s (m.nextLeft t) (m.nextRight t') h.1 h.2) = _
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, ih]
    cases m
    · simp only [pairMoveKernel, PairMove.nextLeft, PairMove.nextRight, pairValue]
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro y _
      rw [Finset.sum_eq_single x.2]
      · simp
      · intro b _ hb
        simp [hb]
      · simp
    · simp only [pairMoveKernel, PairMove.nextLeft, PairMove.nextRight, pairValue]
      rw [Fintype.sum_prod_type, Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro y _
      rw [Finset.sum_eq_single x.1]
      · simp
      · intro b _ hb
        simp [hb]
      · simp
    · simp [pairMoveKernel, PairMove.nextLeft, PairMove.nextRight, pairValue]

/-- Final pair state of a finite prefix, with the initial state retained
when that prefix is empty. -/
def mergedTraceLast {X : Type*} :
    (s : List PairMove) → X → NestTrace X s.length → X
  | [], x, _ => x
  | _::s, _, h => mergedTraceLast s h.1 h.2

/-- A joint history splits uniquely at the boundary between two schedules. -/
def mergedTraceAppend (X : Type*) :
    (s r : List PairMove) → NestTrace X s.length × NestTrace X r.length ≃
      NestTrace X (s ++ r).length
  | [], r => Equiv.punitProd _
  | _::s, r =>
    (Equiv.prodAssoc X (NestTrace X s.length) (NestTrace X r.length)).trans
      (Equiv.prodCongr (Equiv.refl X) (mergedTraceAppend X s r))

/-- Split the path weight at a prefix, advancing both local clocks by the
number of moves assigned to them in the prefix. -/
theorem mergedTraceMass_append {Ω X Y : Type*}
    (k : ℕ → X → X → Ω → ℝ) (k' : ℕ → Y → Y → Ω → ℝ)
    (ω : Ω) (s r : List PairMove) (t t' : ℕ) (x : X × Y)
    (h : NestTrace (X × Y) s.length) (h' : NestTrace (X × Y) r.length) :
    mergedTraceMass k k' ω (s ++ r) t t' x (mergedTraceAppend (X × Y) s r (h,h')) =
      mergedTraceMass k k' ω s t t' x h *
        mergedTraceMass k k' ω r (t + leftCount s) (t' + rightCount s) (mergedTraceLast s x h) h' := by
  induction s generalizing t t' x with
  | nil =>
    simp [mergedTraceAppend, mergedTraceMass, mergedTraceLast, leftCount, rightCount]
    rfl
  | cons m s ih =>
    change pairMoveKernel k k' m t t' x h.1 ω *
      mergedTraceMass k k' ω (s ++ r) (m.nextLeft t) (m.nextRight t') h.1
        (mergedTraceAppend (X × Y) s r (h.2,h')) =
      (pairMoveKernel k k' m t t' x h.1 ω *
        mergedTraceMass k k' ω s (m.nextLeft t) (m.nextRight t') h.1 h.2) *
      mergedTraceMass k k' ω r (t + leftCount (m::s)) (t' + rightCount (m::s))
        (mergedTraceLast s h.1 h.2) h'
    rw [ih, mul_assoc]
    cases m <;> simp only [PairMove.nextLeft, PairMove.nextRight, leftCount, rightCount,
      Nat.add_assoc, Nat.add_comm 1]

/-- The weighted suffix of a marked prefix is the existing pair value at
the pair state attained at that prefix. -/
theorem mergedTrace_marked_prefix_eq {d : ℕ} {X Y : Type*} [Fintype X] [Fintype Y]
    (k : ℕ → X → X → Configuration d × Configuration d → ℝ)
    (k' : ℕ → Y → Y → Configuration d × Configuration d → ℝ)
    (z : Configuration d × Configuration d) (s r : List PairMove) (t t' : ℕ) (x : X × Y)
    (F : NestTrace (X × Y) s.length → ℝ) :
    (∑ h : NestTrace (X × Y) (s ++ r).length,
      F ((mergedTraceAppend (X × Y) s r).symm h).1 * mergedTraceMass k k' z (s ++ r) t t' x h) =
    ∑ h : NestTrace (X × Y) s.length,
      (F h * mergedTraceMass k k' z s t t' x h) *
        pairValue k k' r (t + leftCount s) (t' + rightCount s)
          (mergedTraceLast s x h).1 (mergedTraceLast s x h).2 z := by
  let e := mergedTraceAppend (X × Y) s r
  rw [← e.sum_comp, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro h _
  change (∑ h' : NestTrace (X × Y) r.length,
    F (e.symm (e (h,h'))).1 * mergedTraceMass k k' z (s ++ r) t t' x (e (h,h'))) = _
  simp only [Equiv.symm_apply_apply]
  dsimp only [e]
  simp_rw [mergedTraceMass_append, ← mul_assoc, ← Finset.mul_sum, mergedTraceMass_sum_eq_pairValue]

end NearCritical.Section10
