module

public import NearCritical.Section10MergedTrace

/-! The prefix of the merged history depends only on its revealed blocks.
The future-weight bound therefore applies to marks of the actual prefix. -/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open MeasureTheory
open scoped Classical

/-- The block read at a single position of the merged schedule. -/
def pairMoveBlock {d : ℕ} (B B' : ℕ → Finset (LBond d)) (m : PairMove)
    (t t' : ℕ) : Finset (LBond d) :=
  match m with
  | .left => B t
  | .right => B' t'
  | .both => B t ∪ B' t'

/-- The union of the blocks read during a finite schedule. -/
def mergedTraceBlocks {d : ℕ} (B B' : ℕ → Finset (LBond d)) :
    List PairMove → ℕ → ℕ → Finset (LBond d)
  | [], _, _ => ∅
  | m::s, t, t' => pairMoveBlock B B' m t t' ∪
      mergedTraceBlocks B B' s (m.nextLeft t) (m.nextRight t')

theorem PairFresh.suffix_of_append {d : ℕ} (B B' : ℕ → Finset (LBond d))
    (s r : List PairMove) (t t' : ℕ) (R : Finset (LBond d))
    (hF : PairFresh B B' (s ++ r) t t' R) :
    PairFresh B B' r (t + leftCount s) (t' + rightCount s)
      (R ∪ mergedTraceBlocks B B' s t t') := by
  induction s generalizing t t' R with
  | nil => simpa [leftCount, rightCount, mergedTraceBlocks] using hF
  | cons m s ih =>
    have htail : PairFresh B B' (s ++ r) (m.nextLeft t) (m.nextRight t')
        (R ∪ pairMoveBlock B B' m t t') := by
      cases m <;> exact hF.2
    have h := ih _ _ _ htail
    cases m <;> simpa [PairMove.nextLeft, PairMove.nextRight, leftCount, rightCount,
      mergedTraceBlocks, pairMoveBlock, Finset.union_assoc, Nat.add_assoc, Nat.add_comm 1] using h

theorem pairMoveKernel_isLocal {d : ℕ} {X Y : Type*}
    (B B' : ℕ → Finset (LBond d))
    (k : ℕ → X → X → Configuration d × Configuration d → ℝ)
    (k' : ℕ → Y → Y → Configuration d × Configuration d → ℝ)
    (hk : ∀ t x y, IsLocal (B t) (k t x y)) (hk' : ∀ t x y, IsLocal (B' t) (k' t x y))
    (m : PairMove) (t t' : ℕ) (x y : X × Y) :
    IsLocal (pairMoveBlock B B' m t t') (pairMoveKernel k k' m t t' x y) := by
  cases m
  · change IsLocal (B t) (fun z => if y.2 = x.2 then k t x.1 y.1 z else 0)
    by_cases hy : y.2 = x.2
    · simp only [if_pos hy]
      exact hk t x.1 y.1
    · simp only [if_neg hy]
      exact isLocal_const _ 0
  · change IsLocal (B' t') (fun z => if y.1 = x.1 then k' t' x.2 y.2 z else 0)
    by_cases hy : y.1 = x.1
    · simp only [if_pos hy]
      exact hk' t' x.2 y.2
    · simp only [if_neg hy]
      exact isLocal_const _ 0
  · exact (hk t x.1 y.1).mul_union (hk' t' x.2 y.2)

theorem mergedTraceMass_isLocal {d : ℕ} {X Y : Type*}
    (B B' : ℕ → Finset (LBond d))
    (k : ℕ → X → X → Configuration d × Configuration d → ℝ)
    (k' : ℕ → Y → Y → Configuration d × Configuration d → ℝ)
    (hk : ∀ t x y, IsLocal (B t) (k t x y)) (hk' : ∀ t x y, IsLocal (B' t) (k' t x y))
    (s : List PairMove) (t t' : ℕ) (x : X × Y) (h : NestTrace (X × Y) s.length) :
    IsLocal (mergedTraceBlocks B B' s t t') (fun z => mergedTraceMass k k' z s t t' x h) := by
  induction s generalizing t t' x with
  | nil => exact isLocal_const _ 1
  | cons m s ih =>
    exact (pairMoveKernel_isLocal B B' k k' hk hk' m t t' x h.1).mul_union (ih _ _ _ h.2)

/-- A nonnegative mark of the revealed prefix can be carried to the full
history at a cost of at most the nominal shared-step factor of the suffix. -/
theorem mergedTrace_marked_prefix_integral_le {d : ℕ} {X Y : Type*} [Fintype X] [Fintype Y]
    (p q : unitInterval) (B B' : ℕ → Finset (LBond d))
    (k : ℕ → X → X → Configuration d × Configuration d → ℝ)
    (k' : ℕ → Y → Y → Configuration d × Configuration d → ℝ)
    (hk : ∀ t x y, IsLocal (B t) (k t x y)) (hk' : ∀ t x y, IsLocal (B' t) (k' t x y))
    (hk₀ : ∀ t x y z, 0 ≤ k t x y z) (hk'₀ : ∀ t x y z, 0 ≤ k' t x y z)
    {ρ : ℝ} (hρ : 0 < ρ)
    (hL : ∀ t x, (∫ z, ∑ y, k t x y z ∂((percolation d p).prod (percolation d q))) ≤ 1)
    (hR : ∀ t x, (∫ z, ∑ y, k' t x y z ∂((percolation d p).prod (percolation d q))) ≤ 1)
    (hBoth : ∀ t t' x x', (∫ z, ∑ y : X × Y, k t x y.1 z * k' t' x' y.2 z
      ∂((percolation d p).prod (percolation d q))) ≤ ρ)
    (s r : List PairMove) (t t' : ℕ) (x : X × Y) (R : Finset (LBond d))
    (hF : PairFresh B B' (s ++ r) t t' R)
    (F : NestTrace (X × Y) s.length → Configuration d × Configuration d → ℝ)
    (hFloc : ∀ h, IsLocal (R ∪ mergedTraceBlocks B B' s t t') (F h))
    (hF₀ : ∀ h z, 0 ≤ F h z) {b : ℝ} (hb : 0 < b) :
    let μ := (percolation d p).prod (percolation d q)
    (∫ z, ∑ h : NestTrace (X × Y) (s ++ r).length,
      F ((mergedTraceAppend (X × Y) s r).symm h).1 z *
        mergedTraceMass k k' z (s ++ r) t t' x h ∂μ) / (b * ρ ^ sharedCount r) ≤
      (∫ z, ∑ h : NestTrace (X × Y) s.length,
        F h z * mergedTraceMass k k' z s t t' x h ∂μ) / b := by
  intro μ
  let G := fun h z => F h z * mergedTraceMass k k' z s t t' x h
  let V := fun h => pairValue k k' r (t + leftCount s) (t' + rightCount s)
    (mergedTraceLast s x h).1 (mergedTraceLast s x h).2
  have hG (h : NestTrace (X × Y) s.length) :
      IsLocal (R ∪ mergedTraceBlocks B B' s t t') (G h) :=
    (hFloc h).mul ((mergedTraceMass_isLocal B B' k k' hk hk' s t t' x h).mono
      Finset.subset_union_right)
  have hGV (h : NestTrace (X × Y) s.length) : Integrable (fun z => G h z * V h z) μ := by
    obtain ⟨T, hT⟩ := pairValue_exists_isLocal B B' k k' hk hk' r (t + leftCount s)
      (t' + rightCount s) (mergedTraceLast s x h).1 (mergedTraceLast s x h).2
    exact ((hG h).mul_union hT).integrable p q
  have hsplit : (fun z => ∑ h : NestTrace (X × Y) (s ++ r).length,
      F ((mergedTraceAppend (X × Y) s r).symm h).1 z *
        mergedTraceMass k k' z (s ++ r) t t' x h) =
      fun z => ∑ h, G h z * V h z :=
    funext fun z => mergedTrace_marked_prefix_eq k k' z s r t t' x (fun h => F h z)
  have hsum : (∫ z, ∑ h, G h z * V h z ∂μ) ≤
      ρ ^ sharedCount r * (∫ z, ∑ h, G h z ∂μ) := by
    rw [integral_finsetSum _ (fun h _ => hGV h),
      integral_finsetSum _ (fun h _ => (hG h).integrable p q), Finset.mul_sum]
    apply Finset.sum_le_sum
    intro h _
    exact pairValue_integral_le p q B B' k k' hk hk' hk₀ hk'₀ hρ.le hL hR hBoth
      r (t + leftCount s) (t' + rightCount s) (mergedTraceLast s x h).1 (mergedTraceLast s x h).2
      _ (G h) (hG h) (fun z => mul_nonneg (hF₀ h z)
        (mergedTraceMass_nonneg k k' hk₀ hk'₀ z s t t' x h)) (PairFresh.suffix_of_append B B' s r t t' R hF)
  rw [hsplit]
  apply (div_le_div_iff₀ (mul_pos hb (pow_pos hρ _)) hb).2
  convert mul_le_mul_of_nonneg_right hsum hb.le using 1 <;> ring

end NearCritical.Section10
