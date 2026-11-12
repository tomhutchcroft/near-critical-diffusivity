module

public import NearCritical.Section10MergedTraceStep

/-! Exact transport through a deterministic stay, and the uniform bound
for the normalized mass of shared-tube marks. -/

@[expose] public section
noncomputable section

namespace NearCritical.Section10

open MeasureTheory
open scoped Classical

theorem mergedTraceLast_snoc {X : Type*} (s : List PairMove) (m : PairMove)
    (x y : X) (h : NestTrace X s.length) :
    mergedTraceLast (s ++ [m]) x (mergedTraceAppend X s [m] (h,(y,PUnit.unit))) = y := by
  induction s generalizing x with
  | nil => rfl
  | cons n s ih =>
    change mergedTraceLast (s ++ [m]) h.1 (mergedTraceAppend X s [m] (h.2,(y,PUnit.unit))) = y
    exact ih h.1 h.2

/-- A deterministic row transports a mark with unit mass. The destination
may replace a used-sign placeholder while retaining both nests. -/
theorem mergedTrace_marked_deterministic_snoc_eq {Ω X Y : Type*} [Fintype X] [Fintype Y]
    (k : ℕ → X → X → Ω → ℝ) (k' : ℕ → Y → Y → Ω → ℝ)
    (z : Ω) (s : List PairMove) (m : PairMove) (t t' : ℕ) (x : X × Y)
    (dest : X × Y → X × Y)
    (hrow : ∀ u y, pairMoveKernel k k' m (t + leftCount s) (t' + rightCount s) u y z =
      if y = dest u then (1:ℝ) else 0)
    (F : NestTrace (X × Y) s.length → X × Y → ℝ) :
    (∑ h : NestTrace (X × Y) s.length, ∑ y : X × Y, F h y *
      mergedTraceMass k k' z (s ++ [m]) t t' x
        (mergedTraceAppend (X × Y) s [m] (h,(y,PUnit.unit)))) =
    ∑ h : NestTrace (X × Y) s.length,
      F h (dest (mergedTraceLast s x h)) * mergedTraceMass k k' z s t t' x h := by
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [Finset.sum_eq_single (dest (mergedTraceLast s x h))]
  · rw [mergedTraceMass_snoc, hrow, if_pos rfl, mul_one]
  · intro y _ hy
    rw [mergedTraceMass_snoc, hrow, if_neg hy, mul_zero, mul_zero]
  · simp

theorem sharedCount_append (s r : List PairMove) :
    sharedCount (s ++ r) = sharedCount s + sharedCount r := by
  induction s with
  | nil => simp [sharedCount]
  | cons m s ih => cases m <;> simp [sharedCount, ih, Nat.add_right_comm]

/-- Expectation of a marked joint prefix at a fixed reveal. -/
def markedPrefixMass {d : ℕ} {X Y : Type*} [Fintype X] [Fintype Y]
    (p q : unitInterval)
    (k : ℕ → X → X → Configuration d × Configuration d → ℝ)
    (k' : ℕ → Y → Y → Configuration d × Configuration d → ℝ)
    (s : List PairMove) (t t' : ℕ) (x : X × Y)
    (F : NestTrace (X × Y) s.length → Configuration d × Configuration d → ℝ) : ℝ :=
  ∫ z, ∑ h : NestTrace (X × Y) s.length, F h z * mergedTraceMass k k' z s t t' x h
    ∂((percolation d p).prod (percolation d q))

/-- Index a marked prefix extended by one row as the previous history
and the newly chosen pair of states. -/
theorem markedPrefixMass_snoc {d : ℕ} {X Y : Type*} [Fintype X] [Fintype Y]
    (p q : unitInterval)
    (k : ℕ → X → X → Configuration d × Configuration d → ℝ)
    (k' : ℕ → Y → Y → Configuration d × Configuration d → ℝ)
    (s : List PairMove) (m : PairMove) (t t' : ℕ) (x : X × Y)
    (F : NestTrace (X × Y) s.length → X × Y → Configuration d × Configuration d → ℝ) :
    markedPrefixMass p q k k' (s ++ [m]) t t' x (fun h z =>
      let g := (mergedTraceAppend (X × Y) s [m]).symm h
      F g.1 g.2.1 z) =
    ∫ z, ∑ h : NestTrace (X × Y) s.length, ∑ y : X × Y,
      F h y z * mergedTraceMass k k' z (s ++ [m]) t t' x
        (mergedTraceAppend (X × Y) s [m] (h,(y,PUnit.unit)))
      ∂((percolation d p).prod (percolation d q)) := by
  unfold markedPrefixMass
  apply integral_congr_ae
  refine Filter.Eventually.of_forall fun z => ?_
  let e := mergedTraceAppend (X × Y) s [m]
  change (∑ h : NestTrace (X × Y) (s ++ [m]).length,
    F (e.symm h).1 (e.symm h).2.1 z * mergedTraceMass k k' z (s ++ [m]) t t' x h) =
    ∑ h : NestTrace (X × Y) s.length, ∑ y : X × Y,
      F h y z * mergedTraceMass k k' z (s ++ [m]) t t' x (e (h,(y,PUnit.unit)))
  rw [← e.sum_comp, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro h _
  change (∑ g : (X × Y) × PUnit, F (e.symm (e (h,g))).1 (e.symm (e (h,g))).2.1 z *
    mergedTraceMass k k' z (s ++ [m]) t t' x (e (h,g))) = _
  simp only [Equiv.symm_apply_apply]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro y _
  simp <;> exact Or.inl rfl

/-- A fresh suffix carrying a mark can only decrease its mass after
division by the nominal factor for the entire prefix. -/
theorem markedPrefixMass_normalized_suffix_le {d : ℕ} {X Y : Type*} [Fintype X] [Fintype Y]
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
    (hF₀ : ∀ h z, 0 ≤ F h z) :
    markedPrefixMass p q k k' (s ++ r) t t' x
      (fun h => F ((mergedTraceAppend (X × Y) s r).symm h).1) / ρ ^ sharedCount (s ++ r) ≤
      markedPrefixMass p q k k' s t t' x F / ρ ^ sharedCount s := by
  rw [sharedCount_append, pow_add]
  exact mergedTrace_marked_prefix_integral_le p q B B' k k' hk hk' hk₀ hk'₀ hρ hL hR hBoth
    s r t t' x R hF F hFloc hF₀ (pow_pos hρ _)

/-- A mark can enter from spread at cost `e`, and otherwise can persist
only from a strictly earlier mark with factor at most two thirds. -/
theorem sharedMark_mass_le_three {e : ℝ} (he : 0 ≤ e) (a : ℕ → ℝ) {n : ℕ}
    (hstep : ∀ j < n, a j ≤ e ∨ ∃ i < j, a j ≤ e + (2/3:ℝ) * a i) :
    ∀ j < n, a j ≤ 3*e := by
  intro j
  induction j using Nat.strong_induction_on with
  | h j ih =>
    intro hj
    rcases hstep j hj with h | ⟨i,hi,h⟩
    · linarith
    · have hprev := ih i hi (hi.trans hj)
      linarith

end NearCritical.Section10
