module

public import NearCritical.Section10MergedTraceLocal

/-! Apply a fresh-row bound to a marked prefix of the actual merged history. -/
@[expose] public section
noncomputable section

namespace NearCritical.Section10

open MeasureTheory
open scoped Classical

theorem mergedTraceMass_snoc {Ω X Y : Type*}
    (k : ℕ → X → X → Ω → ℝ) (k' : ℕ → Y → Y → Ω → ℝ)
    (z : Ω) (s : List PairMove) (m : PairMove) (t t' : ℕ) (x y : X × Y)
    (h : NestTrace (X × Y) s.length) :
    mergedTraceMass k k' z (s ++ [m]) t t' x
      (mergedTraceAppend (X × Y) s [m] (h,(y,PUnit.unit))) =
    mergedTraceMass k k' z s t t' x h *
      pairMoveKernel k k' m (t + leftCount s) (t' + rightCount s) (mergedTraceLast s x h) y z := by
  calc
    _ = mergedTraceMass k k' z s t t' x h *
        mergedTraceMass k k' z [m] (t + leftCount s) (t' + rightCount s)
          (mergedTraceLast s x h) (y,PUnit.unit) :=
      mergedTraceMass_append k k' z s [m] t t' x h (y,PUnit.unit)
    _ = _ := by simp only [mergedTraceMass, mul_one]

/-- A mark on a prefix can be propagated across a fresh move by bounding
the marked row from each fixed past. -/
theorem mergedTrace_marked_snoc_integral_le {d : ℕ} {X Y : Type*} [Fintype X] [Fintype Y]
    (p q : unitInterval) (B B' : ℕ → Finset (LBond d))
    (k : ℕ → X → X → Configuration d × Configuration d → ℝ)
    (k' : ℕ → Y → Y → Configuration d × Configuration d → ℝ)
    (hk : ∀ t x y, IsLocal (B t) (k t x y)) (hk' : ∀ t x y, IsLocal (B' t) (k' t x y))
    (hk₀ : ∀ t x y z, 0 ≤ k t x y z) (hk'₀ : ∀ t x y z, 0 ≤ k' t x y z)
    (s : List PairMove) (m : PairMove) (t t' : ℕ) (x : X × Y) (R : Finset (LBond d))
    (G : NestTrace (X × Y) s.length → Configuration d × Configuration d → ℝ)
    (E : NestTrace (X × Y) s.length → X × Y → Configuration d × Configuration d → ℝ)
    (hG : ∀ h, IsLocal (R ∪ mergedTraceBlocks B B' s t t') (G h))
    (hG₀ : ∀ h z, 0 ≤ G h z) {c : ℝ} :
    let μ := (percolation d p).prod (percolation d q)
    let j := t + leftCount s
    let j' := t' + rightCount s
    let T := pairMoveBlock B B' m j j'
    Disjoint (R ∪ mergedTraceBlocks B B' s t t') T →
    (∀ h y, IsLocal T (E h y)) →
    (∀ h, (∫ z, ∑ y, E h y z * pairMoveKernel k k' m j j'
      (mergedTraceLast s x h) y z ∂μ) ≤ c) →
    (∫ z, ∑ h : NestTrace (X × Y) s.length, ∑ y : X × Y,
      (G h z * E h y z) *
        mergedTraceMass k k' z (s ++ [m]) t t' x
          (mergedTraceAppend (X × Y) s [m] (h,(y,PUnit.unit))) ∂μ) ≤
      c * (∫ z, ∑ h : NestTrace (X × Y) s.length, G h z * mergedTraceMass k k' z s t t' x h ∂μ) := by
  intro μ j j' T hd hE hrow
  let V := fun h z => G h z * mergedTraceMass k k' z s t t' x h
  let U := fun h z => ∑ y, E h y z * pairMoveKernel k k' m j j' (mergedTraceLast s x h) y z
  have hV (h : NestTrace (X × Y) s.length) : IsLocal (R ∪ mergedTraceBlocks B B' s t t') (V h) :=
    (hG h).mul ((mergedTraceMass_isLocal B B' k k' hk hk' s t t' x h).mono Finset.subset_union_right)
  have hU (h : NestTrace (X × Y) s.length) : IsLocal T (U h) :=
    isLocal_sum fun y => (hE h y).mul
      (pairMoveKernel_isLocal B B' k k' hk hk' m j j' (mergedTraceLast s x h) y)
  have heq : (fun z => ∑ h : NestTrace (X × Y) s.length, ∑ y : X × Y,
      (G h z * E h y z) *
        mergedTraceMass k k' z (s ++ [m]) t t' x
          (mergedTraceAppend (X × Y) s [m] (h,(y,PUnit.unit)))) =
      fun z => ∑ h, V h z * U h z := by
    funext z
    apply Finset.sum_congr rfl
    intro h _
    simp only [V, U, Finset.mul_sum, mergedTraceMass_snoc]
    apply Finset.sum_congr rfl
    intro y _
    ring
  rw [heq, integral_finsetSum _ (fun h _ => ((hV h).mul_union (hU h)).integrable p q)]
  change (∑ h, ∫ z, V h z * U h z ∂μ) ≤ c * (∫ z, ∑ h, V h z ∂μ)
  rw [integral_finsetSum _ (fun h _ => (hV h).integrable p q), Finset.mul_sum]
  apply Finset.sum_le_sum
  intro h _
  rw [IsLocal.integral_mul p q hd (hV h) (hU h), mul_comm c]
  exact mul_le_mul_of_nonneg_left (hrow h)
    (integral_nonneg fun z => mul_nonneg (hG₀ h z) (mergedTraceMass_nonneg k k' hk₀ hk'₀ z s t t' x h))

end NearCritical.Section10
