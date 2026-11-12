module

public import NearCritical.Section10SiteCollisionRows
public import NearCritical.Section10MergedTraceStep
public import NearCritical.Section10MergedArrivalAppend

/-! The marked prefix estimates at the second physical arrival. A solo
row compares with the recorded earlier nest. A shared row with disjoint
bridges uses the diagonal of the two-child occupation bound. -/

@[expose] public section
noncomputable section
namespace NearCritical.Section10

open MeasureTheory
open scoped Classical

private theorem sum_left_arrival {Ω X Y : Type*} [Fintype X] [Fintype Y]
    (K : ℕ → X → X → Ω → ℝ) (K' : ℕ → Y → Y → Ω → ℝ)
    (j j' : ℕ) (u : X × Y) (z : Ω) (P : X → Prop) [DecidablePred P] :
    (∑ y : X × Y, (if P y.1 then (1:ℝ) else 0) * pairMoveKernel K K' .left j j' u y z) =
    ∑ v : X, if P v then K j u.1 v z else 0 := by
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro v _
  rw [Finset.sum_eq_single u.2]
  · by_cases h : P v <;> simp [pairMoveKernel,h]
  · intro v' _ hv'
    simp [pairMoveKernel,hv']
  · simp

private theorem sum_right_arrival {Ω X Y : Type*} [Fintype X] [Fintype Y]
    (K : ℕ → X → X → Ω → ℝ) (K' : ℕ → Y → Y → Ω → ℝ)
    (j j' : ℕ) (u : X × Y) (z : Ω) (P : Y → Prop) [DecidablePred P] :
    (∑ y : X × Y, (if P y.2 then (1:ℝ) else 0) * pairMoveKernel K K' .right j j' u y z) =
    ∑ v : Y, if P v then K' j' u.2 v z else 0 := by
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  rw [Finset.sum_eq_single u.1]
  · by_cases h : P v <;> simp [pairMoveKernel,h]
  · intro v' _ hv'
    simp [pairMoveKernel,hv']
  · simp

/-- Destination state on the selected side of a solo row. -/
def soloDestination {X : Type*} (m : PairMove) (y : X × X) : X :=
  match m with
  | .left => y.1
  | _ => y.2

namespace NestLayout

variable {d : ℕ} {X C : Type*} [Fintype X]
  (nest : X → Finset C) (p q : unitInterval)
  (B B' : ℕ → Finset (LBond d))
  (K K' : ℕ → X → X → Configuration d × Configuration d → ℝ)
  (hK : ∀ t x y, IsLocal (B t) (K t x y)) (hK' : ∀ t x y, IsLocal (B' t) (K' t x y))
  (hK₀ : ∀ t x y z, 0 ≤ K t x y z) (hK'₀ : ∀ t x y z, 0 ≤ K' t x y z)

include hK hK' hK₀ hK'₀

/-- A site collision at a solo second arrival is bounded by H1, with the
earlier nest read from the full past. -/
theorem firstGood_solo_site_collision_prefix (s : List PairMove) (m : PairMove) (hm : m ≠ .both)
    (t t' : ℕ) (x : X × X) (R : Finset (LBond d))
    (F : NestTrace (X × X) s.length → Configuration d × Configuration d → ℝ)
    (N : NestTrace (X × X) s.length → Finset C)
    (V : NestTrace (X × X) s.length → Prop) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hN : ∀ h, V h → (N h).card ≤ b) :
    let μ := (percolation d p).prod (percolation d q)
    let j := t + leftCount s
    let j' := t' + rightCount s
    let E := fun h (y : X × X) =>
      if V h ∧ (N h ∩ nest (soloDestination m y)).Nonempty then (1:ℝ) else 0
    (∀ h, IsLocal (R ∪ mergedTraceBlocks B B' s t t') (F h)) →
    (∀ h z, 0 ≤ F h z) →
    Disjoint (R ∪ mergedTraceBlocks B B' s t t') (pairMoveBlock B B' m j j') →
    (∀ h, V h → ∀ c ∈ N h, m = .left →
      (∫ z, ∑ y : X, if c ∈ nest y then K j (mergedTraceLast s x h).1 y z else 0 ∂μ) ≤ a) →
    (∀ h, V h → ∀ c ∈ N h, m = .right →
      (∫ z, ∑ y : X, if c ∈ nest y then K' j' (mergedTraceLast s x h).2 y z else 0 ∂μ) ≤ a) →
    (∫ z, ∑ h : NestTrace (X × X) s.length, ∑ y : X × X,
      (F h z * E h y) * mergedTraceMass K K' z (s ++ [m]) t t' x
        (mergedTraceAppend (X × X) s [m] (h,(y,PUnit.unit))) ∂μ) ≤
      (b*a) * (∫ z, ∑ h : NestTrace (X × X) s.length,
        F h z * mergedTraceMass K K' z s t t' x h ∂μ) := by
  intro μ j j' E hF hF₀ hd hleft hright
  refine mergedTrace_marked_snoc_integral_le p q B B' K K' hK hK' hK₀ hK'₀
    s m t t' x R F (fun h y _ => E h y) hF hF₀ hd
    (fun h y => isLocal_const _ (E h y)) ?_
  intro h
  let u := mergedTraceLast s x h
  by_cases hv : V h
  · cases m
    · have hbound := firstGood_solo_site_collision_row_le μ nest (K j u.1)
        (hK₀ j u.1) (fun y => (hK j u.1 y).integrable p q)
        (N h) (fun c hc => hleft h hv c hc rfl)
      refine le_trans ?_ (hbound.trans (mul_le_mul_of_nonneg_right (hN h hv) ha))
      apply le_of_eq
      apply integral_congr_ae
      refine Filter.Eventually.of_forall fun z => ?_
      simpa only [E, hv, true_and, soloDestination] using
        sum_left_arrival K K' j j' u z (fun v => (N h ∩ nest v).Nonempty)
    · have hbound := firstGood_solo_site_collision_row_le μ nest (K' j' u.2)
        (hK'₀ j' u.2) (fun y => (hK' j' u.2 y).integrable p q)
        (N h) (fun c hc => hright h hv c hc rfl)
      refine le_trans ?_ (hbound.trans (mul_le_mul_of_nonneg_right (hN h hv) ha))
      apply le_of_eq
      apply integral_congr_ae
      refine Filter.Eventually.of_forall fun z => ?_
      simpa only [E, hv, true_and, soloDestination] using
        sum_right_arrival K K' j j' u z (fun v => (N h ∩ nest v).Nonempty)
    · exact (hm rfl).elim
  · have hzero (y : X × X) : E h y = 0 := by simp [E,hv]
    simp only [hzero, zero_mul, Finset.sum_const_zero, integral_zero]
    exact mul_nonneg hb ha

/-- A shared arrival through disjoint bridges can cause a site collision
only on the diagonal of the H2 occupation estimate. -/
theorem firstGood_disjoint_site_collision_prefix (s : List PairMove) (t t' : ℕ) (x : X × X)
    (R : Finset (LBond d))
    (F : NestTrace (X × X) s.length → Configuration d × Configuration d → ℝ)
    (S : Finset C) (V : NestTrace (X × X) s.length → Prop)
    (g : NestTrace (X × X) s.length → Configuration d × Configuration d → ℝ)
    (hg₀ : ∀ h z, 0 ≤ g h z) {a : ℝ} (ha : 0 ≤ a) :
    let μ := (percolation d p).prod (percolation d q)
    let j := t + leftCount s
    let j' := t' + rightCount s
    let E := fun h (y : X × X) z =>
      if V h ∧ (S ∩ (nest y.1 ∩ nest y.2)).Nonempty then g h z else 0
    (∀ h, IsLocal (R ∪ mergedTraceBlocks B B' s t t') (F h)) →
    (∀ h z, 0 ≤ F h z) →
    Disjoint (R ∪ mergedTraceBlocks B B' s t t') (pairMoveBlock B B' .both j j') →
    (∀ h, IsLocal (pairMoveBlock B B' .both j j') (g h)) →
    (∀ h, V h → ∀ c ∈ S,
      let u := mergedTraceLast s x h
      (∫ z, g h z *
        ((∑ y : X, if c ∈ nest y then K j u.1 y z else 0) *
         (∑ y : X, if c ∈ nest y then K' j' u.2 y z else 0)) ∂μ) ≤ a) →
    (∫ z, ∑ h : NestTrace (X × X) s.length, ∑ y : X × X,
      (F h z * E h y z) * mergedTraceMass K K' z (s ++ [.both]) t t' x
        (mergedTraceAppend (X × X) s [.both] (h,(y,PUnit.unit))) ∂μ) ≤
      ((S.card : ℝ)*a) * (∫ z, ∑ h : NestTrace (X × X) s.length,
        F h z * mergedTraceMass K K' z s t t' x h ∂μ) := by
  intro μ j j' E hF hF₀ hd hg hrow
  refine mergedTrace_marked_snoc_integral_le p q B B' K K' hK hK' hK₀ hK'₀
    s .both t t' x R F E hF hF₀ hd ?_ ?_
  · intro h y
    by_cases hv : V h ∧ (S ∩ (nest y.1 ∩ nest y.2)).Nonempty
    · simpa only [E, if_pos hv] using hg h
    · simpa only [E, if_neg hv] using isLocal_const (pairMoveBlock B B' .both j j') 0
  · intro h
    let u := mergedTraceLast s x h
    by_cases hv : V h
    · have hnon (y : X × X) (z : Configuration d × Configuration d) :
          0 ≤ g h z * (K j u.1 y.1 z * K' j' u.2 y.2 z) :=
        mul_nonneg (hg₀ h z) (mul_nonneg (hK₀ j u.1 y.1 z) (hK'₀ j' u.2 y.2 z))
      have hI (y : X × X) :
          Integrable (fun z => g h z * (K j u.1 y.1 z * K' j' u.2 y.2 z)) μ :=
        ((hg h).mul ((hK j u.1 y.1).mul_union (hK' j' u.2 y.2))).integrable p q
      refine le_trans ?_ (firstGood_disjoint_site_collision_row_le μ nest (K j u.1) (K' j' u.2)
        (g h) hnon hI S (hrow h hv))
      apply le_of_eq
      apply integral_congr_ae
      refine Filter.Eventually.of_forall fun z => Finset.sum_congr rfl fun y _ => ?_
      simp only [E,hv,true_and,pairMoveKernel,ite_mul,zero_mul,j,j',u]
    · have hzero (y : X × X) (z : Configuration d × Configuration d) : E h y z = 0 := by
        simp [E,hv]
      simp only [hzero, zero_mul, Finset.sum_const_zero, integral_zero]
      exact mul_nonneg (Nat.cast_nonneg _) ha

end NestLayout
end NearCritical.Section10
