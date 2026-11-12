module

public import NearCritical.Section10FirstGoodArrivalPrefix
public import NearCritical.Section10SharedMarkRecurrence

/-! Occupations of prescribed clusters at successive fresh solo arrivals.
The intervening history can contribute only its nominal shared-row factor. -/

@[expose] public section
noncomputable section

namespace NearCritical.Section10

open MeasureTheory
open scoped Classical

theorem mergedTraceBlocks_append {d : ℕ} (B B' : ℕ → Finset (LBond d))
    (s r : List PairMove) (t t' : ℕ) :
    mergedTraceBlocks B B' (s ++ r) t t' = mergedTraceBlocks B B' s t t' ∪
      mergedTraceBlocks B B' r (t + leftCount s) (t' + rightCount s) := by
  induction s generalizing t t' with
  | nil => simp [mergedTraceBlocks, leftCount, rightCount]
  | cons m s ih =>
    simp only [List.cons_append, mergedTraceBlocks]
    rw [ih, Finset.union_assoc]
    cases m <;> simp only [leftCount, rightCount, PairMove.nextLeft, PairMove.nextRight,
      Nat.add_assoc, Nat.add_comm 1]

theorem PairFresh.prefix_of_append {d : ℕ} (B B' : ℕ → Finset (LBond d))
    (s r : List PairMove) (t t' : ℕ) (R : Finset (LBond d))
    (h : PairFresh B B' (s ++ r) t t' R) : PairFresh B B' s t t' R := by
  induction s generalizing t t' R with
  | nil => trivial
  | cons m s ih =>
    cases m <;> exact ⟨h.1,ih _ _ _ h.2⟩

theorem PairFresh.disjoint_blocks {d : ℕ} (B B' : ℕ → Finset (LBond d))
    (s : List PairMove) (t t' : ℕ) (R : Finset (LBond d))
    (h : PairFresh B B' s t t' R) : Disjoint R (mergedTraceBlocks B B' s t t') := by
  induction s generalizing t t' R with
  | nil => simp [mergedTraceBlocks]
  | cons m s ih =>
    apply Finset.disjoint_union_right.mpr
    cases m <;> exact ⟨h.1, Finset.disjoint_of_subset_left Finset.subset_union_left (ih _ _ _ h.2)⟩

variable {d : ℕ} {X C : Type*} [Fintype X]
  (nest : X → Finset C) (p q : unitInterval)
  (B B' : ℕ → Finset (LBond d))
  (K K' : ℕ → X → X → Configuration d × Configuration d → ℝ)
  (hK : ∀ t x y, IsLocal (B t) (K t x y)) (hK' : ∀ t x y, IsLocal (B' t) (K' t x y))
  (hK₀ : ∀ t x y z, 0 ≤ K t x y z) (hK'₀ : ∀ t x y z, 0 ≤ K' t x y z)

include hK hK' hK₀ hK'₀

/-- A prescribed cluster at a fresh solo arrival costs the H1 bound,
with the mark on the past allowed to depend on earlier occupations. -/
theorem markedPrefixMass_solo_occupation_le {ρ a : ℝ} (hρ : 0 < ρ) (ha : 0 ≤ a)
    (s : List PairMove) (m : PairMove) (hm : m ≠ .both)
    (t t' : ℕ) (x : X × X) (R : Finset (LBond d))
    (F : NestTrace (X × X) s.length → Configuration d × Configuration d → ℝ)
    (V : NestTrace (X × X) s.length → Prop) (c : C) :
    let μ := (percolation d p).prod (percolation d q)
    let j := t + leftCount s
    let j' := t' + rightCount s
    let E (h : NestTrace (X × X) s.length) (y : X × X) :=
      if V h ∧ c ∈ nest (soloDestination m y) then (1:ℝ) else 0
    (∀ h, IsLocal (R ∪ mergedTraceBlocks B B' s t t') (F h)) →
    (∀ h z, 0 ≤ F h z) →
    Disjoint (R ∪ mergedTraceBlocks B B' s t t') (pairMoveBlock B B' m j j') →
    (∀ h, V h → m = .left →
      (∫ z, ∑ y : X, if c ∈ nest y then K j (mergedTraceLast s x h).1 y z else 0 ∂μ) ≤ a) →
    (∀ h, V h → m = .right →
      (∫ z, ∑ y : X, if c ∈ nest y then K' j' (mergedTraceLast s x h).2 y z else 0 ∂μ) ≤ a) →
    markedPrefixMass p q K K' (s ++ [m]) t t' x (fun h z =>
      let g := (mergedTraceAppend (X × X) s [m]).symm h
      F g.1 z * E g.1 g.2.1) / ρ ^ sharedCount (s ++ [m]) ≤
      a * (markedPrefixMass p q K K' s t t' x F / ρ ^ sharedCount s) := by
  intro μ j j' E hF hF₀ hd hleft hright
  have hmark (S : Finset C) : (({c} : Finset C) ∩ S).Nonempty ↔ c ∈ S := by
    simp [Finset.Nonempty, Finset.mem_inter]
  have hraw := NestLayout.firstGood_solo_site_collision_prefix nest p q B B' K K' hK hK' hK₀ hK'₀
    s m hm t t' x R F (fun _ => {c}) V (b := 1) ha (by norm_num) (fun _ _ => by simp)
    hF hF₀ hd
    (fun h hv c' hc he => by
      have hc' := Finset.mem_singleton.mp hc
      subst c'
      exact hleft h hv he)
    (fun h hv c' hc he => by
      have hc' := Finset.mem_singleton.mp hc
      subst c'
      exact hright h hv he)
  simp only [hmark, one_mul] at hraw
  have hcount : sharedCount (s ++ [m]) = sharedCount s := by
    rw [sharedCount_append]
    cases m
    · simp [sharedCount]
    · simp [sharedCount]
    · exact (hm rfl).elim
  rw [hcount, ← mul_div_assoc,
    markedPrefixMass_snoc p q K K' s m t t' x (fun h y z => F h z * E h y)]
  apply div_le_div_of_nonneg_right _ (pow_nonneg hρ.le _)
  simpa only [E, mul_ite, ite_mul, mul_one, mul_zero, zero_mul, markedPrefixMass] using hraw

/-- An occupation already marked on an earlier prefix can be carried
across the gap before a fresh solo arrival. This multiplies the two H1
costs even when other shared rows occur between the arrivals. -/
theorem markedPrefixMass_solo_occupation_after_gap_le {ρ a b : ℝ}
    (hρ : 0 < ρ) (ha : 0 ≤ a)
    (hL : ∀ t x, (∫ z, ∑ y, K t x y z ∂((percolation d p).prod (percolation d q))) ≤ 1)
    (hR : ∀ t x, (∫ z, ∑ y, K' t x y z ∂((percolation d p).prod (percolation d q))) ≤ 1)
    (hBoth : ∀ t t' x x', (∫ z, ∑ y : X × X, K t x y.1 z * K' t' x' y.2 z
      ∂((percolation d p).prod (percolation d q))) ≤ ρ)
    (s r : List PairMove) (m : PairMove) (hm : m ≠ .both)
    (t t' : ℕ) (x : X × X) (R : Finset (LBond d))
    (hFresh : PairFresh B B' ((s ++ r) ++ [m]) t t' R)
    (F : NestTrace (X × X) s.length → Configuration d × Configuration d → ℝ)
    (hF : ∀ h, IsLocal (R ∪ mergedTraceBlocks B B' s t t') (F h))
    (hF₀ : ∀ h z, 0 ≤ F h z)
    (hb : markedPrefixMass p q K K' s t t' x F / ρ ^ sharedCount s ≤ b)
    (V : NestTrace (X × X) (s ++ r).length → Prop) (c : C) :
    let μ := (percolation d p).prod (percolation d q)
    let s' := s ++ r
    let j := t + leftCount s'
    let j' := t' + rightCount s'
    let F' := fun h => F ((mergedTraceAppend (X × X) s r).symm h).1
    let E (h : NestTrace (X × X) s'.length) (y : X × X) :=
      if V h ∧ c ∈ nest (soloDestination m y) then (1:ℝ) else 0
    (∀ h, V h → m = .left →
      (∫ z, ∑ y : X, if c ∈ nest y then K j (mergedTraceLast s' x h).1 y z else 0 ∂μ) ≤ a) →
    (∀ h, V h → m = .right →
      (∫ z, ∑ y : X, if c ∈ nest y then K' j' (mergedTraceLast s' x h).2 y z else 0 ∂μ) ≤ a) →
    markedPrefixMass p q K K' (s' ++ [m]) t t' x (fun h z =>
      let f := (mergedTraceAppend (X × X) s' [m]).symm h
      F' f.1 z * E f.1 f.2.1) / ρ ^ sharedCount (s' ++ [m]) ≤ a * b := by
  intro μ s' j j' F' E hleft hright
  have hsubset : R ∪ mergedTraceBlocks B B' s t t' ⊆
      R ∪ mergedTraceBlocks B B' s' t t' := by
    rw [show s' = s ++ r from rfl, mergedTraceBlocks_append, ← Finset.union_assoc]
    exact Finset.subset_union_left
  have hFloc (h : NestTrace (X × X) s'.length) :
      IsLocal (R ∪ mergedTraceBlocks B B' s' t t') (F' h) :=
    (hF _).mono hsubset
  have hF₀' (h : NestTrace (X × X) s'.length) (z : Configuration d × Configuration d) :
      0 ≤ F' h z := hF₀ _ _
  have hrow := PairFresh.suffix_of_append B B' s' [m] t t' R hFresh
  have hd : Disjoint (R ∪ mergedTraceBlocks B B' s' t t') (pairMoveBlock B B' m j j') := by
    cases m <;> exact hrow.1
  have hp := markedPrefixMass_solo_occupation_le nest p q B B' K K' hK hK' hK₀ hK'₀
    hρ ha s' m hm t t' x R F' V c hFloc hF₀' hd hleft hright
  have hgap := markedPrefixMass_normalized_suffix_le p q B B' K K' hK hK' hK₀ hK'₀
    hρ hL hR hBoth s r t t' x R
      (PairFresh.prefix_of_append B B' s' [m] t t' R hFresh) F hF hF₀
  exact hp.trans (mul_le_mul_of_nonneg_left (hgap.trans hb) ha)

/-- On a shared row, the disjoint-bridge gate allows the H2 bound on
occupation of a prescribed pair. Division by the shared-row factor
leaves `a/ρ` as the normalized cost. -/
theorem markedPrefixMass_shared_pair_occupation_le {ρ a : ℝ} (hρ : 0 < ρ) (ha : 0 ≤ a)
    (s : List PairMove) (t t' : ℕ) (x : X × X) (R : Finset (LBond d))
    (F : NestTrace (X × X) s.length → Configuration d × Configuration d → ℝ)
    (V : NestTrace (X × X) s.length → Prop) (c c' : C)
    (g : NestTrace (X × X) s.length → Configuration d × Configuration d → ℝ) :
    let μ := (percolation d p).prod (percolation d q)
    let j := t + leftCount s
    let j' := t' + rightCount s
    let E (h : NestTrace (X × X) s.length) (y : X × X) z :=
      if V h ∧ c ∈ nest y.1 ∧ c' ∈ nest y.2 then g h z else 0
    (∀ h, IsLocal (R ∪ mergedTraceBlocks B B' s t t') (F h)) →
    (∀ h z, 0 ≤ F h z) →
    Disjoint (R ∪ mergedTraceBlocks B B' s t t') (pairMoveBlock B B' .both j j') →
    (∀ h, IsLocal (pairMoveBlock B B' .both j j') (g h)) →
    (∀ h, V h →
      let u := mergedTraceLast s x h
      (∫ z, g h z *
        ((∑ y : X, if c ∈ nest y then K j u.1 y z else 0) *
         (∑ y : X, if c' ∈ nest y then K' j' u.2 y z else 0)) ∂μ) ≤ a) →
    markedPrefixMass p q K K' (s ++ [.both]) t t' x (fun h z =>
      let f := (mergedTraceAppend (X × X) s [.both]).symm h
      F f.1 z * E f.1 f.2.1 z) / ρ ^ sharedCount (s ++ [.both]) ≤
      (a/ρ) * (markedPrefixMass p q K K' s t t' x F / ρ ^ sharedCount s) := by
  intro μ j j' E hF hF₀ hd hg hrow
  have hraw : markedPrefixMass p q K K' (s ++ [.both]) t t' x (fun h z =>
      let f := (mergedTraceAppend (X × X) s [.both]).symm h
      F f.1 z * E f.1 f.2.1 z) ≤ a * markedPrefixMass p q K K' s t t' x F := by
    rw [markedPrefixMass_snoc p q K K' s .both t t' x (fun h y z => F h z * E h y z)]
    refine mergedTrace_marked_snoc_integral_le p q B B' K K' hK hK' hK₀ hK'₀
      s .both t t' x R F E hF hF₀ hd ?_ ?_
    · intro h y
      by_cases hh : V h ∧ c ∈ nest y.1 ∧ c' ∈ nest y.2
      · simpa only [E, if_pos hh] using hg h
      · simpa only [E, if_neg hh] using isLocal_const (pairMoveBlock B B' .both j j') 0
    · intro h
      let u := mergedTraceLast s x h
      by_cases hv : V h
      · refine le_trans ?_ (hrow h hv)
        apply le_of_eq
        apply integral_congr_ae
        refine Filter.Eventually.of_forall fun z => ?_
        change (∑ y : X × X, E h y z * (K j u.1 y.1 z * K' j' u.2 y.2 z)) =
          g h z * ((∑ y : X, if c ∈ nest y then K j u.1 y z else 0) *
            (∑ y : X, if c' ∈ nest y then K' j' u.2 y z else 0))
        rw [Fintype.sum_prod_type, Finset.sum_mul]
        simp only [Finset.mul_sum]
        refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun y' _ => ?_
        by_cases hp : c ∈ nest y <;> by_cases hq : c' ∈ nest y' <;> simp [E, hv, hp, hq]
      · have he (y : X × X) (z : Configuration d × Configuration d) : E h y z = 0 := by
          simp [E,hv]
        simp only [he, zero_mul, Finset.sum_const_zero, integral_zero]
        exact ha
  rw [sharedCount_append, pow_add, show sharedCount [.both] = 1 from rfl, pow_one]
  calc
    _ ≤ (a * markedPrefixMass p q K K' s t t' x F) / (ρ ^ sharedCount s * ρ) :=
      div_le_div_of_nonneg_right hraw (mul_nonneg (pow_nonneg hρ.le _) hρ.le)
    _ = _ := by ring


end NearCritical.Section10
