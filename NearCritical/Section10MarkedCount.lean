module

public import NearCritical.Section10SharedMarkRecurrence
public import NearCritical.Section10LatticeRule

/-! Summing the normalized mass of each possible site or tube gives
the normalized mass of the number of marks. -/

@[expose] public section
noncomputable section

namespace NearCritical.Section10

open MeasureTheory
open scoped Classical

/-- The expectation of a finite mark count is the sum of the individual
marked expectations, with the same normalized history on both sides. -/
theorem markedPrefixMass_card_filter_le {d : ℕ} {X Y C : Type*} [Fintype X] [Fintype Y]
    (p q : unitInterval) (B B' : ℕ → Finset (LBond d))
    (K : ℕ → X → X → Configuration d × Configuration d → ℝ)
    (K' : ℕ → Y → Y → Configuration d × Configuration d → ℝ)
    (hK : ∀ t x y, IsLocal (B t) (K t x y)) (hK' : ∀ t x y, IsLocal (B' t) (K' t x y))
    (s : List PairMove) (t t' : ℕ) (x : X × Y)
    (S : Finset C) (T : C → Finset (LBond d))
    (P : C → NestTrace (X × Y) s.length → Configuration d × Configuration d → Prop)
    (hP : ∀ c ∈ S, ∀ h, ReadsOnly (T c) (P c h)) (ρ E : ℝ)
    (hE : ∀ c ∈ S, markedPrefixMass p q K K' s t t' x
      (fun h z => if P c h z then 1 else 0) / ρ ^ sharedCount s ≤ E) :
    markedPrefixMass p q K K' s t t' x (fun h z => ((S.filter fun c => P c h z).card : ℝ)) /
      ρ ^ sharedCount s ≤ (S.card : ℝ) * E := by
  let μ := (percolation d p).prod (percolation d q)
  let H := NestTrace (X × Y) s.length
  let W (h : H) z := mergedTraceMass K K' z s t t' x h
  let V (c : C) (h : H) z := if P c h z then (1:ℝ) else 0
  have hI (c : C) (hc : c ∈ S) : Integrable (fun z => ∑ h : H, V c h z * W h z) μ := by
    apply integrable_finsetSum
    intro h _
    have hV := isLocal_of_readsOnly (hP c hc h) (fun b : Prop => if b then (1:ℝ) else 0)
    exact (hV.mul_union (mergedTraceMass_isLocal B B' K K' hK hK' s t t' x h)).integrable p q
  have hpt (z : Configuration d × Configuration d) :
      (∑ h : H, ((S.filter fun c => P c h z).card : ℝ) * W h z) =
        ∑ c ∈ S, ∑ h : H, V c h z * W h z := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [← Finset.sum_mul]
    congr 1
    dsimp only [V]
    rw [← Finset.sum_filter]
    simp
  have heq :
      markedPrefixMass p q K K' s t t' x (fun h z => ((S.filter fun c => P c h z).card : ℝ)) =
        ∑ c ∈ S, markedPrefixMass p q K K' s t t' x (V c) := by
    change (∫ z, ∑ h : H, ((S.filter fun c => P c h z).card : ℝ) * W h z ∂μ) =
      ∑ c ∈ S, ∫ z, ∑ h : H, V c h z * W h z ∂μ
    exact (integral_congr_ae (Filter.Eventually.of_forall hpt)).trans (integral_finsetSum S hI)
  rw [heq,Finset.sum_div]
  exact (Finset.sum_le_sum hE).trans_eq (by simp [nsmul_eq_mul])

/-- A nonnegative mark can be bounded by two other marks on the
support of the history weight. The upper marks are local, which
supplies the integrability needed to add their masses. -/
theorem markedPrefixMass_le_add_of_nonzero {d : ℕ} {X Y : Type*} [Fintype X] [Fintype Y]
    (p q : unitInterval) (B B' : ℕ → Finset (LBond d))
    (K : ℕ → X → X → Configuration d × Configuration d → ℝ)
    (K' : ℕ → Y → Y → Configuration d × Configuration d → ℝ)
    (hK : ∀ t x y, IsLocal (B t) (K t x y)) (hK' : ∀ t x y, IsLocal (B' t) (K' t x y))
    (hK₀ : ∀ t x y z, 0 ≤ K t x y z) (hK'₀ : ∀ t x y z, 0 ≤ K' t x y z)
    (s : List PairMove) (t t' : ℕ) (x : X × Y) (T : Finset (LBond d))
    (F G H : NestTrace (X × Y) s.length → Configuration d × Configuration d → ℝ)
    (hG : ∀ f, IsLocal T (G f)) (hH : ∀ f, IsLocal T (H f))
    (hF : ∀ f z, 0 ≤ F f z)
    (h : ∀ f z, mergedTraceMass K K' z s t t' x f ≠ 0 → F f z ≤ G f z + H f z) :
    markedPrefixMass p q K K' s t t' x F ≤
      markedPrefixMass p q K K' s t t' x G + markedPrefixMass p q K K' s t t' x H := by
  let μ := (percolation d p).prod (percolation d q)
  let V := NestTrace (X × Y) s.length
  let W (f : V) z := mergedTraceMass K K' z s t t' x f
  let I (J : V → Configuration d × Configuration d → ℝ) z := ∑ f : V, J f z * W f z
  have hW (f : V) : IsLocal (mergedTraceBlocks B B' s t t') (W f) :=
    mergedTraceMass_isLocal B B' K K' hK hK' s t t' x f
  have hI (J : V → Configuration d × Configuration d → ℝ) (hJ : ∀ f, IsLocal T (J f)) :
      Integrable (I J) μ :=
    integrable_finsetSum _ (fun f _ => ((hJ f).mul_union (hW f)).integrable p q)
  have hW₀ (f : V) (z : Configuration d × Configuration d) : 0 ≤ W f z :=
    mergedTraceMass_nonneg K K' hK₀ hK'₀ z s t t' x f
  change (∫ z, I F z ∂μ) ≤ (∫ z, I G z ∂μ) + ∫ z, I H z ∂μ
  rw [← integral_add (hI G hG) (hI H hH)]
  refine integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun z => Finset.sum_nonneg fun f _ => mul_nonneg (hF f z) (hW₀ f z))
    ((hI G hG).add (hI H hH)) ?_
  refine Filter.Eventually.of_forall fun z => ?_
  dsimp only [I, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun f _ => ?_
  rw [← add_mul]
  by_cases hzero : W f z = 0
  · simp only [hzero,mul_zero,le_refl]
  · exact mul_le_mul_of_nonneg_right (h f z hzero) (hW₀ f z)

end NearCritical.Section10
