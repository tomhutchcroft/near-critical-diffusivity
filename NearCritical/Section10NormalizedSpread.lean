module

public import NearCritical.Section10FirstGoodSpreadPending
public import NearCritical.Section10SharedMarkRecurrence

/-! Convert the H3 bound against the incoming pair occupations into
the normalized mass of a marked shared row. -/

@[expose] public section
noncomputable section

namespace NearCritical.Section10.NestLayout

open MeasureTheory Set
open scoped Classical

variable {D d M : ℕ} (Λ : NestLayout D d) [LinearOrder (Finset (Vertex d))]
  (p q : unitInterval) (ρ κ : ℝ) (hκ : 0 < κ)
  (hs : ∀ (γ : SourceRoute D M) (G : Λ.Φ) (j : ℕ) (x : Λ.X), ρ⁻¹ ≤
    localSuccessProbability p q (Λ.Bl₀ G.1 (routeLab M γ.position j))
      (bitSet G.2 (fun z => Λ.succσ G (routeLab M γ.position j) x
        (Λ.view G.1 (routeLab M γ.position j) z))))
  (hsite : ∀ s, κ⁻¹ ≤ coupledProb p q (Λ.siteEvent s))

/-- The normalized mass of a shared tube entered from a marked spread
history. Admissibility is needed only on histories with nonzero weight. -/
theorem firstGood_spread_pending_prefix_le (hρ : 0 < ρ) (G : Λ.Φ)
    (γ γ' : SourceRoute D M) (s : List PairMove) (t t' : ℕ) (x : Λ.X × Λ.X)
    (R : Finset (LBond d))
    (F : NestTrace (Λ.X × Λ.X) s.length → Configuration d × Configuration d → ℝ)
    {A K : ℝ} (hA : 0 ≤ A) :
    let μ := (percolation d p).prod (percolation d q)
    let j := t + leftCount s
    let j' := t' + rightCount s
    let ℓ := routeLab M γ.position j
    let S := Λ.fam G ℓ.site
    let B (δ : SourceRoute D M) i := Λ.Bl₀ G.1 (routeLab M δ.position i)
    let L := (Λ.ruleFirstGood M p q ρ κ hκ hs hsite).toNestRule.kernel
    let T := R ∪ mergedTraceBlocks (B γ) (B γ') s t t'
    let u := mergedTraceLast s x
    let Mark h z :=
      Λ.firstGoodSharedTubeMark G ℓ (u h).1.1.val (u h).2.1.val (u h).1.2 (u h).2.2 z
    let W h z := F h z * mergedTraceMass (L γ G) (L γ' G) z s t t' x h
    (∀ h, IsLocal T (F h)) → (∀ h z, 0 ≤ F h z) → Disjoint T (B γ j) →
    (∀ h z, W h z ≠ 0 → (u h).1.1.val ⊆ S ∧ (u h).2.1.val ⊆ S) →
    (∀ C ∈ S, ∀ C' ∈ S, markedPrefixMass p q (L γ G) (L γ' G) s t t' x
      (fun h z => if C ∈ (u h).1.1.val ∧ C' ∈ (u h).2.1.val then F h z else 0) /
        ρ ^ sharedCount s ≤ A) →
    (∀ C ∈ S, ∀ a b : Bool,
      (∑ C' ∈ S.erase C, μ.real {z | Λ.firstGoodSharedTubeMark G ℓ {C} {C'} a b z}) ≤ K) →
    markedPrefixMass p q (L γ G) (L γ' G) (s ++ [.both]) t t' x (fun h z =>
      let f := (mergedTraceAppend (Λ.X × Λ.X) s [.both]).symm h
      if Mark f.1 z then F f.1 z else 0) / ρ ^ sharedCount (s ++ [.both]) ≤
      ρ * ((S.card : ℝ) * (A * (1 + 4*K))) := by
  intro μ j j' ℓ S B L T u Mark W hF hF₀ hd hvalid hspread hrow
  let H := NestTrace (Λ.X × Λ.X) s.length
  let V (h : H) := (u h).1.1.val ⊆ S ∧ (u h).2.1.val ⊆ S
  let e : Λ.X := (⟨∅, Finset.mem_powerset.mpr (Finset.empty_subset _)⟩, false)
  let l (h : H) := if V h then (u h).1 else e
  let r (h : H) := if V h then (u h).2 else e
  have hL (δ : SourceRoute D M) (i : ℕ) (v y : Λ.X) : IsLocal (B δ i) (L δ G i v y) :=
    stepKernel_isLocal _ _ _ _ y
  have hL₀ (δ : SourceRoute D M) (i : ℕ) (v y : Λ.X) (z : Configuration d × Configuration d) :
      0 ≤ L δ G i v y z :=
    stepKernel_nonneg _ _ _ ((inv_nonneg.mpr hρ.le).trans (hs δ G i v)) y z
  have hW (h : H) : IsLocal T (W h) :=
    (hF h).mul ((mergedTraceMass_isLocal (B γ) (B γ') (L γ G) (L γ' G)
      (hL γ) (hL γ') s t t' x h).mono Finset.subset_union_right)
  have hW₀ (h : H) (z : Configuration d × Configuration d) : 0 ≤ W h z :=
    mul_nonneg (hF₀ h z) (mergedTraceMass_nonneg _ _ (hL₀ γ) (hL₀ γ') z s t t' x h)
  have hzero (h : H) (hn : ¬ V h) (z : Configuration d × Configuration d) : W h z = 0 := by
    by_contra hw
    exact hn (hvalid h z hw)
  have hl (h : H) : (l h).1.val ⊆ S := by
    by_cases hv : V h
    · rw [show l h = (u h).1 from if_pos hv]
      exact hv.1
    · rw [show l h = e from if_neg hv]
      exact Finset.empty_subset _
  have hr (h : H) : (r h).1.val ⊆ S := by
    by_cases hv : V h
    · rw [show r h = (u h).2 from if_pos hv]
      exact hv.2
    · rw [show r h = e from if_neg hv]
      exact Finset.empty_subset _
  have hspread' (C : Finset (Vertex d)) (hC : C ∈ S) (C' : Finset (Vertex d)) (hC' : C' ∈ S) :
      (∑ h : H, if C ∈ (l h).1.val ∧ C' ∈ (r h).1.val then (∫ z, W h z ∂μ) else 0) ≤
        A * ρ ^ sharedCount s := by
    have hs₀ := (div_le_iff₀ (pow_pos hρ _)).mp (hspread C hC C' hC')
    refine le_trans (le_of_eq ?_) hs₀
    unfold markedPrefixMass
    have hterm (h : H) : IsLocal T (fun z =>
        (if C ∈ (u h).1.1.val ∧ C' ∈ (u h).2.1.val then F h z else 0) *
          mergedTraceMass (L γ G) (L γ' G) z s t t' x h) := by
      by_cases he : C ∈ (u h).1.1.val ∧ C' ∈ (u h).2.1.val
      · simpa only [if_pos he] using hW h
      · simpa only [if_neg he, zero_mul] using isLocal_const T 0
    rw [integral_finsetSum _ (fun h _ => (hterm h).integrable p q)]
    refine Finset.sum_congr rfl fun h _ => ?_
    by_cases hv : V h
    · by_cases he : C ∈ (u h).1.1.val ∧ C' ∈ (u h).2.1.val
      · simp only [l,r,if_pos hv,if_pos he,W] <;> rfl
      · simp only [l,r,if_pos hv,if_neg he,zero_mul,integral_zero]
    · have hw : (fun z => W h z) = fun _ => 0 := funext (hzero h hv)
      have hwint : (∫ z, W h z ∂μ) = 0 := by rw [hw, integral_zero]
      rw [hwint, ite_self]
      by_cases he : C ∈ (u h).1.1.val ∧ C' ∈ (u h).2.1.val
      · simp only [if_pos he]
        exact hwint.symm
      · simp only [if_neg he,zero_mul,integral_zero]
  let P h := {z | Λ.firstGoodSharedTubeMark G ℓ (l h).1.val (r h).1.val (l h).2 (r h).2 z}
  let J h (y : Λ.X × Λ.X) z := L γ G j (l h) y.1 z * L γ' G j' (r h) y.2 z
  have hstep := Λ.firstGood_spread_pending_tube_step_le p q ρ κ hκ hs hsite hρ G γ γ'
    j j' T hd l r W hW hW₀ (mul_nonneg hA (pow_nonneg hρ.le _)) hl hr hspread' hrow
  have heq : markedPrefixMass p q (L γ G) (L γ' G) (s ++ [.both]) t t' x (fun h z =>
      let f := (mergedTraceAppend (Λ.X × Λ.X) s [.both]).symm h
      if Mark f.1 z then F f.1 z else 0) =
      ∑ h : H, ∫ z, (P h).indicator (fun z => W h z * ∑ y, J h y z) z ∂μ := by
    rw [markedPrefixMass_snoc p q (L γ G) (L γ' G) s .both t t' x
      (fun h _ z => if Mark h z then F h z else 0)]
    have hpt (h : H) (y : Λ.X × Λ.X) (z : Configuration d × Configuration d) :
        (if Mark h z then F h z else 0) * mergedTraceMass (L γ G) (L γ' G) z
            (s ++ [.both]) t t' x (mergedTraceAppend (Λ.X × Λ.X) s [.both] (h,(y,PUnit.unit))) =
          (P h).indicator (fun z => W h z * J h y z) z := by
      rw [mergedTraceMass_snoc]
      by_cases hv : V h
      · have hP : z ∈ P h ↔ Mark h z := by simp only [P,mem_setOf_eq,l,r,if_pos hv,Mark]
        by_cases hm : Mark h z
        · rw [if_pos hm, indicator_of_mem (hP.mpr hm)]
          simp only [J,l,r,if_pos hv,pairMoveKernel,W,u,j,j']
          exact (mul_assoc _ _ _).symm
        · rw [if_neg hm, zero_mul, indicator_of_notMem (fun hp => hm (hP.mp hp))]
      · have hw := hzero h hv z
        rw [show (P h).indicator (fun z => W h z * J h y z) z = 0 by
          by_cases hz : z ∈ P h
          · rw [indicator_of_mem hz, hw, zero_mul]
          · exact indicator_of_notMem hz _]
        by_cases hm : Mark h z
        · rw [if_pos hm, ← mul_assoc]
          exact mul_eq_zero_of_left hw _
        · rw [if_neg hm, zero_mul]
    simp_rw [hpt]
    have hI (h : H) : Integrable (fun z => ∑ y : Λ.X × Λ.X,
        (P h).indicator (fun z => W h z * J h y z) z) μ := by
      apply integrable_finsetSum
      intro y _
      have hP : MeasurableSet (P h) :=
        (Λ.firstGoodSharedTubeMark_readsOnly G ℓ (l h).1.val (r h).1.val (l h).2 (r h).2).measurableSet
      exact (((hW h).mul_union ((hL γ j (l h) y.1).mul_union
        (hL γ' j' (r h) y.2))).integrable p q).indicator hP
    rw [integral_finsetSum _ (fun h _ => hI h)]
    refine Finset.sum_congr rfl fun h _ => integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    change (∑ y : Λ.X × Λ.X, (P h).indicator (fun z => W h z * J h y z) z) =
      (P h).indicator (fun z => W h z * ∑ y, J h y z) z
    by_cases hp : z ∈ P h
    · simp only [indicator_of_mem hp, Finset.mul_sum]
    · simp only [indicator_of_notMem hp, Finset.sum_const_zero]
  rw [heq, sharedCount_append, pow_add, show sharedCount [.both] = 1 from rfl, pow_one]
  refine (div_le_div_of_nonneg_right hstep (mul_nonneg (pow_nonneg hρ.le _) hρ.le)).trans_eq ?_
  field_simp [ne_of_gt hρ, pow_ne_zero _ (ne_of_gt hρ)] <;> ring

end NearCritical.Section10.NestLayout
