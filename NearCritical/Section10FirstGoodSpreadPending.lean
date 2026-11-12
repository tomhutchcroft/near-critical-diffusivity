module

public import NearCritical.Section10FirstGoodSpreadEntry

/-! Entry into a shared-tube mark when the pending signs are part of the
past. A common parent is charged separately from distinct parents. -/

@[expose] public section
noncomputable section

namespace NearCritical.Section10.NestLayout

open MeasureTheory Set
open scoped Classical

/-- The entire pending-sign row is bounded pointwise by the reciprocal
of the uniform lower bound on success probability. -/
theorem firstGood_pending_row_cap {D d M : ℕ} (Λ : NestLayout D d)
    [LinearOrder (Finset (Vertex d))] (p q : unitInterval) (ρ κ : ℝ)
    (hκ : 0 < κ)
    (hs : ∀ (γ : SourceRoute D M) (G : Λ.Φ) (j : ℕ) (x : Λ.X), ρ⁻¹ ≤
      localSuccessProbability p q (Λ.Bl₀ G.1 (routeLab M γ.position j))
        (bitSet G.2 (fun z => Λ.succσ G (routeLab M γ.position j) x
          (Λ.view G.1 (routeLab M γ.position j) z))))
    (hsite : ∀ s, κ⁻¹ ≤ coupledProb p q (Λ.siteEvent s))
    (hρ : 0 < ρ) (γ : SourceRoute D M) (G : Λ.Φ) (j : ℕ) (x : Λ.X)
    (z : Configuration d × Configuration d) :
    let R := (Λ.ruleFirstGood M p q ρ κ hκ hs hsite).toNestRule
    (∀ y, 0 ≤ R.kernel γ G j x y z) ∧ (∑ y, R.kernel γ G j x y z) ≤ ρ := by
  intro R
  let T := Λ.Bl₀ G.1 (routeLab M γ.position j)
  let S : Set (T → Bool) := R.a γ G j x
  let O : (T → Bool) → Finset Λ.X := R.o γ G j x
  let s := localSuccessProbability p q T S
  have hs' : ρ⁻¹ ≤ s := hs γ G j x
  have hs₀ : 0 < s := (inv_pos.mpr hρ).trans_le hs'
  refine ⟨fun y => stepKernel_nonneg T S O hs₀.le y z, ?_⟩
  change (∑ y : Λ.X, stepKernel T S O s y z) ≤ ρ
  rw [stepKernel_sum T S O (R.ho γ G j x)]
  split_ifs
  · simpa only [one_mul] using (inv_le_comm₀ hs₀ hρ).mpr hs'
  · simpa only [zero_mul] using hρ.le

/-- A pair occupation bound on the past controls a fresh shared-tube mark.
A diagonal pair costs at most one, and the four sign pairs each contribute
the distinct-parent row bound. -/
theorem firstGood_spread_pending_tube_entry_le {D d : ℕ} (Λ : NestLayout D d)
    {H : Type*} [Fintype H] (p q : unitInterval) (G : Λ.Φ) (ℓ : RouteLabel D)
    (R : Finset (LBond d)) (hd : Disjoint R (Λ.Bl₀ G.1 ℓ))
    (N N' : H → Finset (Finset (Vertex d))) (a b : H → Bool)
    (hN : ∀ h, N h ⊆ Λ.fam G ℓ.site) (hN' : ∀ h, N' h ⊆ Λ.fam G ℓ.site)
    (W : H → Configuration d × Configuration d → ℝ)
    (hW : ∀ h, IsLocal R (W h)) (hW₀ : ∀ h z, 0 ≤ W h z)
    {A K : ℝ} (hA : 0 ≤ A) :
    let μ := (percolation d p).prod (percolation d q)
    let S := Λ.fam G ℓ.site
    (∀ C ∈ S, ∀ E ∈ S,
      (∑ h, if C ∈ N h ∧ E ∈ N' h then (∫ z, W h z ∂μ) else 0) ≤ A) →
    (∀ C ∈ S, ∀ s t : Bool,
      (∑ E ∈ S.erase C, μ.real {z | Λ.firstGoodSharedTubeMark G ℓ {C} {E} s t z}) ≤ K) →
    (∑ h, ∫ z, ({z | Λ.firstGoodSharedTubeMark G ℓ (N h) (N' h) (a h) (b h) z}).indicator
      (W h) z ∂μ) ≤ (S.card : ℝ) * (A * (1 + 4*K)) := by
  intro μ S hspread hrow
  let I := S.product S
  let B (i : Finset (Vertex d) × Finset (Vertex d)) (h : H) := i.1 ∈ N h ∧ i.2 ∈ N' h
  let P (C E : Finset (Vertex d)) (s : Bool × Bool) :=
    {z | Λ.firstGoodSharedTubeMark G ℓ {C} {E} s.1 s.2 z}
  let F (i : Finset (Vertex d) × Finset (Vertex d))
      (z : Configuration d × Configuration d) := i.1 = i.2 ∨ ∃ s : Bool × Bool, z ∈ P i.1 i.2 s
  let c (i : Finset (Vertex d) × Finset (Vertex d)) := μ.real {z | F i z}
  let m (h : H) := ∫ z, W h z ∂μ
  have hF (i : Finset (Vertex d) × Finset (Vertex d)) : ReadsOnly (Λ.Bl₀ G.1 ℓ) (F i) := by
    intro z z' hz
    apply propext
    change (i.1 = i.2 ∨ ∃ s : Bool × Bool, z ∈ P i.1 i.2 s) ↔
      (i.1 = i.2 ∨ ∃ s : Bool × Bool, z' ∈ P i.1 i.2 s)
    apply or_congr Iff.rfl
    apply exists_congr
    intro s
    exact Iff.of_eq (Λ.firstGoodSharedTubeMark_readsOnly G ℓ {i.1} {i.2} s.1 s.2 z z' hz)
  have hh (h : H) :
      (∫ z, ({z | Λ.firstGoodSharedTubeMark G ℓ (N h) (N' h) (a h) (b h) z}).indicator
        (W h) z ∂μ) ≤ ∑ i ∈ I, (if B i h then m h else 0) * c i := by
    let U := {z | ∃ i ∈ I, B i h ∧ F i z}
    have hu' : ReadsOnly (Λ.Bl₀ G.1 ℓ) (fun z => z ∈ U) := by
      intro z z' hz
      apply propext
      change (∃ i ∈ I, B i h ∧ F i z) ↔ (∃ i ∈ I, B i h ∧ F i z')
      exact exists_congr fun i => and_congr Iff.rfl (and_congr Iff.rfl (Iff.of_eq (hF i z z' hz)))
    have hsub : {z | Λ.firstGoodSharedTubeMark G ℓ (N h) (N' h) (a h) (b h) z} ⊆ U := by
      intro z hz
      obtain ⟨C,hC,E,hE,hCE⟩ :=
        (Λ.firstGoodSharedTubeMark_iff_exists_pair G ℓ (N h) (N' h) (a h) (b h) z).mp hz
      exact ⟨(C,E),Finset.mem_product.mpr ⟨hN h hC,hN' h hE⟩,
        ⟨hC,hE⟩,Or.inr ⟨(a h,b h),hCE⟩⟩
    have hle : (∫ z, ({z | Λ.firstGoodSharedTubeMark G ℓ (N h) (N' h) (a h) (b h) z}).indicator
        (W h) z ∂μ) ≤ ∫ z, U.indicator (W h) z ∂μ := by
      refine integral_mono_of_nonneg (Filter.Eventually.of_forall ?_)
        (((hW h).integrable p q).indicator hu'.measurableSet) (Filter.Eventually.of_forall ?_)
      · intro z
        exact indicator_nonneg (fun z _ => hW₀ h z) _
      · intro z
        exact indicator_le_indicator_of_subset hsub (fun z => hW₀ h z) z
    refine hle.trans ((weighted_fresh_union_le p q R (Λ.Bl₀ G.1 ℓ) hd I (W h) (hW h) (hW₀ h)
      (fun i _ => B i h) F (fun _ _ _ _ _ => rfl) (fun i _ => hF i)).trans_eq ?_)
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : B i h <;> simp [hi, m, c, μ]
  have hc (C E : Finset (Vertex d)) (hne : E ≠ C) :
      c (C,E) ≤ ∑ s : Bool × Bool, μ.real (P C E s) := by
    have hsub : {z | F (C,E) z} ⊆ ⋃ s ∈ (Finset.univ : Finset (Bool × Bool)), P C E s := by
      rintro z (he | ⟨s,hs⟩)
      · exact (hne he.symm).elim
      · exact mem_iUnion.mpr ⟨s,mem_iUnion.mpr ⟨Finset.mem_univ _,hs⟩⟩
    exact (measureReal_mono hsub (measure_ne_top _ _)).trans (measureReal_biUnion_finset_le _ _)
  have hsum (C : Finset (Vertex d)) (hC : C ∈ S) :
      (∑ E ∈ S, c (C,E)) ≤ 1 + 4*K := by
    have hdiag : c (C,C) ≤ 1 :=
      (measureReal_mono (subset_univ _) (measure_ne_top μ univ)).trans_eq probReal_univ
    rw [← Finset.sum_erase_add _ _ hC]
    have hoff : (∑ E ∈ S.erase C, c (C,E)) ≤ 4*K := calc
      _ ≤ ∑ E ∈ S.erase C, ∑ s : Bool × Bool, μ.real (P C E s) :=
        Finset.sum_le_sum fun E hE => hc C E (Finset.mem_erase.mp hE).1
      _ = ∑ s : Bool × Bool, ∑ E ∈ S.erase C, μ.real (P C E s) := Finset.sum_comm
      _ ≤ ∑ _s : Bool × Bool, K := Finset.sum_le_sum fun s _ => hrow C hC s.1 s.2
      _ = _ := by simp [Fintype.card_prod, nsmul_eq_mul]
    linarith
  calc
    _ ≤ ∑ h, ∑ i ∈ I, (if B i h then m h else 0) * c i :=
      Finset.sum_le_sum fun h _ => hh h
    _ = ∑ i ∈ I, (∑ h, if B i h then m h else 0) * c i := by
      rw [Finset.sum_comm]
      simp only [Finset.sum_mul]
    _ ≤ ∑ C ∈ S, A * (1 + 4*K) := by
      rw [show I = S ×ˢ S from rfl, Finset.sum_product]
      apply Finset.sum_le_sum
      intro C hC
      calc
        _ ≤ ∑ E ∈ S, A * c (C,E) := Finset.sum_le_sum fun E hE =>
          mul_le_mul_of_nonneg_right (hspread C hC E hE) measureReal_nonneg
        _ ≤ A * (1 + 4*K) := by
          rw [← Finset.mul_sum]
          exact mul_le_mul_of_nonneg_left (hsum C hC) hA
    _ = _ := by simp [nsmul_eq_mul]

/-- Including both normalized child rows costs at most `ρ²` in the
spread bound on the incoming shared-tube mark. Here `W` is the full
prefix weight and `x, x'` are its two final states. -/
theorem firstGood_spread_pending_tube_step_le {D d M : ℕ} (Λ : NestLayout D d)
    {H : Type*} [Fintype H] [LinearOrder (Finset (Vertex d))]
    (p q : unitInterval) (ρ κ : ℝ) (hκ : 0 < κ)
    (hs : ∀ (γ : SourceRoute D M) (G : Λ.Φ) (j : ℕ) (x : Λ.X), ρ⁻¹ ≤
      localSuccessProbability p q (Λ.Bl₀ G.1 (routeLab M γ.position j))
        (bitSet G.2 (fun z => Λ.succσ G (routeLab M γ.position j) x
          (Λ.view G.1 (routeLab M γ.position j) z))))
    (hsite : ∀ s, κ⁻¹ ≤ coupledProb p q (Λ.siteEvent s))
    (hρ : 0 < ρ) (G : Λ.Φ) (γ γ' : SourceRoute D M) (j j' : ℕ)
    (R : Finset (LBond d)) (hd : Disjoint R (Λ.Bl₀ G.1 (routeLab M γ.position j)))
    (x x' : H → Λ.X) (W : H → Configuration d × Configuration d → ℝ)
    (hW : ∀ h, IsLocal R (W h)) (hW₀ : ∀ h z, 0 ≤ W h z)
    {A K : ℝ} (hA : 0 ≤ A) :
    let μ := (percolation d p).prod (percolation d q)
    let ℓ := routeLab M γ.position j
    let S := Λ.fam G ℓ.site
    let L := (Λ.ruleFirstGood M p q ρ κ hκ hs hsite).toNestRule.kernel
    let E h := {z | Λ.firstGoodSharedTubeMark G ℓ (x h).1.val (x' h).1.val (x h).2 (x' h).2 z}
    (∀ h, (x h).1.val ⊆ S) → (∀ h, (x' h).1.val ⊆ S) →
    (∀ C ∈ S, ∀ C' ∈ S, (∑ h, if C ∈ (x h).1.val ∧ C' ∈ (x' h).1.val
      then (∫ z, W h z ∂μ) else 0) ≤ A) →
    (∀ C ∈ S, ∀ a b : Bool,
      (∑ C' ∈ S.erase C, μ.real {z | Λ.firstGoodSharedTubeMark G ℓ {C} {C'} a b z}) ≤ K) →
    (∑ h, ∫ z, (E h).indicator (fun z => W h z *
      (∑ y : Λ.X × Λ.X, L γ G j (x h) y.1 z * L γ' G j' (x' h) y.2 z)) z ∂μ) ≤
      ρ^2 * ((S.card : ℝ) * (A * (1 + 4*K))) := by
  intro μ ℓ S L E hN hN' hspread hrow
  refine le_trans (b := ρ^2 * ∑ h, ∫ z, (E h).indicator (W h) z ∂μ) ?_ ?_
  swap
  · exact mul_le_mul_of_nonneg_left
      (Λ.firstGood_spread_pending_tube_entry_le p q G ℓ R hd
        (fun h => (x h).1.val) (fun h => (x' h).1.val)
        (fun h => (x h).2) (fun h => (x' h).2) hN hN' W hW hW₀ hA hspread hrow)
      (sq_nonneg ρ)
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun h _ => ?_
  rw [← integral_const_mul]
  have hEm : MeasurableSet (E h) :=
    (Λ.firstGoodSharedTubeMark_readsOnly G ℓ (x h).1.val (x' h).1.val (x h).2 (x' h).2).measurableSet
  have hprod (z : Configuration d × Configuration d) :
      0 ≤ (∑ y : Λ.X × Λ.X, L γ G j (x h) y.1 z * L γ' G j' (x' h) y.2 z) ∧
      (∑ y : Λ.X × Λ.X, L γ G j (x h) y.1 z * L γ' G j' (x' h) y.2 z) ≤ ρ^2 := by
    obtain ⟨hl,hL⟩ := Λ.firstGood_pending_row_cap p q ρ κ hκ hs hsite hρ γ G j (x h) z
    obtain ⟨hr,hR⟩ := Λ.firstGood_pending_row_cap p q ρ κ hκ hs hsite hρ γ' G j' (x' h) z
    refine ⟨Finset.sum_nonneg (fun y _ => mul_nonneg (hl y.1) (hr y.2)), ?_⟩
    rw [Fintype.sum_prod_type]
    simp only [← Finset.mul_sum, ← Finset.sum_mul]
    rw [pow_two]
    exact mul_le_mul hL hR (Finset.sum_nonneg (fun y _ => hr y)) hρ.le
  refine integral_mono_of_nonneg (Filter.Eventually.of_forall ?_)
    (((hW h).integrable p q).indicator hEm |>.const_mul _) (Filter.Eventually.of_forall ?_)
  · intro z
    exact indicator_nonneg (fun z _ => mul_nonneg (hW₀ h z) (hprod z).1) _
  · intro z
    change (E h).indicator (fun z => W h z *
      (∑ y : Λ.X × Λ.X, L γ G j (x h) y.1 z * L γ' G j' (x' h) y.2 z)) z ≤
      ρ^2 * (E h).indicator (W h) z
    by_cases hz : z ∈ E h
    · rw [indicator_of_mem hz, indicator_of_mem hz, mul_comm (ρ^2)]
      exact mul_le_mul_of_nonneg_left (hprod z).2 (hW₀ h z)
    · simp only [indicator_of_notMem hz, mul_zero, le_rfl]

end NearCritical.Section10.NestLayout
