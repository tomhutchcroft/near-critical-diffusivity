module

public import NearCritical.Section10FirstGoodPhaseRow
public import NearCritical.Section10MergedTraceStep

/-! Apply the opposite-sign bridge estimate to the actual shared row. -/

@[expose] public section
noncomputable section

namespace NearCritical.Section10.NestLayout

open MeasureTheory Set
open scoped Classical

variable {D d M : ℕ} (Λ : NestLayout D d) [LinearOrder (Finset (Vertex d))]
  (p q : unitInterval) (ρ κ : ℝ) (hκ : 0 < κ)
  (hs : ∀ (γ : SourceRoute D M) (G : Λ.Φ) (t : ℕ) (x : Λ.X), ρ⁻¹ ≤
    localSuccessProbability p q (Λ.Bl₀ G.1 (routeLab M γ.position t))
      (bitSet G.2 (fun z => Λ.succσ G (routeLab M γ.position t) x
        (Λ.view G.1 (routeLab M γ.position t) z))))
  (hsiteProb : ∀ s, κ⁻¹ ≤ coupledProb p q (Λ.siteEvent s))

theorem firstGood_usedKernel_apply (γ : SourceRoute D M) (G : Λ.Φ)
    (active : ℕ → Bool) (t : ℕ) (x y : Λ.X) (z : Configuration d × Configuration d) :
    let L := (Λ.ruleFirstGood M p q ρ κ hκ hs hsiteProb).toNestRule.kernel γ G
    usedMaskedKernel active (Λ.firstGoodMaskBase p q ρ κ hκ hs hsiteProb γ G active) t x y z =
      if active t = true then L t (x.1,y.2) (y.1,false) z
      else if y.2 = false then L t (x.1,false) (y.1,false) z else 0 := by
  intro L
  unfold usedMaskedKernel firstGoodMaskBase
  split_ifs with h
  · change 2 * L t (x.1,y.2) (y.1,false) z / 2 = _
    ring
  · rfl
  · rfl

theorem firstGood_usedKernel_isLocal (γ : SourceRoute D M) (G : Λ.Φ)
    (active : ℕ → Bool) (t : ℕ) (x y : Λ.X) :
    IsLocal (Λ.Bl₀ G.1 (routeLab M γ.position t))
      (usedMaskedKernel active (Λ.firstGoodMaskBase p q ρ κ hκ hs hsiteProb γ G active) t x y) := by
  let L := (Λ.ruleFirstGood M p q ρ κ hκ hs hsiteProb).toNestRule.kernel γ G
  have hloc (u v : Λ.X) : IsLocal (Λ.Bl₀ G.1 (routeLab M γ.position t)) (L t u v) :=
    stepKernel_isLocal _ _ _ _ v
  have he := funext (Λ.firstGood_usedKernel_apply p q ρ κ hκ hs hsiteProb γ G active t x y)
  change _ = (fun z => if active t = true then L t (x.1,y.2) (y.1,false) z
    else if y.2 = false then L t (x.1,false) (y.1,false) z else 0) at he
  rw [he]
  by_cases ht : active t = true
  · simpa only [if_pos ht] using hloc (x.1,y.2) (y.1,false)
  · by_cases hy : y.2 = false
    · simp only [if_neg ht, if_pos hy]
      exact hloc (x.1,false) (y.1,false)
    · simp only [if_neg ht, if_neg hy]
      exact isLocal_const _ 0

theorem firstGood_usedKernel_nonneg (hρ : 0 < ρ) (γ : SourceRoute D M) (G : Λ.Φ)
    (active : ℕ → Bool) (t : ℕ) (x y : Λ.X) (z : Configuration d × Configuration d) :
    0 ≤ usedMaskedKernel active (Λ.firstGoodMaskBase p q ρ κ hκ hs hsiteProb γ G active) t x y z := by
  rw [Λ.firstGood_usedKernel_apply p q ρ κ hκ hs hsiteProb γ G active t x y z]
  have h (u v : Λ.X) :
      0 ≤ (Λ.ruleFirstGood M p q ρ κ hκ hs hsiteProb).toNestRule.kernel γ G t u v z :=
    stepKernel_nonneg _ _ _ ((inv_nonneg.mpr hρ.le).trans (hs γ G t u)) v z
  split_ifs
  · exact h _ _
  · exact h _ _
  · exact le_rfl

/-- At a shared physical move, the normalized weight that continues a phase
is at most two thirds. The test uses the actual whole-nest bridge mark,
and the sign is stored by the used-sign kernel on the current move. -/
theorem firstGood_shared_persistence_row
    (hρ : 0 < ρ) (hρ' : ρ ≤ 9/8) (G : Λ.Φ)
    (γ γ' : SourceRoute D M) (t t' : ℕ) (active active' : ℕ → Bool)
    (ht : active t = true) (ht' : active' t' = true)
    (x x' : Λ.X)
    (hx : Λ.moveCtx G (routeLab M γ.position t) x)
    (hx' : Λ.moveCtx G (routeLab M γ'.position t') x') :
    let ℓ := routeLab M γ.position t
    let μ := (percolation d p).prod (percolation d q)
    let A (a b : Bool) := {z | Λ.firstGoodSharedTubeMark G ℓ x.1.val x'.1.val a b z}
    let K := usedMaskedKernel active (Λ.firstGoodMaskBase p q ρ κ hκ hs hsiteProb γ G active)
    let K' := usedMaskedKernel active' (Λ.firstGoodMaskBase p q ρ κ hκ hs hsiteProb γ' G active')
    (∀ a b, a ≠ b → μ.real (A a b) ≤ 1/40) →
    (∫ z, ∑ y : Λ.X × Λ.X, (A y.1.2 y.2.2).indicator
      (fun z => K t x y.1 z * K' t' x' y.2 z) z ∂μ) ≤ 2/3 := by
  intro ℓ μ A K K' hrare
  let L := (Λ.ruleFirstGood M p q ρ κ hκ hs hsiteProb).toNestRule.kernel γ G
  let L' := (Λ.ruleFirstGood M p q ρ κ hκ hs hsiteProb).toNestRule.kernel γ' G
  have hk (z : Configuration d × Configuration d) (y : Λ.X) :
      K t x y z = L t (x.1,y.2) (y.1,false) z := by
    have he := Λ.firstGood_usedKernel_apply p q ρ κ hκ hs hsiteProb γ G active t x y z
    change K t x y z = if active t = true then L t (x.1,y.2) (y.1,false) z
      else if y.2 = false then L t (x.1,false) (y.1,false) z else 0 at he
    rw [he, if_pos ht]
  have hk' (z : Configuration d × Configuration d) (y : Λ.X) :
      K' t' x' y z = L' t' (x'.1,y.2) (y.1,false) z := by
    have he := Λ.firstGood_usedKernel_apply p q ρ κ hκ hs hsiteProb γ' G active' t' x' y z
    change K' t' x' y z = if active' t' = true then L' t' (x'.1,y.2) (y.1,false) z
      else if y.2 = false then L' t' (x'.1,false) (y.1,false) z else 0 at he
    rw [he, if_pos ht']
  have h₁ (a : Bool) (z : Configuration d × Configuration d) :=
    Λ.firstGood_move_sign_row_le p q ρ κ hκ hs hsiteProb hρ γ G t (x.1,a) z hx
  have h₂ (b : Bool) (z : Configuration d × Configuration d) :=
    Λ.firstGood_move_sign_row_le p q ρ κ hκ hs hsiteProb hρ γ' G t' (x'.1,b) z hx'
  let w (a b : Bool) (z : Configuration d × Configuration d) :=
    (∑ y : ↥Λ.P, L t (x.1,a) (y,false) z) * (∑ y' : ↥Λ.P, L' t' (x'.1,b) (y',false) z)
  have hw (a b : Bool) (z : Configuration d × Configuration d) :
      0 ≤ w a b z ∧ w a b z ≤ (ρ/2)^2 := by
    have h₁₀ : 0 ≤ ∑ y : ↥Λ.P, L t (x.1,a) (y,false) z :=
      Finset.sum_nonneg fun y _ => (h₁ a z).1 (y,false)
    have h₂₀ : 0 ≤ ∑ y : ↥Λ.P, L' t' (x'.1,b) (y,false) z :=
      Finset.sum_nonneg fun y _ => (h₂ b z).1 (y,false)
    exact ⟨mul_nonneg h₁₀ h₂₀, by
      rw [pow_two]
      exact mul_le_mul (h₁ a z).2 (h₂ b z).2 h₂₀ (by positivity)⟩
  have hm (a b : Bool) : MeasurableSet (A a b) :=
    (Λ.firstGoodSharedTubeMark_readsOnly G ℓ x.1.val x'.1.val a b).measurableSet
  have hA (a b : Bool) : μ.real (A a b) ≤ if a = b then 1 else 1/40 := by
    by_cases hab : a = b
    · rw [if_pos hab]
      exact (measureReal_mono (subset_univ _) (measure_ne_top μ univ)).trans_eq probReal_univ
    · simpa only [if_neg hab] using hrare a b hab
  have hsum (z : Configuration d × Configuration d) :
      (∑ y : Λ.X × Λ.X, (A y.1.2 y.2.2).indicator
        (fun z => K t x y.1 z * K' t' x' y.2 z) z) =
      ∑ a : Bool, ∑ b : Bool, (A a b).indicator (w a b) z := by
    simp only [Set.indicator_apply, hk, hk', Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    have hswap (y : ↥Λ.P) :
        (∑ y' : ↥Λ.P, ∑ b : Bool, if z ∈ A a b then
          L t (x.1,a) (y,false) z * L' t' (x'.1,b) (y',false) z else 0) =
        ∑ b : Bool, ∑ y' : ↥Λ.P, if z ∈ A a b then
          L t (x.1,a) (y,false) z * L' t' (x'.1,b) (y',false) z else 0 :=
      Finset.sum_comm
    simp_rw [hswap]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b _
    by_cases hz : z ∈ A a b
    · simp only [if_pos hz, w, Fintype.sum_mul_sum]
    · simp [hz]
  calc
    _ = ∫ z, ∑ a : Bool, ∑ b : Bool, (A a b).indicator (w a b) z ∂μ :=
      integral_congr_ae (Filter.Eventually.of_forall hsum)
    _ ≤ ∫ z, ∑ a : Bool, ∑ b : Bool, (A a b).indicator (fun _ => (ρ/2)^2) z ∂μ := by
      refine integral_mono_of_nonneg (Filter.Eventually.of_forall ?_)
        (integrable_finsetSum _ fun a _ =>
          integrable_finsetSum _ fun b _ => (integrable_const _).indicator (hm a b))
        (Filter.Eventually.of_forall ?_)
      · intro z
        apply Finset.sum_nonneg
        intro a _
        apply Finset.sum_nonneg
        intro b _
        by_cases hz : z ∈ A a b <;> simp [hz, (hw a b z).1]
      · intro z
        apply Finset.sum_le_sum
        intro a _
        apply Finset.sum_le_sum
        intro b _
        by_cases hz : z ∈ A a b <;> simp [hz, (hw a b z).2]
    _ = ∑ a : Bool, ∑ b : Bool, μ.real (A a b) * (ρ/2)^2 := by
      rw [integral_finsetSum _ (fun a _ =>
        integrable_finsetSum _ fun b _ => (integrable_const _).indicator (hm a b))]
      apply Finset.sum_congr rfl
      intro a _
      rw [integral_finsetSum _ (fun b _ => (integrable_const _).indicator (hm a b))]
      apply Finset.sum_congr rfl
      intro b _
      rw [integral_indicator_const _ (hm a b), smul_eq_mul]
    _ ≤ ∑ a : Bool, ∑ b : Bool, (if a = b then 1 else 1/40) * (ρ/2)^2 :=
      Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ =>
        mul_le_mul_of_nonneg_right (hA a b) (sq_nonneg _)
    _ = (41/20:ℝ) * (ρ/2)^2 := by norm_num [Fintype.sum_bool] <;> ring
    _ ≤ 2/3 := by
      have hpow : (ρ/2)^2 ≤ (9/16:ℝ)^2 :=
        (sq_le_sq₀ (by positivity) (by norm_num)).mpr (by linarith)
      exact (mul_le_mul_of_nonneg_left hpow (by norm_num)).trans (by norm_num)

end NearCritical.Section10.NestLayout
