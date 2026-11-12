module

public import NearCritical.Section10Survivor

/-! Integrate the fixed-reveal marked bound against the actual cube
weights of a pair of routes. -/

@[expose] public section
noncomputable section

namespace NearCritical.Section10

open MeasureTheory
open scoped Classical

/-- Each revealed weight times its frozen observable is integrable,
since the reveal values form a finite partition into local events. -/
theorem revealed_local_marked_mass_integrable {d : ℕ} {Φ : Type*} [Fintype Φ]
    (p q : unitInterval) (ρ : Configuration d × Configuration d → Φ)
    (S T : Φ → Finset (LBond d))
    (hρ : ∀ F, IsLocal (S F) (fun z => if ρ z = F then (1:ℝ) else 0))
    (w : Φ → ℝ) (f : Φ → Configuration d × Configuration d → ℝ)
    (hf : ∀ F, IsLocal (T F) (f F)) :
    Integrable (fun z => w (ρ z) * f (ρ z) z) ((percolation d p).prod (percolation d q)) := by
  let V (F : Φ) (z : Configuration d × Configuration d) :=
    ((if ρ z = F then (1:ℝ) else 0) * w F) * f F z
  have he : (fun z => w (ρ z) * f (ρ z) z) = fun z => ∑ F, V F z := by
    funext z
    rw [Finset.sum_eq_single (ρ z)]
    · simp only [V, if_pos rfl,ite_true,one_mul]
    · intro F _ hF
      simp only [V,if_neg (Ne.symm hF),zero_mul]
    · simp
  rw [he]
  exact integrable_finsetSum _ (fun F _ => (((hρ F).mul (isLocal_const _ _)).mul_union (hf F)).integrable p q)

/-- On each realized reveal with positive weight, the fresh marked
expectation is multiplied by the probability and weight of that atom. -/
theorem revealed_local_marked_mass_le {d : ℕ} {Φ : Type*} [Fintype Φ]
    (p q : unitInterval) (ρ : Configuration d × Configuration d → Φ)
    (S T : Φ → Finset (LBond d))
    (hρ : ∀ F, IsLocal (S F) (fun z => if ρ z = F then (1:ℝ) else 0))
    (hd : ∀ F, Disjoint (S F) (T F))
    (w : Φ → ℝ) (hw : ∀ F, 0 ≤ w F)
    (f : Φ → Configuration d × Configuration d → ℝ)
    (hf : ∀ F, IsLocal (T F) (f F)) (A : ℝ) :
    let μ := (percolation d p).prod (percolation d q)
    (∀ F, (∃ z, ρ z = F) → w F ≠ 0 → (∫ z, f F z ∂μ) ≤ A) →
    (∫ z, w (ρ z) * f (ρ z) z ∂μ) ≤ A * (∫ z, w (ρ z) ∂μ) := by
  intro μ hA
  let V (F : Φ) (z : Configuration d × Configuration d) :=
    (if ρ z = F then (1:ℝ) else 0) * w F
  have hV (F : Φ) : IsLocal (S F) (V F) := (hρ F).mul (isLocal_const _ _)
  have hV₀ (F : Φ) (z : Configuration d × Configuration d) : 0 ≤ V F z := by
    unfold V
    split_ifs
    · simpa only [one_mul] using hw F
    · rw [zero_mul]
  have hterm (F : Φ) : (∫ z, V F z * f F z ∂μ) ≤ A * ∫ z, V F z ∂μ := by
    rw [IsLocal.integral_mul p q (hd F) (hV F) (hf F), mul_comm A]
    by_cases h : (∃ z, ρ z = F) ∧ w F ≠ 0
    · exact mul_le_mul_of_nonneg_left (hA F h.1 h.2) (integral_nonneg (hV₀ F))
    · have he : (fun z => V F z) = fun _ => 0 := by
        funext z
        by_cases hz : ρ z = F
        · have hw₀ : w F = 0 := by
            by_contra hw'
            exact h ⟨⟨z,hz⟩,hw'⟩
          simp only [V,hz,if_true,hw₀,mul_zero]
        · simp only [V,hz,if_false,zero_mul]
      rw [he, integral_zero, zero_mul, zero_mul]
  have hsplit (g : Φ → Configuration d × Configuration d → ℝ)
      (z : Configuration d × Configuration d) :
      w (ρ z) * g (ρ z) z = ∑ F, V F z * g F z := by
    rw [Finset.sum_eq_single (ρ z)]
    · simp only [V, if_pos rfl, ite_true, one_mul]
    · intro F _ hn
      simp only [V, if_neg (Ne.symm hn), zero_mul]
    · intro hn
      exact (hn (Finset.mem_univ _)).elim
  have hsplit' (z : Configuration d × Configuration d) : w (ρ z) = ∑ F, V F z := by
    simpa only [mul_one] using hsplit (fun _ _ => 1) z
  rw [integral_congr_ae (Filter.Eventually.of_forall (hsplit f)),
    integral_congr_ae (Filter.Eventually.of_forall hsplit'),
    integral_finsetSum _ (fun F _ => ((hV F).mul_union (hf F)).integrable p q),
    integral_finsetSum _ (fun F _ => (hV F).integrable p q), Finset.mul_sum]
  exact Finset.sum_le_sum fun F _ => hterm F

/-- The actual cube weights cost at most `κ²` per common route level
when passing from a frozen marked expectation to the coupled law. -/
theorem NestRule.revealed_marked_pair_le
    {D M d : ℕ} {X Φ : Type} [Fintype X] [Fintype Φ]
    (p q : unitInterval) {ρ κ : ℝ} (R : NestRule D M d p q ρ κ X Φ)
    (hκ : 1 ≤ κ) (γ γ' : SourceRoute D M)
    (T : Φ → Finset (LBond d)) (hd : ∀ F, Disjoint (R.S F) (T F))
    (f : Φ → Configuration d × Configuration d → ℝ)
    (hf : ∀ F, IsLocal (T F) (f F)) {A : ℝ} (hA₀ : 0 ≤ A) :
    let μ := (percolation d p).prod (percolation d q)
    (∀ F, (∃ z, R.ρ z = F) → 0 < R.w γ F → 0 < R.w γ' F → (∫ z, f F z ∂μ) ≤ A) →
    (∫ z, (R.w γ (R.ρ z) * R.w γ' (R.ρ z)) * f (R.ρ z) z ∂μ) ≤
      A * κ ^ (2 * routeCommonLevels D M (γ,γ')) := by
  intro μ hA
  let w (F : Φ) := R.w γ F * R.w γ' F
  have hw (F : Φ) : 0 ≤ w F := mul_nonneg (R.hw0 γ F) (R.hw0 γ' F)
  have hb := revealed_local_marked_mass_le p q R.ρ R.S T R.hρ hd w hw f hf A
    (fun F hF hne =>
      hA F hF (lt_of_le_of_ne (R.hw0 γ F) (left_ne_zero_of_mul hne).symm)
        (lt_of_le_of_ne (R.hw0 γ' F) (right_ne_zero_of_mul hne).symm))
  refine hb.trans (mul_le_mul_of_nonneg_left ?_ hA₀)
  have he (z : Configuration d × Configuration d) :
      w (R.ρ z) = (∏ s ∈ routeSites M γ.position, R.u s z) *
        (∏ s ∈ routeSites M γ'.position, R.u s z) := by
    dsimp only [w]
    rw [R.hwu γ, R.hwu γ']
  rw [integral_congr_ae (Filter.Eventually.of_forall he)]
  let L := routeSites M γ.position
  let L' := routeSites M γ'.position
  let S := @Inter.inter _ (@Finset.instInter (RSite D) (Classical.decEq _)) L L'
  let S' := @Inter.inter _ (@Finset.instInter (RSite D)
    (@instDecidableEqProd ℕ (Fin D → ℤ) instDecidableEqNat (Classical.decEq _))) L L'
  have hS : S = S' := by
    ext x
    simp only [S,S',Finset.mem_inter]
  have hcard : S.card ≤ 2 * routeCommonLevels D M (γ,γ') := by
    rw [hS]
    exact common_route_sites_card_le_two_levels M γ.position γ'.position
  exact (siteWeight_pair_le p q R.Es R.hEs R.u R.hu R.hu0 R.humean hκ R.husq L L').trans
    (pow_le_pow_right₀ hκ hcard)

end NearCritical.Section10
