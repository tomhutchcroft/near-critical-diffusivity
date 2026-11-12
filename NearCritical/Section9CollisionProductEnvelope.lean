module
public import NearCritical.Section9CollisionProducts
public import NearCritical.Section9RightMarkedBounds

/-! Uniform contraction of all four original/replacement collision products. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory
open scoped Classical BigOperators

private theorem collision_aggregate_contraction {d : ℕ} (hd : 9 ≤ d) {G : ℝ}
    (hG : 0 ≤ G) (green : CriticalSupGreenUpper d G)
    (D D' A B W : Finset (Vertex d)) (c c' : ℝ) (hc : 0 ≤ c) (hc' : 0 ≤ c')
    (f g : Vertex d → ℝ) (hg : ∀ w, 0 ≤ g w)
    (hf : ∀ w, f w ≤ c * ∑ x ∈ A, ∑ u ∈ D,
      twoPoint d (criticalPoint d) x u * twoPoint d (criticalPoint d) w u)
    (hg' : ∀ w, g w ≤ c' * ∑ y ∈ B, ∑ v ∈ D',
      twoPoint d (criticalPoint d) y v * twoPoint d (criticalPoint d) w v) :
    ∑ w ∈ W, f w * g w ≤
      (c*c') * (G^4 * ((4 : ℝ)^((d : ℝ)-2)*(2+19*(2*(d : ℝ)*3^(d-1))))^2 *
        ((4 : ℝ)^((d : ℝ)-4)*(162+163*(2*(d : ℝ)*3^(d-1))))) *
      ∑ x ∈ A, ∑ y ∈ B, (max 1 (latticeDistance x y))^((8 : ℝ)-(d : ℝ)) := by
  let T := fun (S : Finset (Vertex d)) x w => ∑ u ∈ S,
    twoPoint d (criticalPoint d) x u * twoPoint d (criticalPoint d) w u
  let K := G^4 * ((4 : ℝ)^((d : ℝ)-2)*(2+19*(2*(d : ℝ)*3^(d-1))))^2 *
    ((4 : ℝ)^((d : ℝ)-4)*(162+163*(2*(d : ℝ)*3^(d-1))))
  have hT (S : Finset (Vertex d)) (x w : Vertex d) : 0 ≤ T S x w :=
    Finset.sum_nonneg fun _ _ => mul_nonneg measureReal_nonneg measureReal_nonneg
  have hproduct (w : Vertex d) : f w * g w ≤
      (c*c') * (∑ x ∈ A, ∑ y ∈ B, T D x w * T D' y w) := by
    calc
      _ ≤ (c * ∑ x ∈ A, T D x w) * (c' * ∑ y ∈ B, T D' y w) :=
        mul_le_mul (hf w) (hg' w) (hg w)
          (mul_nonneg hc (Finset.sum_nonneg fun x _ => hT D x w))
      _ = (c*c') * ((∑ x ∈ A, T D x w) * (∑ y ∈ B, T D' y w)) := by ring
      _ = _ := by
        congr 1
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro x _
        rw [Finset.mul_sum]
  calc
    _ ≤ ∑ w ∈ W, (c*c') * (∑ x ∈ A, ∑ y ∈ B, T D x w * T D' y w) :=
      Finset.sum_le_sum fun w _ => hproduct w
    _ = (c*c') * (∑ w ∈ W, ∑ x ∈ A, ∑ y ∈ B, T D x w * T D' y w) :=
      (Finset.mul_sum _ _ _).symm
    _ = (c*c') * (∑ x ∈ A, ∑ y ∈ B, ∑ w ∈ W, T D x w * T D' y w) := by
      congr 1
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.sum_comm]
    _ ≤ (c*c') * (∑ x ∈ A, ∑ y ∈ B,
        K * (max 1 (latticeDistance x y))^((8 : ℝ)-(d : ℝ))) := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hc hc')
      exact Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ =>
        section9_finite_collision_convolution_le hd hG green D D' W x y
    _ = _ := by simp only [← Finset.mul_sum]; dsimp [K]; ring

/-- Every side choice has the same explicit eighth-order convolution constant.
The budgets are actual opposite-side arm bounds and actual tail/head masses;
no collision estimate or replacement pivotality is assumed. -/
theorem section9_collision_product_envelope {d : ℕ} (hd : 9 ≤ d) {G : ℝ}
    (hG : 0 ≤ G) (green : CriticalSupGreenUpper d G)
    (E : Finset (Vertex d × Vertex d)) (hswap : ∀ e ∈ E, e.swap ∈ E)
    (L R Q₁ H₁ F₁ Q₃ H₃ F₃ A B W : Finset (Vertex d))
    (hH₁ : H₁ ⊆ Q₁) (hH₃ : H₃ ⊆ Q₃)
    (hpos : percolation d (criticalPoint d) (section9RevealEvent Q₁ H₁ Q₃ H₃ F₁ F₃) ≠ 0)
    (hLQ₃ : Disjoint L Q₃) (hRQ₁ : Disjoint R Q₁)
    (Hleft Hright Mleft Mright : ℝ)
    (hHl : 0 ≤ Hleft) (hHr : 0 ≤ Hright) (hMl : 0 ≤ Mleft) (hMr : 0 ≤ Mright)
    (hOppRight : ∀ e ∈ E, (percolation d (criticalPoint d)).real
      (connectionToSetEvent (R : Set (Vertex d)) e.2 (B : Set (Vertex d))) ≤ Hleft)
    (hOppLeft : ∀ e ∈ E, (percolation d (criticalPoint d)).real
      (connectionToSetEvent (L : Set (Vertex d)) e.1 (A : Set (Vertex d))) ≤ Hright)
    (hTail : ∀ u ∈ L, ∑ e ∈ E, (percolation d (criticalPoint d)).real
      (connectionToSetEvent (L : Set (Vertex d)) e.1 {u}) ≤ Mleft)
    (hHead : ∀ v ∈ R, ∑ e ∈ E, (percolation d (criticalPoint d)).real
      (connectionToSetEvent (R : Set (Vertex d)) e.2 {v}) ≤ Mright)
    (s t : Bool) :
    let ν := section9RevealedLaw (criticalPoint d) Q₁ H₁ Q₃ H₃ F₁ F₃
    let K := G^4 * ((4 : ℝ)^((d : ℝ)-2)*(2+19*(2*(d : ℝ)*3^(d-1))))^2 *
      ((4 : ℝ)^((d : ℝ)-4)*(162+163*(2*(d : ℝ)*3^(d-1))))
    section9CollisionProduct ν E L R Q₁ F₁ Q₃ F₃ A B W s t ≤
      ((if s then Hright*Mright else Hleft*Mleft) *
       (if t then Hright*Mright else Hleft*Mleft)) * K *
      ∑ x ∈ (if s then B else A), ∑ y ∈ (if t then B else A),
        (max 1 (latticeDistance x y))^((8 : ℝ)-(d : ℝ)) := by
  intro ν K
  let budget := fun b : Bool => if b then Hright*Mright else Hleft*Mleft
  let target := fun b : Bool => if b then B else A
  let domain := fun b : Bool => if b then R else L
  have hbudget (b : Bool) : 0 ≤ budget b := by cases b <;> dsimp [budget] <;> positivity
  have hpivot (b : Bool) (w : Vertex d) :
      (∑ e ∈ E, ν.real (section9PivotalMarkEvent b L R Q₁ F₁ Q₃ F₃ A B e w)) ≤
        budget b * ∑ x ∈ target b, ∑ u ∈ domain b,
          twoPoint d (criticalPoint d) x u * twoPoint d (criticalPoint d) w u := by
    cases b
    · simpa [section9PivotalMarkEvent,budget,target,domain] using
        section9_conditioned_marked_pivot_sum_twoPoint_le E L R Q₁ H₁ F₁ Q₃ H₃ F₃ A B
          hH₁ hH₃ hpos hLQ₃ hRQ₁ Hleft Mleft hHl hMl hOppRight hTail w
    · simpa [section9PivotalMarkEvent,budget,target,domain] using
        section9_conditioned_right_marked_pivot_sum_twoPoint_le E hswap L R Q₁ H₁ F₁ Q₃ H₃ F₃ A B
          hH₁ hH₃ hpos hLQ₃ hRQ₁ Hright Mright hHr hMr hOppLeft hHead w
  have harm (b : Bool) (w : Vertex d) :
      (∑ e ∈ E, ν.real (section9ArmMarkEvent b L R Q₁ F₁ Q₃ F₃ A B e w)) ≤
        budget b * ∑ x ∈ target b, ∑ u ∈ domain b,
          twoPoint d (criticalPoint d) x u * twoPoint d (criticalPoint d) w u := by
    cases b
    · simpa [section9ArmMarkEvent,budget,target,domain] using
        section9_conditioned_marked_arm_sum_twoPoint_le E L R Q₁ H₁ F₁ Q₃ H₃ F₃ A B
          hH₁ hH₃ hpos hLQ₃ hRQ₁ Hleft Mleft hHl hMl hOppRight hTail w
    · simpa [section9ArmMarkEvent,budget,target,domain] using
        section9_conditioned_right_marked_arm_sum_twoPoint_le E hswap L R Q₁ H₁ F₁ Q₃ H₃ F₃ A B
          hH₁ hH₃ hpos hLQ₃ hRQ₁ Hright Mright hHr hMr hOppLeft hHead w
  simpa only [section9CollisionProduct,budget,target,domain,K] using
    collision_aggregate_contraction hd hG green (domain s) (domain t) (target s) (target t) W
    (budget s) (budget t) (hbudget s) (hbudget t)
    (fun w => ∑ e ∈ E, ν.real (section9PivotalMarkEvent s L R Q₁ F₁ Q₃ F₃ A B e w))
    (fun w => ∑ e ∈ E, ν.real (section9ArmMarkEvent t L R Q₁ F₁ Q₃ F₃ A B e w))
    (fun _ => Finset.sum_nonneg fun _ _ => measureReal_nonneg) (hpivot s) (harm t)

end NearCritical
