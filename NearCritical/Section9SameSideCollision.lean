module
public import NearCritical.Section9MarkedPivotSum
public import NearCritical.Section9CollisionConvolution

/-! The same-side product contribution from the pivotal resampling argument. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory
open scoped Classical BigOperators

/-- Summing the product of actual heart-conditioned left-marked pivotal
probabilities gives the eighth-order root-pair kernel. The arm and mass
budgets are the explicit inputs supplied by the middle/end-cube geometry. -/
theorem section9_conditioned_same_side_collision_le {d : ℕ} (hd : 9 ≤ d) {G : ℝ}
    (hG : 0 ≤ G) (green : CriticalSupGreenUpper d G)
    (E : Finset (Vertex d × Vertex d))
    (L R Q₁ H₁ F₁ Q₃ H₃ F₃ A B W : Finset (Vertex d))
    (hH₁ : H₁ ⊆ Q₁) (hH₃ : H₃ ⊆ Q₃)
    (hpos : percolation d (criticalPoint d) (section9RevealEvent Q₁ H₁ Q₃ H₃ F₁ F₃) ≠ 0)
    (hLQ₃ : Disjoint L Q₃) (hRQ₁ : Disjoint R Q₁)
    (H M : ℝ) (hH : 0 ≤ H) (hM : 0 ≤ M)
    (hRight : ∀ e ∈ E, (percolation d (criticalPoint d)).real
      (connectionToSetEvent (R : Set (Vertex d)) e.2 (B : Set (Vertex d))) ≤ H)
    (hMass : ∀ u ∈ L, ∑ e ∈ E, (percolation d (criticalPoint d)).real
      (connectionToSetEvent (L : Set (Vertex d)) e.1 {u}) ≤ M) :
    let ν := section9RevealedLaw (criticalPoint d) Q₁ H₁ Q₃ H₃ F₁ F₃
    let K := G^4 * ((4 : ℝ)^((d : ℝ)-2)*(2+19*(2*(d : ℝ)*3^(d-1))))^2 *
      ((4 : ℝ)^((d : ℝ)-4)*(162+163*(2*(d : ℝ)*3^(d-1))))
    ∑ w ∈ W, (∑ e ∈ E, ν.real {ω |
      sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ A B e ∧
      w ∈ sprinklingUnexploredCluster ω L Q₁ F₁ e.1})^2 ≤
      (H*M)^2 * K * ∑ x ∈ A, ∑ y ∈ A,
        (max 1 (latticeDistance x y))^((8 : ℝ)-(d : ℝ)) := by
  intro ν K
  let T := fun x w => ∑ u ∈ L,
    twoPoint d (criticalPoint d) x u * twoPoint d (criticalPoint d) w u
  have hT (x w : Vertex d) : 0 ≤ T x w :=
    Finset.sum_nonneg fun _ _ => mul_nonneg measureReal_nonneg measureReal_nonneg
  have hpoint (w : Vertex d) :
      (∑ e ∈ E, ν.real {ω | sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ A B e ∧
        w ∈ sprinklingUnexploredCluster ω L Q₁ F₁ e.1})^2 ≤
      (H*M)^2 * (∑ x ∈ A, T x w)^2 := by
    have hb := section9_conditioned_marked_pivot_sum_twoPoint_le E L R Q₁ H₁ F₁ Q₃ H₃ F₃ A B
      hH₁ hH₃ hpos hLQ₃ hRQ₁ H M hH hM hRight hMass w
    calc
      _ ≤ ((H*M) * ∑ x ∈ A, T x w)^2 :=
        pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ => measureReal_nonneg) hb 2
      _ = _ := by ring
  have hsquare (w : Vertex d) : (∑ x ∈ A, T x w)^2 =
      ∑ x ∈ A, ∑ y ∈ A, T x w * T y w := by
    rw [pow_two, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro x _
    rw [Finset.mul_sum]
  have hcontract (x y : Vertex d) : ∑ w ∈ W, T x w * T y w ≤
      K * (max 1 (latticeDistance x y))^((8 : ℝ)-(d : ℝ)) :=
    section9_finite_collision_convolution_le hd hG green L L W x y
  calc
    _ ≤ ∑ w ∈ W, (H*M)^2 * (∑ x ∈ A, T x w)^2 :=
      Finset.sum_le_sum fun w _ => hpoint w
    _ = (H*M)^2 * (∑ w ∈ W, ∑ x ∈ A, ∑ y ∈ A, T x w * T y w) := by
      simp only [hsquare, Finset.mul_sum]
    _ = (H*M)^2 * (∑ x ∈ A, ∑ y ∈ A, ∑ w ∈ W, T x w * T y w) := by
      congr 1
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.sum_comm]
    _ ≤ (H*M)^2 * (∑ x ∈ A, ∑ y ∈ A,
        K * (max 1 (latticeDistance x y))^((8 : ℝ)-(d : ℝ))) := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      exact Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => hcontract x y
    _ = _ := by simp only [← Finset.mul_sum]; ring

end NearCritical
