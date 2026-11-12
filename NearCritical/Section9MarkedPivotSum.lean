module
public import NearCritical.Section9ConditionedMarkedTree
public import NearCritical.Section9CoalescenceCaseOneSum

/-! Summation of the actual marked pivotal probability over middle candidates. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory
open scoped Classical BigOperators

/-- The conditional marked pivot sum factors into the right-arm bound,
the pivot-tail mass, and the remaining two-arm diagram. -/
theorem section9_conditioned_marked_pivot_sum_le {d : ℕ} (p : unitInterval)
    (E : Finset (Vertex d × Vertex d))
    (L R Q₁ H₁ F₁ Q₃ H₃ F₃ A B : Finset (Vertex d))
    (hH₁ : H₁ ⊆ Q₁) (hH₃ : H₃ ⊆ Q₃)
    (hpos : percolation d p (section9RevealEvent Q₁ H₁ Q₃ H₃ F₁ F₃) ≠ 0)
    (hLQ₃ : Disjoint L Q₃) (hRQ₁ : Disjoint R Q₁)
    (H M : ℝ) (hH : 0 ≤ H)
    (hRight : ∀ e ∈ E, (percolation d p).real
      (connectionToSetEvent (R : Set (Vertex d)) e.2 (B : Set (Vertex d))) ≤ H)
    (hMass : ∀ u ∈ L, ∑ e ∈ E, (percolation d p).real
      (connectionToSetEvent (L : Set (Vertex d)) e.1 {u}) ≤ M)
    (w : Vertex d) :
    let ν := section9RevealedLaw p Q₁ H₁ Q₃ H₃ F₁ F₃
    let P := fun a b => (percolation d p).real
      (connectionToSetEvent (L : Set (Vertex d)) a {b})
    (∑ e ∈ E, ν.real {ω | sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ A B e ∧
      w ∈ sprinklingUnexploredCluster ω L Q₁ F₁ e.1}) ≤
      H * (M * ∑ x ∈ A, ∑ u ∈ L, P u w * P x u) := by
  intro ν P
  have hP (a b : Vertex d) : 0 ≤ P a b := measureReal_nonneg
  calc
    _ ≤ ∑ e ∈ E, (∑ x ∈ A, ∑ u ∈ L, P e.1 u * (P u w * P x u)) * H := by
      apply Finset.sum_le_sum
      intro e he
      exact (section9_conditioned_marked_pivotal_tree_bound p L R Q₁ H₁ F₁ Q₃ H₃ F₃ A B
        hH₁ hH₃ hpos hLQ₃ hRQ₁ e w).trans
        (mul_le_mul_of_nonneg_left (hRight e he) (Finset.sum_nonneg fun x _ =>
          Finset.sum_nonneg fun u _ => mul_nonneg (hP _ _) (mul_nonneg (hP _ _) (hP _ _))))
    _ = (∑ x ∈ A, ∑ u ∈ L, (∑ e ∈ E, P e.1 u) * (P u w * P x u)) * H := by
      rw [← Finset.sum_mul, Finset.sum_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.sum_comm]
      simp only [Finset.sum_mul]
    _ ≤ (∑ x ∈ A, ∑ u ∈ L, M * (P u w * P x u)) * H := by
      apply mul_le_mul_of_nonneg_right _ hH
      exact Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun u hu =>
        mul_le_mul_of_nonneg_right (hMass u hu) (mul_nonneg (hP _ _) (hP _ _))
    _ = _ := by simp only [← Finset.mul_sum]; ring

/-- The remaining restricted diagram is bounded by the actual full-space
critical bubble, without a tree-diagram premise. -/
theorem section9_conditioned_marked_pivot_sum_twoPoint_le {d : ℕ}
    (E : Finset (Vertex d × Vertex d))
    (L R Q₁ H₁ F₁ Q₃ H₃ F₃ A B : Finset (Vertex d))
    (hH₁ : H₁ ⊆ Q₁) (hH₃ : H₃ ⊆ Q₃)
    (hpos : percolation d (criticalPoint d) (section9RevealEvent Q₁ H₁ Q₃ H₃ F₁ F₃) ≠ 0)
    (hLQ₃ : Disjoint L Q₃) (hRQ₁ : Disjoint R Q₁)
    (H M : ℝ) (hH : 0 ≤ H) (hM : 0 ≤ M)
    (hRight : ∀ e ∈ E, (percolation d (criticalPoint d)).real
      (connectionToSetEvent (R : Set (Vertex d)) e.2 (B : Set (Vertex d))) ≤ H)
    (hMass : ∀ u ∈ L, ∑ e ∈ E, (percolation d (criticalPoint d)).real
      (connectionToSetEvent (L : Set (Vertex d)) e.1 {u}) ≤ M)
    (w : Vertex d) :
    let ν := section9RevealedLaw (criticalPoint d) Q₁ H₁ Q₃ H₃ F₁ F₃
    (∑ e ∈ E, ν.real {ω | sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ A B e ∧
      w ∈ sprinklingUnexploredCluster ω L Q₁ F₁ e.1}) ≤
      (H*M) * ∑ x ∈ A, ∑ u ∈ L,
        twoPoint d (criticalPoint d) x u * twoPoint d (criticalPoint d) w u := by
  intro ν
  have hP (a b : Vertex d) :
      (percolation d (criticalPoint d)).real
        (connectionToSetEvent (L : Set (Vertex d)) a {b}) ≤ twoPoint d (criticalPoint d) a b := by
    simpa only [Finset.coe_singleton, Finset.sum_singleton] using
      connectionToSet_probability_le_twoPoint_sum (criticalPoint d) (L : Set (Vertex d)) a {b}
  have hrev (u w : Vertex d) :
      (percolation d (criticalPoint d)).real
        (connectionToSetEvent (L : Set (Vertex d)) u {w}) ≤ twoPoint d (criticalPoint d) w u := by
    change section9RightArm L u w ≤ _
    rw [section9RightArm_symm]
    exact hP w u
  refine (section9_conditioned_marked_pivot_sum_le (criticalPoint d) E L R Q₁ H₁ F₁ Q₃ H₃ F₃ A B
    hH₁ hH₃ hpos hLQ₃ hRQ₁ H M hH hRight hMass w).trans ?_
  rw [← mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg hH hM)
  apply Finset.sum_le_sum
  intro x _
  apply Finset.sum_le_sum
  intro u _
  calc
    _ ≤ twoPoint d (criticalPoint d) w u * twoPoint d (criticalPoint d) x u :=
      mul_le_mul (hrev u w) (hP x u) measureReal_nonneg measureReal_nonneg
    _ = _ := mul_comm _ _

end NearCritical
