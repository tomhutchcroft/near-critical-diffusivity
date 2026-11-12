module

public import NearCritical.Section9CoalescenceCross
public import NearCritical.Section9FiniteTripodDecay
public import NearCritical.Section9CoalescenceCaseOneSum

@[expose] public section
namespace NearCritical
open MeasureTheory
open scoped Classical

/-- Case 2 critical pivot sum derived from finite BK and the paper's
two-point asymptotics. -/
theorem section9_case_two_finite_critical_sum_le {d : ℕ} (hd : 5 ≤ d)
    (asymptotics : TwoPointAsymptotics d) :
    ∃ C G : ℝ, 0 < C ∧ 0 < G ∧
      ∀ (i : Fin d) (n : ℕ), 0 < n →
      ∀ (L R Q₁ F₁ Q₃ F₃ B : Finset (Vertex d)) (x y : Vertex d),
      x ∈ section9FiniteEndCube i n 0 → y ∈ section9FiniteEndCube i n 0 →
      B ⊆ section9FiniteEndCube i n (2*(n:ℝ)) →
      let P := orientedLatticePairs (section9FiniteMiddle i n)
      (∑ e ∈ P, (percolation d (criticalPoint d)).real {ω |
        ∃ f : Vertex d × Vertex d,
          sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ {x} B e ∧
          sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ {y} B f ∧
          Disjoint (sprinklingUnexploredCluster ω L Q₁ F₁ e.1)
            (sprinklingUnexploredCluster ω L Q₁ F₁ f.1) ∧
          (sprinklingUnexploredCluster ω R Q₃ F₃ e.2 ∩
            sprinklingUnexploredCluster ω L Q₁ F₁ f.1).Nonempty}) ≤
        ((2 * (d : ℝ)) * (G * (1 + (2 * (d : ℝ) * 3^(d-1)) * ((6*n : ℕ)+1 : ℝ)^2))) *
          ((B.card : ℝ) * (C * ((n:ℝ)/8) ^ (6 - 2 * (d : ℝ)))) := by
  have hd2 : 2 ≤ d := (by decide : 2 ≤ 5).trans hd
  obtain ⟨C, hC, hJoint⟩ := section9_cross_finite_joint_arm_le hd asymptotics
  obtain ⟨G, hG, green⟩ := criticalSupGreenUpper_of_asymptotics hd2 asymptotics
  refine ⟨C, G, hC, hG, ?_⟩
  intro i n hn L R Q₁ F₁ Q₃ F₃ B x y hx hy hB P
  let H := (B.card : ℝ) * (C * ((n:ℝ)/8) ^ (6 - 2 * (d : ℝ)))
  calc
    _ ≤ ∑ e ∈ P, section9RightArm L e.1 x * H := by
      apply Finset.sum_le_sum
      intro e he
      exact (section9_cross_probability_le (criticalPoint d) L R Q₁ F₁ Q₃ F₃ B x y e).trans
        (mul_le_mul_of_nonneg_left
          (by simpa only [Finset.coe_union] using
            hJoint i n hn (R ∪ L) B e.2 y ((mem_orientedLatticePairs _ _ _).mp he).2.1 hy hB)
          measureReal_nonneg)
    _ ≤ _ := by
      rw [← Finset.sum_mul]
      apply mul_le_mul_of_nonneg_right _ (by dsimp [H]; positivity)
      exact section9_middle_tail_mass_le hd2 hG.le green i n L x (Finset.mem_filter.mp hx).1

end NearCritical
