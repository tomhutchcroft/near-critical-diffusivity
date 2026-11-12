module

public import NearCritical.Section9CoalescenceSharedLeft
public import NearCritical.Section9CoalescenceBubble
public import NearCritical.Section9CoalescenceGeometry
public import NearCritical.Section9SeparatedTwoPoint
public import NearCritical.Section9PivotalMeanUpper

@[expose] public section
namespace NearCritical
open MeasureTheory
open scoped Classical

/-- Sum the fixed-pivot Case 1 diagram, factoring off the uniform
right-arm estimate and the uniform pivot-tail mass. -/
theorem section9_case_one_pivot_sum_le {d : ℕ}
    (p : unitInterval) (P : Finset (Vertex d × Vertex d))
    (L R Q₁ F₁ Q₃ F₃ B : Finset (Vertex d)) (x y : Vertex d)
    (H M : ℝ) (hH : 0 ≤ H)
    (hRight : ∀ e ∈ P, (percolation d p).real
      (connectionToSetEvent (R : Set (Vertex d)) e.2 (B : Set (Vertex d))) ≤ H)
    (hMass : ∀ u ∈ L, ∑ e ∈ P, (percolation d p).real
      (connectionToSetEvent (L : Set (Vertex d)) e.1 {u}) ≤ M) :
    let A := fun a b => (percolation d p).real (connectionToSetEvent (L : Set (Vertex d)) a {b})
    (∑ e ∈ P, (percolation d p).real {ω |
      sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ {x} B e ∧
      (sprinklingUnexploredCluster ω L Q₁ F₁ x ∩
        sprinklingUnexploredCluster ω L Q₁ F₁ y).Nonempty}) ≤
      H * (M * ∑ u ∈ L, A u x * A y u) := by
  intro A
  have hA (a b : Vertex d) : 0 ≤ A a b := measureReal_nonneg
  calc
    _ ≤ ∑ e ∈ P, (∑ u ∈ L, A e.1 u * (A u x * A y u)) * H := by
      apply Finset.sum_le_sum
      intro e he
      exact (section9_shared_left_probability_le p L R Q₁ F₁ Q₃ F₃ B x y e).trans
        (mul_le_mul_of_nonneg_left (hRight e he) (Finset.sum_nonneg fun u _ =>
          mul_nonneg (hA _ _) (mul_nonneg (hA _ _) (hA _ _))))
    _ = (∑ u ∈ L, (∑ e ∈ P, A e.1 u) * (A u x * A y u)) * H := by
      rw [← Finset.sum_mul, Finset.sum_comm]
      simp only [Finset.sum_mul]
    _ ≤ (∑ u ∈ L, M * (A u x * A y u)) * H := by
      apply mul_le_mul_of_nonneg_right _ hH
      exact Finset.sum_le_sum fun u hu =>
        mul_le_mul_of_nonneg_right (hMass u hu) (mul_nonneg (hA _ _) (hA _ _))
    _ = _ := by rw [← Finset.mul_sum, mul_comm _ H]

/-- Reversing an oriented candidate preserves the enumeration and
transports the quadratic head mass to the Case 1 tail mass. -/
theorem section9_middle_tail_mass_le {d : ℕ} (hd : 2 ≤ d) {G : ℝ}
    (hG : 0 ≤ G) (green : CriticalSupGreenUpper d G)
    (i : Fin d) (n : ℕ) (L : Finset (Vertex d)) (u : Vertex d)
    (hu : u ∈ centeredBox d (3*n)) :
    ∑ e ∈ orientedLatticePairs (section9FiniteMiddle i n), section9RightArm L e.1 u ≤
      (2 * (d : ℝ)) * (G * (1 + (2 * (d : ℝ) * 3^(d-1)) * ((6*n : ℕ)+1 : ℝ)^2)) := by
  let P := orientedLatticePairs (section9FiniteMiddle i n)
  have hswap (e : Vertex d × Vertex d) (he : e ∈ P) : e.swap ∈ P := by
    obtain ⟨h₁, h₂, hadj⟩ := (mem_orientedLatticePairs _ _ _).mp he
    exact (mem_orientedLatticePairs _ _ _).mpr ⟨h₂, h₁, hadj.symm⟩
  calc
    _ = ∑ e ∈ P, section9RightArm L u e.2 := by
      apply Finset.sum_bij (fun e _ => e.swap)
      · exact hswap
      · intro a ha b hb hab
        exact congrArg Prod.swap hab
      · intro e he
        exact ⟨e.swap, hswap e he, rfl⟩
      · intro e _
        exact section9RightArm_symm L e.1 u
    _ ≤ _ := section9_middle_head_mass_le hd hG green i n L u hu

/-- A middle pivot's right arm to the entire third-cube target family
costs one separated two-point bound per target. -/
theorem section9_case_one_right_arm_le {d : ℕ} (hd : 2 ≤ d)
    (asymptotics : TwoPointAsymptotics d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (i : Fin d) (n : ℕ), 0 < n →
      ∀ (R B : Finset (Vertex d)) (v : Vertex d),
      v ∈ section9FiniteMiddle i n →
      B ⊆ section9FiniteEndCube i n (2*(n:ℝ)) →
      (percolation d (criticalPoint d)).real
        (connectionToSetEvent (R : Set (Vertex d)) v (B : Set (Vertex d))) ≤
        (B.card : ℝ) * (C * ((n:ℝ)/8) ^ ((2:ℝ)-(d:ℝ))) := by
  obtain ⟨C, hC, hdecay⟩ := section9TwoPoint_middle_end_bounds hd asymptotics
  refine ⟨C, hC, ?_⟩
  intro i n hn R B v hv hB
  refine (connectionToSet_probability_le_twoPoint_sum (criticalPoint d) _ v B).trans ?_
  calc
    _ ≤ ∑ _z ∈ B, C * ((n:ℝ)/8) ^ ((2:ℝ)-(d:ℝ)) :=
      Finset.sum_le_sum fun z hz => hdecay i n hn v hv z (Or.inr (hB hz))
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]

/-- Case 1 critical pivot sum under the source geometry, with the
remaining root-pair kernel displayed explicitly. -/
theorem section9_case_one_critical_sum_le {d : ℕ} (hd : 5 ≤ d)
    (asymptotics : TwoPointAsymptotics d) :
    ∃ C G : ℝ, 0 < C ∧ 0 < G ∧
    ∀ (i : Fin d) (n : ℕ), 0 < n →
    ∀ (L R Q₁ F₁ Q₃ F₃ B : Finset (Vertex d)) (x y : Vertex d),
    L ⊆ centeredBox d (3*n) → B ⊆ section9FiniteEndCube i n (2*(n:ℝ)) →
    let P := orientedLatticePairs (section9FiniteMiddle i n)
    let H := (B.card : ℝ) * (C * ((n:ℝ)/8) ^ ((2:ℝ)-(d:ℝ)))
    let M := (2 * (d : ℝ)) * (G * (1 + (2 * (d : ℝ) * 3^(d-1)) * ((6*n : ℕ)+1 : ℝ)^2))
    let K := G^2 * (((4 : ℝ)^((d : ℝ)-2)*(2+19*(2*(d : ℝ)*3^(d-1)))) *
      (max 1 (latticeDistance x y))^((4 : ℝ)-(d : ℝ)))
    (∑ e ∈ P, (percolation d (criticalPoint d)).real {ω |
      sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ {x} B e ∧
      (sprinklingUnexploredCluster ω L Q₁ F₁ x ∩
        sprinklingUnexploredCluster ω L Q₁ F₁ y).Nonempty}) ≤ H * (M * K) := by
  have hd2 : 2 ≤ d := (by decide : 2 ≤ 5).trans hd
  obtain ⟨C, hC, hArm⟩ := section9_case_one_right_arm_le hd2 asymptotics
  obtain ⟨G, hG, green⟩ := criticalSupGreenUpper_of_asymptotics hd2 asymptotics
  refine ⟨C, G, hC, hG, ?_⟩
  intro i n hn L R Q₁ F₁ Q₃ F₃ B x y hL hB P H M K
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hM : 0 ≤ M := by dsimp [M]; positivity
  refine (section9_case_one_pivot_sum_le (criticalPoint d) P L R Q₁ F₁ Q₃ F₃ B x y
    H M hH (fun e he => hArm i n hn R B e.2 ((mem_orientedLatticePairs _ _ _).mp he).2.1 hB)
    (fun u hu => section9_middle_tail_mass_le hd2 hG.le green i n L u (hL hu))).trans ?_
  apply mul_le_mul_of_nonneg_left _ hH
  apply mul_le_mul_of_nonneg_left _ hM
  calc
    _ = ∑ u ∈ L, section9RightArm L x u * section9RightArm L y u := by
      exact Finset.sum_congr rfl (fun u _ =>
        congrArg (fun a => a * section9RightArm L y u) (section9RightArm_symm L u x))
    _ ≤ _ := section9_restricted_bubble_le hd hG.le green L x y

/-- A single fresh bond opening multiplies the critical event
probability by the sprinkle rate. -/
theorem section9_case_one_opened_probability {d : ℕ} (q : unitInterval)
    (A : Set (Configuration d)) (b : Bond d) :
    ((percolation d (criticalPoint d)).prod (percolation d q)).real
      (A ×ˢ {η | η b = true}) =
        (percolation d (criticalPoint d)).real A * (q : ℝ) := by
  simp only [Measure.real, Measure.prod_prod, ENNReal.toReal_mul,
    percolation_open_bond, ENNReal.toReal_ofReal q.property.1]

end NearCritical
