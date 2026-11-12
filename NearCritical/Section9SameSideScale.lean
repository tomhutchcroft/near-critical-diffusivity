module
public import NearCritical.Section9SameSideCollision
public import NearCritical.Section9CoalescenceCaseThree

/-! Source scale normalization for the same-side collision contribution. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory
open scoped Classical BigOperators

/-- Two separated arms and two quadratic pivot masses produce the source
power n^(8-2d); all scale-independent factors are displayed. -/
theorem section9_same_side_scale {d : ℕ} {n b C M M₀ : ℝ}
    (hn : 0 < n) (hb : 0 ≤ b) (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hMass : M ≤ M₀*n^(2 : ℝ)) :
    ((b*(C*(n/8)^((2 : ℝ)-(d : ℝ))))*M)^2 ≤
      ((C/8^((2 : ℝ)-(d : ℝ)))*M₀)^2 * n^((8 : ℝ)-2*(d : ℝ)) * b^2 := by
  let q : ℝ := 2-(d : ℝ)
  have hdiv : C*(n/8)^q = (C/8^q)*n^q := by
    rw [Real.div_rpow hn.le (by norm_num : (0 : ℝ) ≤ 8)]
    ring
  have hpows : (n^q*n^(2 : ℝ))^2 = n^((8 : ℝ)-2*(d : ℝ)) := by
    rw [← Real.rpow_add hn, ← Real.rpow_natCast (n^(q+2)) 2,
      ← Real.rpow_mul hn.le]
    congr 1
    dsimp [q]
    norm_num <;> ring
  calc
    _ ≤ ((b*(C*(n/8)^q))*(M₀*n^(2 : ℝ)))^2 := by
      apply pow_le_pow_left₀ (mul_nonneg (mul_nonneg hb (by positivity)) hM)
      exact mul_le_mul_of_nonneg_left hMass (by positivity)
    _ = ((C/8^q)*M₀)^2 * (n^q*n^(2 : ℝ))^2 * b^2 := by rw [hdiv]; ring
    _ = _ := by rw [hpows]

/-- The source middle/end-cube geometry supplies both budgets, giving the
same-side resampling contribution with its n^(8-2d) scale. -/
theorem section9_conditioned_same_side_source_bound {d : ℕ} (hd : 9 ≤ d)
    (asymptotics : TwoPointAsymptotics d) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (i : Fin d) (n : ℕ), 0 < n →
      ∀ (L R Q₁ H₁ F₁ Q₃ H₃ F₃ A B W : Finset (Vertex d)),
      H₁ ⊆ Q₁ → H₃ ⊆ Q₃ →
      percolation d (criticalPoint d) (section9RevealEvent Q₁ H₁ Q₃ H₃ F₁ F₃) ≠ 0 →
      Disjoint L Q₃ → Disjoint R Q₁ → L ⊆ centeredBox d (3*n) →
      B ⊆ section9FiniteEndCube i n (2*(n:ℝ)) →
      let ν := section9RevealedLaw (criticalPoint d) Q₁ H₁ Q₃ H₃ F₁ F₃
      let E := orientedLatticePairs (section9FiniteMiddle i n)
      ∑ w ∈ W, (∑ e ∈ E, ν.real {ω |
        sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ A B e ∧
        w ∈ sprinklingUnexploredCluster ω L Q₁ F₁ e.1})^2 ≤
        K * (n : ℝ)^((8 : ℝ)-2*(d : ℝ)) * (B.card : ℝ)^2 *
          ∑ x ∈ A, ∑ y ∈ A, (max 1 (latticeDistance x y))^((8 : ℝ)-(d : ℝ)) := by
  have hd2 : 2 ≤ d := by omega
  obtain ⟨C,hC,hArm⟩ := section9_case_one_right_arm_le hd2 asymptotics
  obtain ⟨G,hG,green⟩ := criticalSupGreenUpper_of_asymptotics hd2 asymptotics
  let J : ℝ := 2*(d : ℝ)*3^(d-1)
  let M₀ : ℝ := (2*(d : ℝ))*(G*(1+49*J))
  let D : ℝ := G^4 * ((4 : ℝ)^((d : ℝ)-2)*(2+19*J))^2 *
    ((4 : ℝ)^((d : ℝ)-4)*(162+163*J))
  let Z : ℝ := ((C/8^((2 : ℝ)-(d : ℝ)))*M₀)^2
  have hD : 0 ≤ D := by dsimp [D,J]; positivity
  refine ⟨Z*D,mul_nonneg (sq_nonneg _) hD,?_⟩
  intro i n hn L R Q₁ H₁ F₁ Q₃ H₃ F₃ A B W hH₁ hH₃ hpos hLQ₃ hRQ₁ hL hB ν E
  let H : ℝ := (B.card : ℝ)*(C*((n : ℝ)/8)^((2 : ℝ)-(d : ℝ)))
  let M : ℝ := (2*(d : ℝ))*(G*(1+J*((6*n : ℕ)+1 : ℝ)^2))
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hM : 0 ≤ M := by dsimp [M,J]; positivity
  have hMass : M ≤ M₀*(n : ℝ)^(2 : ℝ) := by
    rw [Real.rpow_two]
    have hm := mul_le_mul_of_nonneg_left
      (section9_case_three_mass_normalization (K := J) hG.le (by dsimp [J]; positivity) hn)
      (by positivity : 0 ≤ 2*(d : ℝ))
    simpa only [M,M₀,mul_assoc] using hm
  have hs := section9_same_side_scale (d := d) (by exact_mod_cast hn)
    (Nat.cast_nonneg B.card) hC.le hM hMass
  have hc := section9_conditioned_same_side_collision_le hd hG.le green E
    L R Q₁ H₁ F₁ Q₃ H₃ F₃ A B W hH₁ hH₃ hpos hLQ₃ hRQ₁ H M hH hM
    (fun e he => hArm i n hn R B e.2 ((mem_orientedLatticePairs _ _ _).mp he).2.1 hB)
    (fun u hu => section9_middle_tail_mass_le hd2 hG.le green i n L u (hL hu))
  have hroots : 0 ≤ ∑ x ∈ A, ∑ y ∈ A,
      (max 1 (latticeDistance x y))^((8 : ℝ)-(d : ℝ)) := by positivity
  calc
    _ ≤ (H*M)^2 * D * ∑ x ∈ A, ∑ y ∈ A,
        (max 1 (latticeDistance x y))^((8 : ℝ)-(d : ℝ)) := hc
    _ ≤ (Z*(n : ℝ)^((8 : ℝ)-2*(d : ℝ))*(B.card : ℝ)^2) * D *
        ∑ x ∈ A, ∑ y ∈ A, (max 1 (latticeDistance x y))^((8 : ℝ)-(d : ℝ)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hs hD) hroots
    _ = _ := by ring

end NearCritical
