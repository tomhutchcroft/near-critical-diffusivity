module
public import NearCritical.Section9MarkedArmResampling
public import NearCritical.Section9MarkedPivotSum
public import NearCritical.Section9CollisionConvolution
public import NearCritical.Section9SameSideScale

/-! The corrected same-side product bound and its adaptive resampling
integrals. Replacement pivotality is never assumed. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory
open scoped Classical BigOperators

/-- The conditional marked-arm sum factors into the right-arm bound,
the pivot-tail mass, and the remaining two-arm diagram. -/
theorem section9_conditioned_marked_arm_sum_le {d : ℕ} (p : unitInterval)
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
    (∑ e ∈ E, ν.real (section9LeftMarkedArmOccurrence L R Q₁ F₁ Q₃ F₃ A B e w)) ≤
      H * (M * ∑ x ∈ A, ∑ u ∈ L, P u w * P x u) := by
  intro ν P
  have hP (a b : Vertex d) : 0 ≤ P a b := measureReal_nonneg
  calc
    _ ≤ ∑ e ∈ E, (∑ x ∈ A, ∑ u ∈ L, P e.1 u * (P u w * P x u)) * H := by
      apply Finset.sum_le_sum
      intro e he
      exact (section9_conditioned_left_marked_arm_tree_bound p L R Q₁ H₁ F₁ Q₃ H₃ F₃ A B
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
theorem section9_conditioned_marked_arm_sum_twoPoint_le {d : ℕ}
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
    (∑ e ∈ E, ν.real (section9LeftMarkedArmOccurrence L R Q₁ F₁ Q₃ F₃ A B e w)) ≤
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
  refine (section9_conditioned_marked_arm_sum_le (criticalPoint d) E L R Q₁ H₁ F₁ Q₃ H₃ F₃ A B
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

/-- Summing the product of actual heart-conditioned left-marked original pivotal and replacement arm
probabilities gives the eighth-order root-pair kernel. The arm and mass
budgets are the explicit inputs supplied by the middle/end-cube geometry. -/
theorem section9_conditioned_replacement_collision_le {d : ℕ} (hd : 9 ≤ d) {G : ℝ}
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
      w ∈ sprinklingUnexploredCluster ω L Q₁ F₁ e.1}) *
      (∑ f ∈ E, ν.real (section9LeftMarkedArmOccurrence L R Q₁ F₁ Q₃ F₃ A B f w)) ≤
      (H*M)^2 * K * ∑ x ∈ A, ∑ y ∈ A,
        (max 1 (latticeDistance x y))^((8 : ℝ)-(d : ℝ)) := by
  intro ν K
  let T := fun x w => ∑ u ∈ L,
    twoPoint d (criticalPoint d) x u * twoPoint d (criticalPoint d) w u
  have hT (x w : Vertex d) : 0 ≤ T x w :=
    Finset.sum_nonneg fun _ _ => mul_nonneg measureReal_nonneg measureReal_nonneg
  have hpoint (w : Vertex d) :
      (∑ e ∈ E, ν.real {ω | sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ A B e ∧
        w ∈ sprinklingUnexploredCluster ω L Q₁ F₁ e.1}) *
      (∑ f ∈ E, ν.real (section9LeftMarkedArmOccurrence L R Q₁ F₁ Q₃ F₃ A B f w)) ≤
      (H*M)^2 * (∑ x ∈ A, T x w)^2 := by
    have hb := section9_conditioned_marked_pivot_sum_twoPoint_le E L R Q₁ H₁ F₁ Q₃ H₃ F₃ A B
      hH₁ hH₃ hpos hLQ₃ hRQ₁ H M hH hM hRight hMass w
    have hc := section9_conditioned_marked_arm_sum_twoPoint_le E L R Q₁ H₁ F₁ Q₃ H₃ F₃ A B
      hH₁ hH₃ hpos hLQ₃ hRQ₁ H M hH hM hRight hMass w
    calc
      _ ≤ ((H*M) * ∑ x ∈ A, T x w) * ((H*M) * ∑ x ∈ A, T x w) :=
        mul_le_mul hb hc (Finset.sum_nonneg fun _ _ => measureReal_nonneg)
          (mul_nonneg (mul_nonneg hH hM) (Finset.sum_nonneg fun x _ => hT x w))
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

/-- The source middle/end-cube geometry supplies both budgets, giving the
same-side resampling contribution with its n^(8-2d) scale. -/
theorem section9_conditioned_replacement_source_bound {d : ℕ} (hd : 9 ≤ d)
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
        w ∈ sprinklingUnexploredCluster ω L Q₁ F₁ e.1}) *
        (∑ f ∈ E, ν.real (section9LeftMarkedArmOccurrence L R Q₁ F₁ Q₃ F₃ A B f w)) ≤
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
  have hc := section9_conditioned_replacement_collision_le hd hG.le green E
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

/-- The original pivotal event is left-marked; its replacement partner is
only required to have the retained disjoint marked-arm witnesses. -/
def section9LeftReplacementMoment {d : ℕ} (p : unitInterval)
    (E : Finset (Vertex d × Vertex d))
    (L R Q₁ H₁ F₁ Q₃ H₃ F₃ A B W : Finset (Vertex d)) : ℝ :=
  let ν := section9RevealedLaw p Q₁ H₁ Q₃ H₃ F₁ F₃
  ∑ w ∈ W, ∑ e ∈ E, ∑ f ∈ E,
    ∫ ω, (if sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ A B e ∧
      w ∈ sprinklingUnexploredCluster ω L Q₁ F₁ e.1 then (1 : ℝ) else 0) *
      (∫ ζ, (if resampleBonds (section9TwoClusterRevealBonds ω L R Q₁ F₁ Q₃ F₃ e) ω ζ ∈
        section9LeftMarkedArmOccurrence L R Q₁ F₁ Q₃ F₃ A B f w
        then (1 : ℝ) else 0) ∂percolation d p) ∂ν

/-- Finite summation of the actual factorization produces two different
probability sums, with no replacement pivotality restriction. -/
theorem section9_left_replacement_moment_eq {d : ℕ} (p : unitInterval)
    (E : Finset (Vertex d × Vertex d))
    (L R Q₁ H₁ F₁ Q₃ H₃ F₃ A B W : Finset (Vertex d))
    (hH₁ : H₁ ⊆ Q₁) (hH₃ : H₃ ⊆ Q₃)
    (hpos : percolation d p (section9RevealEvent Q₁ H₁ Q₃ H₃ F₁ F₃) ≠ 0)
    (hLQ₃ : Disjoint L Q₃) (hRQ₁ : Disjoint R Q₁) :
    let ν := section9RevealedLaw p Q₁ H₁ Q₃ H₃ F₁ F₃
    section9LeftReplacementMoment p E L R Q₁ H₁ F₁ Q₃ H₃ F₃ A B W =
      ∑ w ∈ W, (∑ e ∈ E, ν.real {ω |
        sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ A B e ∧
        w ∈ sprinklingUnexploredCluster ω L Q₁ F₁ e.1}) *
        (∑ f ∈ E, ν.real (section9LeftMarkedArmOccurrence L R Q₁ F₁ Q₃ F₃ A B f w)) := by
  intro ν
  unfold section9LeftReplacementMoment
  apply Finset.sum_congr rfl
  intro w _
  calc
    _ = ∑ e ∈ E, ∑ f ∈ E,
        ν.real {ω | sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ A B e ∧
          w ∈ sprinklingUnexploredCluster ω L Q₁ F₁ e.1} *
        ν.real (section9LeftMarkedArmOccurrence L R Q₁ F₁ Q₃ F₃ A B f w) := by
      apply Finset.sum_congr rfl
      intro e _
      apply Finset.sum_congr rfl
      intro f _
      exact section9_conditioned_marked_arm_resampling_product p L R Q₁ H₁ F₁ Q₃ H₃ F₃ A B
        hH₁ hH₃ hpos hLQ₃ hRQ₁ e f w
    _ = _ := by rw [Finset.sum_mul]; simp only [Finset.mul_sum]

/-- Source-scale bound for the actual same-side original/replacement
collision integrals, allowing the replacement pivotal event to fail. -/
theorem section9_left_replacement_moment_source_bound {d : ℕ} (hd : 9 ≤ d)
    (asymptotics : TwoPointAsymptotics d) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (i : Fin d) (n : ℕ), 0 < n →
      ∀ (L R Q₁ H₁ F₁ Q₃ H₃ F₃ A B W : Finset (Vertex d)),
      H₁ ⊆ Q₁ → H₃ ⊆ Q₃ →
      percolation d (criticalPoint d) (section9RevealEvent Q₁ H₁ Q₃ H₃ F₁ F₃) ≠ 0 →
      Disjoint L Q₃ → Disjoint R Q₁ → L ⊆ centeredBox d (3*n) →
      B ⊆ section9FiniteEndCube i n (2*(n:ℝ)) →
      section9LeftReplacementMoment (criticalPoint d)
        (orientedLatticePairs (section9FiniteMiddle i n)) L R Q₁ H₁ F₁ Q₃ H₃ F₃ A B W ≤
        K * (n : ℝ)^((8 : ℝ)-2*(d : ℝ)) * (B.card : ℝ)^2 *
          ∑ x ∈ A, ∑ y ∈ A, (max 1 (latticeDistance x y))^((8 : ℝ)-(d : ℝ)) := by
  obtain ⟨K,hK,hbound⟩ := section9_conditioned_replacement_source_bound hd asymptotics
  refine ⟨K,hK,?_⟩
  intro i n hn L R Q₁ H₁ F₁ Q₃ H₃ F₃ A B W hH₁ hH₃ hpos hLQ₃ hRQ₁ hL hB
  rw [section9_left_replacement_moment_eq (criticalPoint d) _ L R Q₁ H₁ F₁ Q₃ H₃ F₃ A B W
    hH₁ hH₃ hpos hLQ₃ hRQ₁]
  exact hbound i n hn L R Q₁ H₁ F₁ Q₃ H₃ F₃ A B W hH₁ hH₃ hpos hLQ₃ hRQ₁ hL hB

end NearCritical
