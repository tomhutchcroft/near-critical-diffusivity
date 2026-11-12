module
public import NearCritical.Section9QuartetCandidateSum
public import NearCritical.Section9CrossJointBound
public import NearCritical.Section9OverlapTranspose
public import NearCritical.Section9RightMarkedBounds

/-! The three original cross-overlap source estimates. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory
open scoped Classical BigOperators

/-- Source Case III: two separated remaining arms multiply the actual
candidate-summed four-terminal connection bound. -/
theorem section9_left_right_pattern_source_sum_bound {d : ℕ} (hd : 9 ≤ d)
    (asymptotics : TwoPointAsymptotics d) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (i : Fin d) (n : ℕ), 0 < n →
      ∀ (L R Q₁ H₁ F₁ Q₃ H₃ F₃ A B : Finset (Vertex d)),
      H₁ ⊆ Q₁ → H₃ ⊆ Q₃ →
      percolation d (criticalPoint d) (section9RevealEvent Q₁ H₁ Q₃ H₃ F₁ F₃) ≠ 0 →
      Disjoint L Q₃ → Disjoint R Q₁ → L ⊆ centeredBox d (3*n) → R ⊆ centeredBox d (3*n) →
      A ⊆ section9FiniteEndCube i n 0 → B ⊆ section9FiniteEndCube i n (2*(n:ℝ)) →
      let ν := section9RevealedLaw (criticalPoint d) Q₁ H₁ Q₃ H₃ F₁ F₃
      let E := orientedLatticePairs (section9FiniteMiddle i n)
      (∑ e ∈ E, ∑ f ∈ E, ν.real (section9OverlapPatternEvent .leftRight L R Q₁ F₁ Q₃ F₃ A B e f)) ≤
        K*(n : ℝ)^((14 : ℝ)-3*(d : ℝ))*(A.card : ℝ)^2*(B.card : ℝ)^2 := by
  obtain ⟨Cq,hCq,hQuartet⟩ := section9_quartet_candidate_source_sum_bound hd asymptotics
  obtain ⟨Ca,hCa,hArm⟩ := section9_middle_to_either_end_arm_le (by omega : 2 ≤ d) asymptotics
  let q : ℝ := 2-(d : ℝ)
  refine ⟨(Ca/8^q)^2*Cq,mul_nonneg (sq_nonneg _) hCq,?_⟩
  intro i n hn L R Q₁ H₁ F₁ Q₃ H₃ F₃ A B hH₁ hH₃ hpos hLQ₃ hRQ₁ hL hR hA hB ν E
  let D := L ∪ R
  let J := fun e f : Vertex d × Vertex d => (percolation d (criticalPoint d)).real
    (section9CrossJointEvent D e.1 f.2 A B)
  let rate : ℝ := Ca*((n : ℝ)/8)^q
  let H : ℝ := ((B.card : ℝ)*rate)*((A.card : ℝ)*rate)
  have hRate : 0 ≤ rate := mul_nonneg hCa.le (Real.rpow_nonneg (by positivity) _)
  have hH : 0 ≤ H := mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hRate)
    (mul_nonneg (Nat.cast_nonneg _) hRate)
  have hRight (e : Vertex d × Vertex d) (he : e ∈ E) :
      (percolation d (criticalPoint d)).real
        (connectionToSetEvent (R : Set (Vertex d)) e.2 (B : Set (Vertex d))) ≤ (B.card : ℝ)*rate :=
    hArm i n hn R B e.2 ((mem_orientedLatticePairs _ _ _).mp he).2.1 (hB.trans Finset.subset_union_right)
  have hLeft (f : Vertex d × Vertex d) (hf : f ∈ E) :
      (percolation d (criticalPoint d)).real
        (connectionToSetEvent (L : Set (Vertex d)) f.1 (A : Set (Vertex d))) ≤ (A.card : ℝ)*rate :=
    hArm i n hn L A f.1 ((mem_orientedLatticePairs _ _ _).mp hf).1 (hA.trans Finset.subset_union_left)
  have heach (e : Vertex d × Vertex d) (he : e ∈ E) (f : Vertex d × Vertex d) (hf : f ∈ E) :
      ν.real (section9OverlapPatternEvent .leftRight L R Q₁ F₁ Q₃ F₃ A B e f) ≤ J e f*H :=
    (section9_conditioned_cross_singleton_joint_probability_le (criticalPoint d)
      L R Q₁ H₁ F₁ Q₃ H₃ F₃ A B hH₁ hH₃ hpos hLQ₃ hRQ₁ e f).trans
      (mul_le_mul_of_nonneg_left
        (mul_le_mul (hRight e he) (hLeft f hf) measureReal_nonneg
          (mul_nonneg (Nat.cast_nonneg _) hRate)) measureReal_nonneg)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hp : ((n : ℝ)^q)^2*(n : ℝ)^((10 : ℝ)-(d : ℝ)) =
      (n : ℝ)^((14 : ℝ)-3*(d : ℝ)) := by
    rw [pow_two,← Real.rpow_add hnR,← Real.rpow_add hnR]
    congr 1
    dsimp [q]
    ring
  calc
    _ ≤ ∑ e ∈ E, ∑ f ∈ E, J e f*H :=
      Finset.sum_le_sum fun e he => Finset.sum_le_sum fun f hf => heach e he f hf
    _ = (∑ e ∈ E, ∑ f ∈ E, J e f)*H := by simp only [Finset.sum_mul]
    _ ≤ (Cq*(n : ℝ)^((10 : ℝ)-(d : ℝ))*(A.card : ℝ)*(B.card : ℝ))*H :=
      mul_le_mul_of_nonneg_right (hQuartet i n hn D A B (Finset.union_subset hL hR) hA hB) hH
    _ = ((Ca/8^q)^2*Cq)*(((n : ℝ)^q)^2*(n : ℝ)^((10 : ℝ)-(d : ℝ)))*
        (A.card : ℝ)^2*(B.card : ℝ)^2 := by
      dsimp [H,rate]
      rw [Real.div_rpow hnR.le (by norm_num : (0 : ℝ) ≤ 8)]
      ring
    _ = _ := by rw [hp]

/-- Source Case IV: one mixed joint factor is bounded by a separated
tripod, while the other is summed over both actual candidates. -/
theorem section9_cross_pattern_source_sum_bound {d : ℕ} (hd : 9 ≤ d)
    (asymptotics : TwoPointAsymptotics d) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (i : Fin d) (n : ℕ), 0 < n →
      ∀ (L R Q₁ H₁ F₁ Q₃ H₃ F₃ A B : Finset (Vertex d)),
      H₁ ⊆ Q₁ → H₃ ⊆ Q₃ →
      percolation d (criticalPoint d) (section9RevealEvent Q₁ H₁ Q₃ H₃ F₁ F₃) ≠ 0 →
      Disjoint L Q₃ → Disjoint R Q₁ → L ⊆ centeredBox d (3*n) → R ⊆ centeredBox d (3*n) →
      A ⊆ section9FiniteEndCube i n 0 → B ⊆ section9FiniteEndCube i n (2*(n:ℝ)) →
      let ν := section9RevealedLaw (criticalPoint d) Q₁ H₁ Q₃ H₃ F₁ F₃
      let E := orientedLatticePairs (section9FiniteMiddle i n)
      (∑ e ∈ E, ∑ f ∈ E, ν.real (section9OverlapPatternEvent .cross L R Q₁ F₁ Q₃ F₃ A B e f)) ≤
        K*(n : ℝ)^((16 : ℝ)-3*(d : ℝ))*(A.card : ℝ)^2*(B.card : ℝ)^2 := by
  obtain ⟨Cq,hCq,hQuartet⟩ := section9_quartet_candidate_source_sum_bound hd asymptotics
  obtain ⟨Ct,hCt,hTripod⟩ := section9_cross_joint_uniform_tripod_bound (by omega : 5 ≤ d) asymptotics
  let q : ℝ := 6-2*(d : ℝ)
  refine ⟨(Ct/8^q)*Cq,mul_nonneg (div_nonneg hCt.le (by positivity)) hCq,?_⟩
  intro i n hn L R Q₁ H₁ F₁ Q₃ H₃ F₃ A B hH₁ hH₃ hpos hLQ₃ hRQ₁ hL hR hA hB ν E
  let D := L ∪ R
  let J := fun e f : Vertex d × Vertex d => (percolation d (criticalPoint d)).real
    (section9CrossJointEvent D e.1 f.2 A B)
  let H : ℝ := (A.card : ℝ)*(B.card : ℝ)*(Ct*((n : ℝ)/8)^q)
  have hH : 0 ≤ H := mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    (mul_nonneg hCt.le (Real.rpow_nonneg (by positivity) _))
  have heach (e : Vertex d × Vertex d) (he : e ∈ E) (f : Vertex d × Vertex d) (hf : f ∈ E) :
      ν.real (section9OverlapPatternEvent .cross L R Q₁ F₁ Q₃ F₃ A B e f) ≤ J e f*H :=
    (section9_conditioned_double_cross_joint_probability_le (criticalPoint d)
      L R Q₁ H₁ F₁ Q₃ H₃ F₃ A B hH₁ hH₃ hpos hLQ₃ hRQ₁ e f).trans
      (mul_le_mul_of_nonneg_left
        (hTripod i n hn D A B f.1 e.2 ((mem_orientedLatticePairs _ _ _).mp hf).1 hA hB)
        measureReal_nonneg)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hp : (n : ℝ)^((10 : ℝ)-(d : ℝ))*(n : ℝ)^q =
      (n : ℝ)^((16 : ℝ)-3*(d : ℝ)) := by
    rw [← Real.rpow_add hnR]
    congr 1
    dsimp [q]
    ring
  calc
    _ ≤ ∑ e ∈ E, ∑ f ∈ E, J e f*H :=
      Finset.sum_le_sum fun e he => Finset.sum_le_sum fun f hf => heach e he f hf
    _ = (∑ e ∈ E, ∑ f ∈ E, J e f)*H := by simp only [Finset.sum_mul]
    _ ≤ (Cq*(n : ℝ)^((10 : ℝ)-(d : ℝ))*(A.card : ℝ)*(B.card : ℝ))*H :=
      mul_le_mul_of_nonneg_right (hQuartet i n hn D A B (Finset.union_subset hL hR) hA hB) hH
    _ = ((Ct/8^q)*Cq)*((n : ℝ)^((10 : ℝ)-(d : ℝ))*(n : ℝ)^q)*
        (A.card : ℝ)^2*(B.card : ℝ)^2 := by
      dsimp [H]
      rw [Real.div_rpow hnR.le (by norm_num : (0 : ℝ) ≤ 8)]
      ring
    _ = _ := by rw [hp]

/-- Source Case V has exactly the same bound as Case III, by candidate
label transposition rather than any spatial symmetry. -/
theorem section9_right_left_pattern_source_sum_bound {d : ℕ} (hd : 9 ≤ d)
    (asymptotics : TwoPointAsymptotics d) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (i : Fin d) (n : ℕ), 0 < n →
      ∀ (L R Q₁ H₁ F₁ Q₃ H₃ F₃ A B : Finset (Vertex d)),
      H₁ ⊆ Q₁ → H₃ ⊆ Q₃ →
      percolation d (criticalPoint d) (section9RevealEvent Q₁ H₁ Q₃ H₃ F₁ F₃) ≠ 0 →
      Disjoint L Q₃ → Disjoint R Q₁ → L ⊆ centeredBox d (3*n) → R ⊆ centeredBox d (3*n) →
      A ⊆ section9FiniteEndCube i n 0 → B ⊆ section9FiniteEndCube i n (2*(n:ℝ)) →
      let ν := section9RevealedLaw (criticalPoint d) Q₁ H₁ Q₃ H₃ F₁ F₃
      let E := orientedLatticePairs (section9FiniteMiddle i n)
      (∑ e ∈ E, ∑ f ∈ E, ν.real (section9OverlapPatternEvent .rightLeft L R Q₁ F₁ Q₃ F₃ A B e f)) ≤
        K*(n : ℝ)^((14 : ℝ)-3*(d : ℝ))*(A.card : ℝ)^2*(B.card : ℝ)^2 := by
  obtain ⟨K,hK,hbound⟩ := section9_left_right_pattern_source_sum_bound hd asymptotics
  refine ⟨K,hK,?_⟩
  intro i n hn L R Q₁ H₁ F₁ Q₃ H₃ F₃ A B hH₁ hH₃ hpos hLQ₃ hRQ₁ hL hR hA hB ν E
  calc
    _ = ∑ e ∈ E, ∑ f ∈ E,
        ν.real (section9OverlapPatternEvent .leftRight L R Q₁ F₁ Q₃ F₃ A B e f) :=
      (section9_cross_singleton_sums_transpose ν E L R Q₁ F₁ Q₃ F₃ A B).symm
    _ ≤ _ := hbound i n hn L R Q₁ H₁ F₁ Q₃ H₃ F₃ A B
      hH₁ hH₃ hpos hLQ₃ hRQ₁ hL hR hA hB

end NearCritical
