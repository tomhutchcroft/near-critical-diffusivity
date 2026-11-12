module
public import NearCritical.Section9CollisionProductEnvelope

/-! Source scaling of all four retained-witness collision products. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory
open scoped Classical BigOperators

/-- The actual first and third cubes are uniformly separated in the
supremum metric used by the collision kernel. -/
theorem section9_end_cubes_collision_separation {d : ℕ} (i : Fin d) (n : ℕ)
    {x y : Vertex d} (hx : x ∈ section9FiniteEndCube i n 0)
    (hy : y ∈ section9FiniteEndCube i n (2*(n:ℝ))) :
    (n : ℝ)/8 ≤ latticeDistance x y := by
  have hxhi := ((Finset.mem_filter.mp hx).2 i).2
  have hylo := ((Finset.mem_filter.mp hy).2 i).1
  simp only [ite_true,sub_zero] at hxhi
  simp only [ite_true] at hylo
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hcoord : |(x i : ℝ)-(y i : ℝ)| ≤ latticeDistance x y := by
    simpa only [latticeDistance,vertexReal,Real.dist_eq] using
      dist_le_pi_dist (vertexReal x) (vertexReal y) i
  have hab : (y i : ℝ)-(x i : ℝ) ≤ |(x i : ℝ)-(y i : ℝ)| := by
    rw [abs_sub_comm]
    exact le_abs_self _
  exact (show (n : ℝ)/8 ≤ (y i : ℝ)-(x i : ℝ) by linarith).trans (hab.trans hcoord)

/-- The mixed root-pair kernel has the additional n^(8-d) decay under
actual source end-cube separation. -/
theorem section9_cross_collision_kernel_sum_le {d : ℕ} (hd : 8 ≤ d)
    (i : Fin d) (n : ℕ) (hn : 0 < n) (A B : Finset (Vertex d))
    (hA : A ⊆ section9FiniteEndCube i n 0)
    (hB : B ⊆ section9FiniteEndCube i n (2*(n:ℝ))) :
    ∑ x ∈ A, ∑ y ∈ B, (max 1 (latticeDistance x y))^((8 : ℝ)-(d : ℝ)) ≤
      (A.card : ℝ)*(B.card : ℝ)*((n : ℝ)/8)^((8 : ℝ)-(d : ℝ)) := by
  have hdR : (8 : ℝ) ≤ d := by exact_mod_cast hd
  have hpoint (x : Vertex d) (hx : x ∈ A) (y : Vertex d) (hy : y ∈ B) :
      (max 1 (latticeDistance x y))^((8 : ℝ)-(d : ℝ)) ≤
        ((n : ℝ)/8)^((8 : ℝ)-(d : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos (by positivity)
      ((section9_end_cubes_collision_separation i n (hA hx) (hB hy)).trans (le_max_right _ _))
      (by linarith)
  calc
    _ ≤ ∑ _x ∈ A, ∑ _y ∈ B, ((n : ℝ)/8)^((8 : ℝ)-(d : ℝ)) :=
      Finset.sum_le_sum fun x hx => Finset.sum_le_sum fun y hy => hpoint x hx y hy
    _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul,mul_assoc]

/-- Two possibly different target cardinalities share the same squared
arm/mass factor and the source n^(8-2d) power. -/
theorem section9_collision_two_sided_scale {d : ℕ} {n a b C M M₀ : ℝ}
    (hn : 0 < n) (ha : 0 ≤ a) (hb : 0 ≤ b) (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hMass : M ≤ M₀*n^(2 : ℝ)) :
    ((a*(C*(n/8)^((2 : ℝ)-(d : ℝ))))*M) *
      ((b*(C*(n/8)^((2 : ℝ)-(d : ℝ))))*M) ≤
      ((C/8^((2 : ℝ)-(d : ℝ)))*M₀)^2 * n^((8 : ℝ)-2*(d : ℝ)) * a*b := by
  have hs := section9_same_side_scale (d := d) hn (by norm_num : (0 : ℝ) ≤ 1) hC hM hMass
  simp only [one_mul,one_pow,mul_one] at hs
  calc
    _ = ((C*(n/8)^((2 : ℝ)-(d : ℝ)))*M)^2 * a*b := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hs ha) hb

/-- All four collision products have one uniform source-scale bound. The
root families and opposite-arm cardinalities follow the two side choices. -/
theorem section9_all_collision_products_source_bound {d : ℕ} (hd : 9 ≤ d)
    (asymptotics : TwoPointAsymptotics d) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (i : Fin d) (n : ℕ), 0 < n →
      ∀ (L R Q₁ H₁ F₁ Q₃ H₃ F₃ A B W : Finset (Vertex d)),
      H₁ ⊆ Q₁ → H₃ ⊆ Q₃ →
      percolation d (criticalPoint d) (section9RevealEvent Q₁ H₁ Q₃ H₃ F₁ F₃) ≠ 0 →
      Disjoint L Q₃ → Disjoint R Q₁ → L ⊆ centeredBox d (3*n) → R ⊆ centeredBox d (3*n) →
      A ⊆ section9FiniteEndCube i n 0 → B ⊆ section9FiniteEndCube i n (2*(n:ℝ)) →
      ∀ s t : Bool,
      section9CollisionProduct (section9RevealedLaw (criticalPoint d) Q₁ H₁ Q₃ H₃ F₁ F₃)
        (orientedLatticePairs (section9FiniteMiddle i n)) L R Q₁ F₁ Q₃ F₃ A B W s t ≤
        K * (n : ℝ)^((8 : ℝ)-2*(d : ℝ)) *
          (if s then (A.card : ℝ) else (B.card : ℝ)) *
          (if t then (A.card : ℝ) else (B.card : ℝ)) *
          ∑ x ∈ (if s then B else A), ∑ y ∈ (if t then B else A),
            (max 1 (latticeDistance x y))^((8 : ℝ)-(d : ℝ)) := by
  have hd2 : 2 ≤ d := by omega
  obtain ⟨C,hC,hArm⟩ := section9_middle_to_either_end_arm_le hd2 asymptotics
  obtain ⟨G,hG,green⟩ := criticalSupGreenUpper_of_asymptotics hd2 asymptotics
  let J : ℝ := 2*(d : ℝ)*3^(d-1)
  let M₀ : ℝ := (2*(d : ℝ))*(G*(1+49*J))
  let D : ℝ := G^4*((4 : ℝ)^((d : ℝ)-2)*(2+19*J))^2 *
    ((4 : ℝ)^((d : ℝ)-4)*(162+163*J))
  let Z : ℝ := ((C/8^((2 : ℝ)-(d : ℝ)))*M₀)^2
  have hD : 0 ≤ D := by dsimp [D,J]; positivity
  refine ⟨Z*D,mul_nonneg (sq_nonneg _) hD,?_⟩
  intro i n hn L R Q₁ H₁ F₁ Q₃ H₃ F₃ A B W hH₁ hH₃ hpos hLQ₃ hRQ₁ hL hR hA hB s t
  let E := orientedLatticePairs (section9FiniteMiddle i n)
  let rate : ℝ := C*((n : ℝ)/8)^((2 : ℝ)-(d : ℝ))
  let M : ℝ := (2*(d : ℝ))*(G*(1+J*((6*n : ℕ)+1 : ℝ)^2))
  let opp := fun b : Bool => if b then (A.card : ℝ) else (B.card : ℝ)
  have hOpp (b : Bool) : 0 ≤ opp b := by cases b <;> dsimp [opp] <;> positivity
  have hM : 0 ≤ M := by dsimp [M,J]; positivity
  have hRate : 0 ≤ rate := by dsimp [rate]; positivity
  have hMass : M ≤ M₀*(n : ℝ)^(2 : ℝ) := by
    rw [Real.rpow_two]
    have hm := mul_le_mul_of_nonneg_left
      (section9_case_three_mass_normalization (K := J) hG.le (by dsimp [J]; positivity) hn)
      (by positivity : 0 ≤ 2*(d : ℝ))
    simpa only [M,M₀,mul_assoc] using hm
  have hTail (u : Vertex d) (hu : u ∈ L) : ∑ e ∈ E,
      (percolation d (criticalPoint d)).real
        (connectionToSetEvent (L : Set (Vertex d)) e.1 {u}) ≤ M :=
    section9_middle_tail_mass_le hd2 hG.le green i n L u (hL hu)
  have hHead (v : Vertex d) (hv : v ∈ R) : ∑ e ∈ E,
      (percolation d (criticalPoint d)).real
        (connectionToSetEvent (R : Set (Vertex d)) e.2 {v}) ≤ M := by
    have hh := section9_middle_head_mass_le hd2 hG.le green i n R v (hR hv)
    simp_rw [section9RightArm_symm R v] at hh
    exact hh
  have heach := section9_collision_product_envelope hd hG.le green E
    (fun e he => (mem_orientedLatticePairs_swap_iff (section9FiniteMiddle i n) e).mpr he)
    L R Q₁ H₁ F₁ Q₃ H₃ F₃ A B W hH₁ hH₃ hpos hLQ₃ hRQ₁
    ((B.card : ℝ)*rate) ((A.card : ℝ)*rate) M M
    (mul_nonneg (Nat.cast_nonneg _) hRate) (mul_nonneg (Nat.cast_nonneg _) hRate) hM hM
    (fun e he => hArm i n hn R B e.2 ((mem_orientedLatticePairs _ _ _).mp he).2.1
      (hB.trans Finset.subset_union_right))
    (fun e he => hArm i n hn L A e.1 ((mem_orientedLatticePairs _ _ _).mp he).1
      (hA.trans Finset.subset_union_left)) hTail hHead s t
  dsimp only at heach
  have hBudget (b : Bool) :
      (if b then ((A.card : ℝ)*rate)*M else ((B.card : ℝ)*rate)*M) = (opp b*rate)*M := by
    cases b <;> rfl
  simp_rw [hBudget] at heach
  have hs := section9_collision_two_sided_scale (d := d) (by exact_mod_cast hn)
    (hOpp s) (hOpp t) hC.le hM hMass
  have hroots : 0 ≤ ∑ x ∈ (if s then B else A), ∑ y ∈ (if t then B else A),
      (max 1 (latticeDistance x y))^((8 : ℝ)-(d : ℝ)) :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
      Real.rpow_nonneg (zero_le_one.trans (le_max_left _ _)) _
  calc
    _ ≤ ((opp s*rate)*M)*((opp t*rate)*M)*D *
        ∑ x ∈ (if s then B else A), ∑ y ∈ (if t then B else A),
          (max 1 (latticeDistance x y))^((8 : ℝ)-(d : ℝ)) := heach
    _ ≤ (Z*(n : ℝ)^((8 : ℝ)-2*(d : ℝ))*opp s*opp t)*D *
        ∑ x ∈ (if s then B else A), ∑ y ∈ (if t then B else A),
          (max 1 (latticeDistance x y))^((8 : ℝ)-(d : ℝ)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hs hD) hroots
    _ = _ := by dsimp [opp]; ring

/-- Both mixed original/replacement side products have the source
n^(16-3d)|A|²|B|² bound, using actual end-cube separation. -/
theorem section9_mixed_collision_products_source_bound {d : ℕ} (hd : 9 ≤ d)
    (asymptotics : TwoPointAsymptotics d) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (i : Fin d) (n : ℕ), 0 < n →
      ∀ (L R Q₁ H₁ F₁ Q₃ H₃ F₃ A B W : Finset (Vertex d)),
      H₁ ⊆ Q₁ → H₃ ⊆ Q₃ →
      percolation d (criticalPoint d) (section9RevealEvent Q₁ H₁ Q₃ H₃ F₁ F₃) ≠ 0 →
      Disjoint L Q₃ → Disjoint R Q₁ → L ⊆ centeredBox d (3*n) → R ⊆ centeredBox d (3*n) →
      A ⊆ section9FiniteEndCube i n 0 → B ⊆ section9FiniteEndCube i n (2*(n:ℝ)) →
      ∀ s : Bool,
      section9CollisionProduct (section9RevealedLaw (criticalPoint d) Q₁ H₁ Q₃ H₃ F₁ F₃)
        (orientedLatticePairs (section9FiniteMiddle i n)) L R Q₁ F₁ Q₃ F₃ A B W s (!s) ≤
        K*(n : ℝ)^((16 : ℝ)-3*(d : ℝ))*(A.card : ℝ)^2*(B.card : ℝ)^2 := by
  obtain ⟨C,hC,hbound⟩ := section9_all_collision_products_source_bound hd asymptotics
  refine ⟨C/8^((8 : ℝ)-(d : ℝ)),div_nonneg hC (by positivity),?_⟩
  intro i n hn L R Q₁ H₁ F₁ Q₃ H₃ F₃ A B W hH₁ hH₃ hpos hLQ₃ hRQ₁ hL hR hA hB s
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hkernel : (∑ x ∈ (if s then B else A), ∑ y ∈ (if !s then B else A),
      (max 1 (latticeDistance x y))^((8 : ℝ)-(d : ℝ))) ≤
      (A.card : ℝ)*(B.card : ℝ)*((n : ℝ)/8)^((8 : ℝ)-(d : ℝ)) := by
    cases s
    · simpa using section9_cross_collision_kernel_sum_le (by omega) i n hn A B hA hB
    · change (∑ x ∈ B, ∑ y ∈ A, (max 1 (latticeDistance x y))^((8 : ℝ)-(d : ℝ))) ≤ _
      rw [Finset.sum_comm]
      simpa only [latticeDistance_comm] using
        section9_cross_collision_kernel_sum_le (by omega) i n hn A B hA hB
  have hc := hbound i n hn L R Q₁ H₁ F₁ Q₃ H₃ F₃ A B W
    hH₁ hH₃ hpos hLQ₃ hRQ₁ hL hR hA hB s (!s)
  have hcards : (if s then (A.card : ℝ) else (B.card : ℝ)) *
      (if !s then (A.card : ℝ) else (B.card : ℝ)) = (A.card : ℝ)*(B.card : ℝ) := by
    cases s <;> simp [mul_comm]
  have hcoef : C*(n : ℝ)^((8 : ℝ)-2*(d : ℝ)) *
      (if s then (A.card : ℝ) else (B.card : ℝ)) *
      (if !s then (A.card : ℝ) else (B.card : ℝ)) =
      C*(n : ℝ)^((8 : ℝ)-2*(d : ℝ)) * ((A.card : ℝ)*(B.card : ℝ)) := by
    rw [mul_assoc _ _ (if !s then (A.card : ℝ) else (B.card : ℝ)),hcards]
  rw [hcoef] at hc
  calc
    _ ≤ (C*(n : ℝ)^((8 : ℝ)-2*(d : ℝ))*((A.card : ℝ)*(B.card : ℝ))) *
        ((A.card : ℝ)*(B.card : ℝ)*((n : ℝ)/8)^((8 : ℝ)-(d : ℝ))) :=
      hc.trans (mul_le_mul_of_nonneg_left hkernel
        (mul_nonneg (mul_nonneg hC (Real.rpow_nonneg (Nat.cast_nonneg n) _))
          (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))))
    _ = (C/8^((8 : ℝ)-(d : ℝ))) *
        ((n : ℝ)^((8 : ℝ)-2*(d : ℝ))*(n : ℝ)^((8 : ℝ)-(d : ℝ))) *
        (A.card : ℝ)^2*(B.card : ℝ)^2 := by
      rw [Real.div_rpow hnR.le (by norm_num : (0 : ℝ) ≤ 8)]
      ring
    _ = _ := by
      have he : ((8 : ℝ)-2*(d : ℝ)) + ((8 : ℝ)-(d : ℝ)) = (16 : ℝ)-3*(d : ℝ) := by ring
      rw [← Real.rpow_add hnR,he]

end NearCritical
