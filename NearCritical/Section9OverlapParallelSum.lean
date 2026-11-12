module
public import NearCritical.Section9OverlapParallel
public import NearCritical.Section9CandidateBubble
public import NearCritical.Section8IntegrableConvolution
public import NearCritical.Section9CollisionScale

/-! Source Case II: finite parallel-overlap diagrams and their source decay. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory
open scoped Classical BigOperators

private theorem parallel_tree_factorization {d : ℕ}
    (E : Finset (Vertex d × Vertex d)) (A B L R : Finset (Vertex d))
    (P : Vertex d → Vertex d → ℝ) :
    (∑ e ∈ E, ∑ f ∈ E,
      (∑ x ∈ A, ∑ u ∈ L, P u e.1*(P u f.1*P x u)) *
      (∑ y ∈ B, ∑ v ∈ R, P v e.2*(P v f.2*P y v))) =
    ∑ x ∈ A, ∑ y ∈ B, ∑ u ∈ L, ∑ v ∈ R,
      P x u*P y v*(∑ e ∈ E, P u e.1*P v e.2)^2 := by
  let Z := (A.product L).product (B.product R)
  let c := fun z : (Vertex d × Vertex d) × (Vertex d × Vertex d) => P z.1.1 z.1.2*P z.2.1 z.2.2
  let b := fun (e : Vertex d × Vertex d) (z : (Vertex d × Vertex d) × (Vertex d × Vertex d)) =>
    P z.1.2 e.1*P z.2.2 e.2
  have hexpand (e f : Vertex d × Vertex d) :
      (∑ x ∈ A, ∑ u ∈ L, P u e.1*(P u f.1*P x u)) *
      (∑ y ∈ B, ∑ v ∈ R, P v e.2*(P v f.2*P y v)) =
      ∑ z ∈ Z, c z*(b e z*b f z) := by
    simp only [Z,Finset.product_eq_sprod,Finset.sum_product,c,b]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro x _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro u _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _
    ring
  have hsquare (z : (Vertex d × Vertex d) × (Vertex d × Vertex d)) :
      (∑ e ∈ E, ∑ f ∈ E, c z*(b e z*b f z)) = c z*(∑ e ∈ E, b e z)^2 := by
    simp only [pow_two,Finset.sum_mul,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _
    apply Finset.sum_congr rfl
    intro f _
    ring
  calc
    _ = ∑ e ∈ E, ∑ f ∈ E, ∑ z ∈ Z, c z*(b e z*b f z) := by simp_rw [hexpand]
    _ = ∑ z ∈ Z, ∑ e ∈ E, ∑ f ∈ E, c z*(b e z*b f z) := by
      calc
        _ = ∑ e ∈ E, ∑ z ∈ Z, ∑ f ∈ E, c z*(b e z*b f z) := by
          apply Finset.sum_congr rfl
          intro e _
          rw [Finset.sum_comm]
        _ = _ := Finset.sum_comm
    _ = ∑ z ∈ Z, c z*(∑ e ∈ E, b e z)^2 := Finset.sum_congr rfl fun z _ => hsquare z
    _ = ∑ x ∈ A, ∑ u ∈ L, ∑ y ∈ B, ∑ v ∈ R,
        P x u*P y v*(∑ e ∈ E, P u e.1*P v e.2)^2 := by
      simp only [Z,Finset.product_eq_sprod,Finset.sum_product,c,b]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.sum_comm]

/-- The actual conditioned parallel-pattern sum is bounded by the finite
squared candidate bubble, with the genuine tail/head coordinates retained. -/
theorem section9_parallel_overlap_sum_diagram_le {d : ℕ}
    (S L R Q₁ H₁ F₁ Q₃ H₃ F₃ A B : Finset (Vertex d))
    (hH₁ : H₁ ⊆ Q₁) (hH₃ : H₃ ⊆ Q₃)
    (hpos : percolation d (criticalPoint d) (section9RevealEvent Q₁ H₁ Q₃ H₃ F₁ F₃) ≠ 0)
    (hLQ₃ : Disjoint L Q₃) (hRQ₁ : Disjoint R Q₁) :
    let ν := section9RevealedLaw (criticalPoint d) Q₁ H₁ Q₃ H₃ F₁ F₃
    let E := orientedLatticePairs S
    let P := twoPoint d (criticalPoint d)
    (∑ e ∈ E, ∑ f ∈ E, ν.real (section9OverlapPatternEvent .parallel L R Q₁ F₁ Q₃ F₃ A B e f)) ≤
      ∑ x ∈ A, ∑ y ∈ B, ∑ u ∈ L, ∑ v ∈ R,
        P x u*P y v*(∑ e ∈ E, P u e.1*P v e.2)^2 := by
  intro ν E P
  have hP (a b : Vertex d) : 0 ≤ P a b := measureReal_nonneg
  have hDom (D : Finset (Vertex d)) (a b : Vertex d) :
      (percolation d (criticalPoint d)).real (connectionToSetEvent (D : Set (Vertex d)) a {b}) ≤ P a b := by
    simpa only [Finset.coe_singleton,Finset.sum_singleton] using
      connectionToSet_probability_le_twoPoint_sum (criticalPoint d) (D : Set (Vertex d)) a {b}
  have hTripod (D T : Finset (Vertex d)) (a b : Vertex d) :
      (∑ x ∈ T, ∑ u ∈ D,
        (percolation d (criticalPoint d)).real (connectionToSetEvent (D : Set (Vertex d)) a {u}) *
          ((percolation d (criticalPoint d)).real (connectionToSetEvent (D : Set (Vertex d)) u {b}) *
           (percolation d (criticalPoint d)).real (connectionToSetEvent (D : Set (Vertex d)) x {u}))) ≤
      ∑ x ∈ T, ∑ u ∈ D, P u a*(P u b*P x u) := by
    apply Finset.sum_le_sum
    intro x _
    apply Finset.sum_le_sum
    intro u _
    have hfirst : (percolation d (criticalPoint d)).real
        (connectionToSetEvent (D : Set (Vertex d)) a {u}) ≤ P u a :=
      (hDom D a u).trans_eq (twoPoint_symm (criticalPoint d) a u)
    exact mul_le_mul hfirst
      (mul_le_mul (hDom D u b) (hDom D x u) measureReal_nonneg (hP _ _))
      (mul_nonneg measureReal_nonneg measureReal_nonneg) (hP _ _)
  calc
    _ ≤ ∑ e ∈ E, ∑ f ∈ E,
        (∑ x ∈ A, ∑ u ∈ L, P u e.1*(P u f.1*P x u)) *
        (∑ y ∈ B, ∑ v ∈ R, P v e.2*(P v f.2*P y v)) := by
      apply Finset.sum_le_sum
      intro e _
      apply Finset.sum_le_sum
      intro f _
      exact (section9_conditioned_parallel_overlap_tree_bound (criticalPoint d)
        L R Q₁ H₁ F₁ Q₃ H₃ F₃ A B hH₁ hH₃ hpos hLQ₃ hRQ₁ e f).trans
        (mul_le_mul (hTripod L A e.1 f.1) (hTripod R B e.2 f.2)
          (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
            mul_nonneg measureReal_nonneg (mul_nonneg measureReal_nonneg measureReal_nonneg))
          (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
            mul_nonneg (hP _ _) (mul_nonneg (hP _ _) (hP _ _))))
    _ = _ := parallel_tree_factorization E A B L R P

/-- The squared candidate-bubble diagram contracts to the fourth-order
root kernel uniformly over all finite candidate and branch cutoffs. -/
theorem section9_parallel_overlap_sum_kernel_bound {d : ℕ} (hd : 9 ≤ d) {G : ℝ}
    (hG : 0 ≤ G) (green : CriticalSupGreenUpper d G) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (S L R Q₁ H₁ F₁ Q₃ H₃ F₃ A B : Finset (Vertex d)),
      H₁ ⊆ Q₁ → H₃ ⊆ Q₃ →
      percolation d (criticalPoint d) (section9RevealEvent Q₁ H₁ Q₃ H₃ F₁ F₃) ≠ 0 →
      Disjoint L Q₃ → Disjoint R Q₁ →
      let ν := section9RevealedLaw (criticalPoint d) Q₁ H₁ Q₃ H₃ F₁ F₃
      let E := orientedLatticePairs S
      (∑ e ∈ E, ∑ f ∈ E, ν.real (section9OverlapPatternEvent .parallel L R Q₁ F₁ Q₃ F₃ A B e f)) ≤
        C*(∑ x ∈ A, ∑ y ∈ B, (max 1 (latticeDistance x y))^((4 : ℝ)-(d : ℝ))) := by
  let Cgreen : ℝ := (4 : ℝ)^((d : ℝ)-2)*(2+19*(2*(d : ℝ)*3^(d-1)))
  let Ce : ℝ := (2*(d : ℝ))*(2 : ℝ)^((d : ℝ)-2)*G^2*Cgreen
  let Cf : ℝ := ((2 : ℝ)^((d : ℝ)-2)*(1+5*(2*(d : ℝ)*3^(d-1))) +
    (2 : ℝ)^(2*(d : ℝ)-8)*(1+9*(2*(d : ℝ)*3^(d-1))))*Cgreen
  let Cg : ℝ := G^2*Ce^2
  have hCe : 0 ≤ Ce := by dsimp [Ce,Cgreen]; positivity
  have hCf : 0 ≤ Cf := by dsimp [Cf,Cgreen]; positivity
  have hCg : 0 ≤ Cg := mul_nonneg (sq_nonneg _) (sq_nonneg _)
  refine ⟨Cg*Cf,mul_nonneg hCg hCf,?_⟩
  intro S L R Q₁ H₁ F₁ Q₃ H₃ F₃ A B hH₁ hH₃ hpos hLQ₃ hRQ₁ ν E
  let P := twoPoint d (criticalPoint d)
  let J := fun u v => ∑ e ∈ E, P u e.1*P v e.2
  have hP (a b : Vertex d) : 0 ≤ P a b := measureReal_nonneg
  have hJ (u v : Vertex d) : 0 ≤ J u v :=
    Finset.sum_nonneg fun _ _ => mul_nonneg (hP _ _) (hP _ _)
  have hJsq (u v : Vertex d) : (J u v)^2 ≤
      Ce^2*(max 1 (latticeDistance u v))^((8 : ℝ)-2*(d : ℝ)) := by
    have hb : J u v ≤ Ce*(max 1 (latticeDistance u v))^((4 : ℝ)-(d : ℝ)) :=
      section9_candidate_bubble_le (by omega) hG green S u v
    have hbase : 0 < max 1 (latticeDistance u v) := zero_lt_one.trans_le (le_max_left _ _)
    calc
      _ ≤ (Ce*(max 1 (latticeDistance u v))^((4 : ℝ)-(d : ℝ)))^2 :=
        pow_le_pow_left₀ (hJ u v) hb 2
      _ = _ := by
        rw [mul_pow,pow_two ((max 1 (latticeDistance u v))^((4 : ℝ)-(d : ℝ))),← Real.rpow_add hbase]
        congr 2
        ring
  have hpoint (x y u v : Vertex d) : P x u*P y v*(J u v)^2 ≤
      Cg*((max 1 (latticeDistance x u))^((2 : ℝ)-(d : ℝ)) *
        (max 1 (latticeDistance u v))^((8 : ℝ)-2*(d : ℝ)) *
        (max 1 (latticeDistance v y))^((2 : ℝ)-(d : ℝ))) := by
    calc
      _ ≤ ((G*(max 1 (latticeDistance x u))^((2 : ℝ)-(d : ℝ))) *
          (G*(max 1 (latticeDistance y v))^((2 : ℝ)-(d : ℝ)))) *
          (Ce^2*(max 1 (latticeDistance u v))^((8 : ℝ)-2*(d : ℝ))) :=
        mul_le_mul (mul_le_mul (green x u) (green y v) (hP _ _) (by positivity))
          (hJsq u v) (sq_nonneg _) (by positivity)
      _ = _ := by rw [latticeDistance_comm v y]; dsimp [Cg]; ring
  have hconv (x y : Vertex d) :
      (∑ u ∈ L, ∑ v ∈ R,
        (max 1 (latticeDistance x u))^((2 : ℝ)-(d : ℝ)) *
        (max 1 (latticeDistance u v))^((8 : ℝ)-2*(d : ℝ)) *
        (max 1 (latticeDistance v y))^((2 : ℝ)-(d : ℝ))) ≤
      Cf*(max 1 (latticeDistance x y))^((4 : ℝ)-(d : ℝ)) :=
    Section8.green_squared_fourth_green_convolution_le hd L R x y
  calc
    _ ≤ ∑ x ∈ A, ∑ y ∈ B, ∑ u ∈ L, ∑ v ∈ R, P x u*P y v*(J u v)^2 :=
      section9_parallel_overlap_sum_diagram_le S L R Q₁ H₁ F₁ Q₃ H₃ F₃ A B
        hH₁ hH₃ hpos hLQ₃ hRQ₁
    _ ≤ ∑ x ∈ A, ∑ y ∈ B, ∑ u ∈ L, ∑ v ∈ R,
        Cg*((max 1 (latticeDistance x u))^((2 : ℝ)-(d : ℝ)) *
          (max 1 (latticeDistance u v))^((8 : ℝ)-2*(d : ℝ)) *
          (max 1 (latticeDistance v y))^((2 : ℝ)-(d : ℝ))) :=
      Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ =>
        Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun v _ => hpoint x y u v
    _ = ∑ x ∈ A, ∑ y ∈ B, Cg*(∑ u ∈ L, ∑ v ∈ R,
        (max 1 (latticeDistance x u))^((2 : ℝ)-(d : ℝ)) *
        (max 1 (latticeDistance u v))^((8 : ℝ)-2*(d : ℝ)) *
        (max 1 (latticeDistance v y))^((2 : ℝ)-(d : ℝ))) := by simp only [Finset.mul_sum]
    _ ≤ ∑ x ∈ A, ∑ y ∈ B,
        Cg*(Cf*(max 1 (latticeDistance x y))^((4 : ℝ)-(d : ℝ))) :=
      Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ =>
        mul_le_mul_of_nonneg_left (hconv x y) hCg
    _ = _ := by simp only [Finset.mul_sum]; ring

/-- Source Case II for the actual parallel pattern, including diagonal
candidate pairs, with all candidate and analytic inputs proved internally. -/
theorem section9_parallel_overlap_source_sum_bound {d : ℕ} (hd : 9 ≤ d)
    (asymptotics : TwoPointAsymptotics d) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (i : Fin d) (n : ℕ), 0 < n →
      ∀ (L R Q₁ H₁ F₁ Q₃ H₃ F₃ A B : Finset (Vertex d)),
      H₁ ⊆ Q₁ → H₃ ⊆ Q₃ →
      percolation d (criticalPoint d) (section9RevealEvent Q₁ H₁ Q₃ H₃ F₁ F₃) ≠ 0 →
      Disjoint L Q₃ → Disjoint R Q₁ →
      A ⊆ section9FiniteEndCube i n 0 → B ⊆ section9FiniteEndCube i n (2*(n:ℝ)) →
      let ν := section9RevealedLaw (criticalPoint d) Q₁ H₁ Q₃ H₃ F₁ F₃
      let E := orientedLatticePairs (section9FiniteMiddle i n)
      (∑ e ∈ E, ∑ f ∈ E, ν.real (section9OverlapPatternEvent .parallel L R Q₁ F₁ Q₃ F₃ A B e f)) ≤
        K*(n : ℝ)^((4 : ℝ)-(d : ℝ))*(A.card : ℝ)*(B.card : ℝ) := by
  obtain ⟨G,hG,green⟩ := criticalSupGreenUpper_of_asymptotics (by omega : 2 ≤ d) asymptotics
  obtain ⟨C,hC,hbound⟩ := section9_parallel_overlap_sum_kernel_bound hd hG.le green
  refine ⟨C/8^((4 : ℝ)-(d : ℝ)),div_nonneg hC (by positivity),?_⟩
  intro i n hn L R Q₁ H₁ F₁ Q₃ H₃ F₃ A B hH₁ hH₃ hpos hLQ₃ hRQ₁ hA hB ν E
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hdR : (4 : ℝ) ≤ d := by exact_mod_cast (by omega : 4 ≤ d)
  have hpoint (x : Vertex d) (hx : x ∈ A) (y : Vertex d) (hy : y ∈ B) :
      (max 1 (latticeDistance x y))^((4 : ℝ)-(d : ℝ)) ≤
        ((n : ℝ)/8)^((4 : ℝ)-(d : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos (by positivity)
      ((section9_end_cubes_collision_separation i n (hA hx) (hB hy)).trans (le_max_right _ _))
      (by linarith)
  have hroots : (∑ x ∈ A, ∑ y ∈ B, (max 1 (latticeDistance x y))^((4 : ℝ)-(d : ℝ))) ≤
      (A.card : ℝ)*(B.card : ℝ)*((n : ℝ)/8)^((4 : ℝ)-(d : ℝ)) := by
    calc
      _ ≤ ∑ _x ∈ A, ∑ _y ∈ B, ((n : ℝ)/8)^((4 : ℝ)-(d : ℝ)) :=
        Finset.sum_le_sum fun x hx => Finset.sum_le_sum fun y hy => hpoint x hx y hy
      _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul,mul_assoc]
  calc
    _ ≤ C*(∑ x ∈ A, ∑ y ∈ B, (max 1 (latticeDistance x y))^((4 : ℝ)-(d : ℝ))) :=
      hbound (section9FiniteMiddle i n) L R Q₁ H₁ F₁ Q₃ H₃ F₃ A B hH₁ hH₃ hpos hLQ₃ hRQ₁
    _ ≤ C*((A.card : ℝ)*(B.card : ℝ)*((n : ℝ)/8)^((4 : ℝ)-(d : ℝ))) :=
      mul_le_mul_of_nonneg_left hroots hC
    _ = _ := by rw [Real.div_rpow hnR.le (by norm_num : (0 : ℝ) ≤ 8)]; ring

end NearCritical
