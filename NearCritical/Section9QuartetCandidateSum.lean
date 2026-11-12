module
public import NearCritical.Section9CrossOverlapCertificates
public import NearCritical.Section9RestrictedQuartetProbability
public import NearCritical.Section9CoalescenceCaseOneSum
public import NearCritical.Section9CollisionScale
public import NearCritical.Section8MixedConvolution

/-! Shared four-terminal candidate summation for the original cross cases. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory
open scoped Classical BigOperators

private theorem quartet_sum_pair_comm {α β γ δ : Type*}
    (S : Finset α) (T : Finset β) (U : Finset γ) (V : Finset δ)
    (F : α → β → γ → δ → ℝ) :
    (∑ a ∈ S, ∑ b ∈ T, ∑ c ∈ U, ∑ e ∈ V, F a b c e) =
      ∑ c ∈ U, ∑ e ∈ V, ∑ a ∈ S, ∑ b ∈ T, F a b c e := by
  calc
    _ = ∑ a ∈ S, ∑ c ∈ U, ∑ e ∈ V, ∑ b ∈ T, F a b c e := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro c _
      rw [Finset.sum_comm]
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro c _
      rw [Finset.sum_comm]

private theorem quartet_candidate_factor {d : ℕ} (E : Finset (Vertex d × Vertex d))
    (P : Vertex d → Vertex d → ℝ) (u v : Vertex d) (t : ℝ) :
    (∑ e ∈ E, ∑ f ∈ E, P e.1 u*P f.2 v*t) =
      (∑ e ∈ E, P e.1 u)*(∑ f ∈ E, P f.2 v)*t := by
  calc
    _ = ∑ e ∈ E, P e.1 u*((∑ f ∈ E, P f.2 v)*t) := by
      apply Finset.sum_congr rfl
      intro e _
      rw [Finset.sum_mul,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro f _
      ring
    _ = (∑ e ∈ E, P e.1 u)*((∑ f ∈ E, P f.2 v)*t) := (Finset.sum_mul _ _ _).symm
    _ = _ := by ring

private theorem quartet_candidate_tree_budget {d : ℕ}
    (E : Finset (Vertex d × Vertex d)) (D A B : Finset (Vertex d))
    (P : Vertex d → Vertex d → ℝ) (hP : ∀ a b, 0 ≤ P a b)
    (M N : ℝ) (hM : 0 ≤ M)
    (hTail : ∀ u ∈ D, ∑ e ∈ E, P e.1 u ≤ M)
    (hHead : ∀ u ∈ D, ∑ f ∈ E, P f.2 u ≤ M)
    (hFree : ∀ v ∈ D, ∑ u ∈ D, P u v ≤ N) :
    (∑ e ∈ E, ∑ f ∈ E, ∑ x ∈ A, ∑ y ∈ B,
      ((∑ u ∈ D, ∑ v ∈ D, P e.1 u*P f.2 u*P u v*P x v*P y v) +
       (∑ u ∈ D, ∑ v ∈ D, P e.1 u*P x u*P u v*P f.2 v*P y v) +
       (∑ u ∈ D, ∑ v ∈ D, P e.1 u*P y u*P u v*P f.2 v*P x v))) ≤
    M^2 * ∑ x ∈ A, ∑ y ∈ B,
      (N*(∑ v ∈ D, P x v*P y v) +
       (∑ u ∈ D, ∑ v ∈ D, P x u*P u v*P y v) +
       (∑ u ∈ D, ∑ v ∈ D, P y u*P u v*P x v)) := by
  let Near := fun (e f : Vertex d × Vertex d) (x y : Vertex d) => ∑ u ∈ D, ∑ v ∈ D,
    P e.1 u*P f.2 u*(P u v*P x v*P y v)
  let Chain := fun (e f : Vertex d × Vertex d) (x y : Vertex d) => ∑ u ∈ D, ∑ v ∈ D,
    P e.1 u*P f.2 v*(P u v*P x u*P y v)
  have hCand (u : Vertex d) (hu : u ∈ D) (v : Vertex d) (hv : v ∈ D)
      (t : ℝ) (ht : 0 ≤ t) :
      (∑ e ∈ E, ∑ f ∈ E, P e.1 u*P f.2 v*t) ≤ M^2*t := by
    rw [quartet_candidate_factor]
    apply mul_le_mul_of_nonneg_right _ ht
    simpa only [pow_two] using mul_le_mul (hTail u hu) (hHead v hv)
      (Finset.sum_nonneg fun f _ => hP f.2 v) hM
  have hNear (x y : Vertex d) : (∑ e ∈ E, ∑ f ∈ E, Near e f x y) ≤
      M^2*(N*(∑ v ∈ D, P x v*P y v)) := by
    calc
      _ = ∑ u ∈ D, ∑ v ∈ D, ∑ e ∈ E, ∑ f ∈ E,
          P e.1 u*P f.2 u*(P u v*P x v*P y v) :=
        quartet_sum_pair_comm E E D D _
      _ ≤ ∑ u ∈ D, ∑ v ∈ D, M^2*(P u v*P x v*P y v) :=
        Finset.sum_le_sum fun u hu => Finset.sum_le_sum fun v _ =>
          hCand u hu u hu _ (mul_nonneg (mul_nonneg (hP _ _) (hP _ _)) (hP _ _))
      _ = M^2*(∑ u ∈ D, ∑ v ∈ D, P u v*(P x v*P y v)) := by
        simp only [Finset.mul_sum,mul_assoc]
      _ = M^2*(∑ v ∈ D, (∑ u ∈ D, P u v)*(P x v*P y v)) := by
        congr 1
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro v _
        rw [Finset.sum_mul]
      _ ≤ M^2*(∑ v ∈ D, N*(P x v*P y v)) := by
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg M)
        exact Finset.sum_le_sum fun v hv =>
          mul_le_mul_of_nonneg_right (hFree v hv) (mul_nonneg (hP _ _) (hP _ _))
      _ = _ := by simp only [Finset.mul_sum]
  have hChain (x y : Vertex d) : (∑ e ∈ E, ∑ f ∈ E, Chain e f x y) ≤
      M^2*(∑ u ∈ D, ∑ v ∈ D, P x u*P u v*P y v) := by
    calc
      _ = ∑ u ∈ D, ∑ v ∈ D, ∑ e ∈ E, ∑ f ∈ E,
          P e.1 u*P f.2 v*(P u v*P x u*P y v) :=
        quartet_sum_pair_comm E E D D _
      _ ≤ ∑ u ∈ D, ∑ v ∈ D, M^2*(P u v*P x u*P y v) :=
        Finset.sum_le_sum fun u hu => Finset.sum_le_sum fun v hv =>
          hCand u hu v hv _ (mul_nonneg (mul_nonneg (hP _ _) (hP _ _)) (hP _ _))
      _ = _ := by
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro u _
        apply Finset.sum_congr rfl
        intro v _
        ring
  have hTerm (e f : Vertex d × Vertex d) (x y : Vertex d) :
      ((∑ u ∈ D, ∑ v ∈ D, P e.1 u*P f.2 u*P u v*P x v*P y v) +
       (∑ u ∈ D, ∑ v ∈ D, P e.1 u*P x u*P u v*P f.2 v*P y v) +
       (∑ u ∈ D, ∑ v ∈ D, P e.1 u*P y u*P u v*P f.2 v*P x v)) =
      Near e f x y+Chain e f x y+Chain e f y x := by
    dsimp only [Near,Chain]
    simp only [mul_assoc,mul_left_comm,mul_comm]
  calc
    _ = ∑ x ∈ A, ∑ y ∈ B, ∑ e ∈ E, ∑ f ∈ E,
        (Near e f x y+Chain e f x y+Chain e f y x) := by
      simp_rw [hTerm]
      exact quartet_sum_pair_comm E E A B _
    _ ≤ ∑ x ∈ A, ∑ y ∈ B,
        (M^2*(N*(∑ v ∈ D, P x v*P y v)) +
         M^2*(∑ u ∈ D, ∑ v ∈ D, P x u*P u v*P y v) +
         M^2*(∑ u ∈ D, ∑ v ∈ D, P y u*P u v*P x v)) := by
      apply Finset.sum_le_sum
      intro x _
      apply Finset.sum_le_sum
      intro y _
      simp only [Finset.sum_add_distrib]
      exact add_le_add (add_le_add (hNear x y) (hChain x y)) (hChain y x)
    _ = _ := by
      simp only [Finset.mul_sum,mul_add]

/-- The three actual quartet trees collapse to two candidate masses, one
free branch mass, and finite bubble/triple diagrams. -/
theorem section9_quartet_candidate_sum_budgets_le {d : ℕ}
    (E : Finset (Vertex d × Vertex d)) (D A B : Finset (Vertex d))
    (M N : ℝ) (hM : 0 ≤ M)
    (hTail : ∀ u ∈ D, ∑ e ∈ E, section9RightArm D e.1 u ≤ M)
    (hHead : ∀ u ∈ D, ∑ f ∈ E, section9RightArm D f.2 u ≤ M)
    (hFree : ∀ v ∈ D, ∑ u ∈ D, section9RightArm D u v ≤ N) :
    (∑ e ∈ E, ∑ f ∈ E, (percolation d (criticalPoint d)).real
      (section9CrossJointEvent D e.1 f.2 A B)) ≤
      M^2 * ∑ x ∈ A, ∑ y ∈ B,
        (N*(∑ v ∈ D, section9RightArm D x v*section9RightArm D y v) +
         (∑ u ∈ D, ∑ v ∈ D, section9RightArm D x u*section9RightArm D u v*section9RightArm D y v) +
         (∑ u ∈ D, ∑ v ∈ D, section9RightArm D y u*section9RightArm D u v*section9RightArm D x v)) := by
  let P := section9RightArm D
  have heach (e f : Vertex d × Vertex d) :
      (percolation d (criticalPoint d)).real (section9CrossJointEvent D e.1 f.2 A B) ≤
      ∑ x ∈ A, ∑ y ∈ B,
        ((∑ u ∈ D, ∑ v ∈ D, P e.1 u*P f.2 u*P u v*P x v*P y v) +
         (∑ u ∈ D, ∑ v ∈ D, P e.1 u*P x u*P u v*P f.2 v*P y v) +
         (∑ u ∈ D, ∑ v ∈ D, P e.1 u*P y u*P u v*P f.2 v*P x v)) := by
    have hb := restricted_quartet_target_probability_le (criticalPoint d) D A B e.1 f.2
    dsimp only at hb
    rw [Set.inter_assoc] at hb
    simpa only [section9CrossJointEvent,P,section9RightArm] using hb
  exact (Finset.sum_le_sum fun e _ => Finset.sum_le_sum fun f _ => heach e f).trans
    (quartet_candidate_tree_budget E D A B P (fun _ _ => measureReal_nonneg) M N hM hTail hHead hFree)

/-- A genuine finite triple convolution of restricted critical arms has
sixth-order decay, using the already proved finite Green convolutions. -/
theorem section9_finite_restricted_triple_le {d : ℕ} (hd : 7 ≤ d) {G : ℝ}
    (hG : 0 ≤ G) (green : CriticalSupGreenUpper d G)
    (D : Finset (Vertex d)) (x y : Vertex d) :
    ∑ u ∈ D, ∑ v ∈ D,
      section9RightArm D x u*section9RightArm D u v*section9RightArm D y v ≤
      (G^3*((4 : ℝ)^((d : ℝ)-2)*(2+19*(2*(d : ℝ)*3^(d-1)))) *
        ((4 : ℝ)^((d : ℝ)-2)*(82+91*(2*(d : ℝ)*3^(d-1))))) *
        (max 1 (latticeDistance x y))^((6 : ℝ)-(d : ℝ)) := by
  let P := twoPoint d (criticalPoint d)
  let Cg : ℝ := (4 : ℝ)^((d : ℝ)-2)*(2+19*(2*(d : ℝ)*3^(d-1)))
  let Cm : ℝ := (4 : ℝ)^((d : ℝ)-2)*(82+91*(2*(d : ℝ)*3^(d-1)))
  have hDom (a b : Vertex d) : section9RightArm D a b ≤ P a b := by
    simpa only [section9RightArm,Finset.coe_singleton,Finset.sum_singleton] using
      connectionToSet_probability_le_twoPoint_sum (criticalPoint d) (D : Set (Vertex d)) a {b}
  have hP (a b : Vertex d) : 0 ≤ P a b := measureReal_nonneg
  have hCg : 0 ≤ Cg := by dsimp [Cg]; positivity
  calc
    _ ≤ ∑ u ∈ D, ∑ v ∈ D, P x u*P v u*P y v := by
      apply Finset.sum_le_sum
      intro u _
      apply Finset.sum_le_sum
      intro v _
      have huv : section9RightArm D u v ≤ P v u :=
        (hDom u v).trans_eq (twoPoint_symm (criticalPoint d) u v)
      exact mul_le_mul (mul_le_mul (hDom x u) huv measureReal_nonneg (hP _ _))
        (hDom y v) measureReal_nonneg (mul_nonneg (hP _ _) (hP _ _))
    _ = ∑ v ∈ D, (∑ u ∈ D, P x u*P v u)*P y v := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro v _
      rw [Finset.sum_mul]
    _ ≤ ∑ v ∈ D,
        (G^2*(Cg*(max 1 (latticeDistance x v))^((4 : ℝ)-(d : ℝ)))) *
        (G*(max 1 (latticeDistance y v))^((2 : ℝ)-(d : ℝ))) := by
      apply Finset.sum_le_sum
      intro v _
      exact mul_le_mul (section9_finite_bubble_le (by omega) hG green D x v)
        (green y v) (hP _ _) (by positivity)
    _ = (G^3*Cg)*(∑ v ∈ D,
        (max 1 (latticeDistance x v))^((4 : ℝ)-(d : ℝ)) *
        (max 1 (latticeDistance y v))^((2 : ℝ)-(d : ℝ))) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v _
      ring
    _ ≤ (G^3*Cg)*(Cm*(max 1 (latticeDistance x y))^((6 : ℝ)-(d : ℝ))) := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg (pow_nonneg hG _) hCg)
      simpa only [Nat.cast_one] using Section8.truncated_fourth_green_convolution_le
        hd 1 (by decide) D x y
    _ = _ := by dsimp [Cg,Cm]; ring

private theorem quartet_source_scale {d : ℕ} {n M N M₀ N₀ C₄ C₆ : ℝ}
    (hn : 0 < n) (hM : 0 ≤ M) (hN : 0 ≤ N)
    (hM₀ : 0 ≤ M₀) (hN₀ : 0 ≤ N₀) (hC₄ : 0 ≤ C₄) (hC₆ : 0 ≤ C₆)
    (hMs : M ≤ M₀*n^(2 : ℝ)) (hNs : N ≤ N₀*n^(2 : ℝ)) :
    M^2*(N*C₄*(n/8)^((4 : ℝ)-(d : ℝ)) +
      2*C₆*(n/8)^((6 : ℝ)-(d : ℝ))) ≤
    (M₀^2*N₀*C₄/8^((4 : ℝ)-(d : ℝ)) +
      2*M₀^2*C₆/8^((6 : ℝ)-(d : ℝ)))*n^((10 : ℝ)-(d : ℝ)) := by
  have h4 : 0 ≤ (n/8)^((4 : ℝ)-(d : ℝ)) := Real.rpow_nonneg (by positivity) _
  have h6 : 0 ≤ (n/8)^((6 : ℝ)-(d : ℝ)) := Real.rpow_nonneg (by positivity) _
  have hsq : M^2 ≤ (M₀*n^(2 : ℝ))^2 :=
    pow_le_pow_left₀ hM hMs 2
  have he4 : (n^(2 : ℝ))^2*n^(2 : ℝ)*n^((4 : ℝ)-(d : ℝ)) =
      n^((10 : ℝ)-(d : ℝ)) := by
    rw [← Real.rpow_mul_natCast hn.le, ← Real.rpow_add hn, ← Real.rpow_add hn]
    congr 1
    ring
  have he6 : (n^(2 : ℝ))^2*n^((6 : ℝ)-(d : ℝ)) =
      n^((10 : ℝ)-(d : ℝ)) := by
    rw [← Real.rpow_mul_natCast hn.le, ← Real.rpow_add hn]
    congr 1
    ring
  calc
    _ ≤ (M₀*n^(2 : ℝ))^2 *
        ((N₀*n^(2 : ℝ))*C₄*(n/8)^((4 : ℝ)-(d : ℝ)) +
          2*C₆*(n/8)^((6 : ℝ)-(d : ℝ))) := by
      apply mul_le_mul hsq
        (add_le_add (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hNs hC₄) h4) le_rfl)
      · exact add_nonneg (mul_nonneg (mul_nonneg hN hC₄) h4)
          (mul_nonneg (mul_nonneg (by norm_num) hC₆) h6)
      · exact sq_nonneg _
    _ = (M₀^2*N₀*C₄/8^((4 : ℝ)-(d : ℝ)))*
          ((n^(2 : ℝ))^2*n^(2 : ℝ)*n^((4 : ℝ)-(d : ℝ))) +
        (2*M₀^2*C₆/8^((6 : ℝ)-(d : ℝ)))*
          ((n^(2 : ℝ))^2*n^((6 : ℝ)-(d : ℝ))) := by
      rw [Real.div_rpow hn.le (by norm_num : (0 : ℝ) ≤ 8),
        Real.div_rpow hn.le (by norm_num : (0 : ℝ) ≤ 8)]
      ring
    _ = _ := by rw [he4,he6]; ring

/-- Summing the actual four-terminal connection event over two middle
candidates costs n^(10-d), uniformly over every finite restricted domain
in the source box. No multipoint or convolution bound is assumed. -/
theorem section9_quartet_candidate_source_sum_bound {d : ℕ} (hd : 9 ≤ d)
    (asymptotics : TwoPointAsymptotics d) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (i : Fin d) (n : ℕ), 0 < n →
      ∀ (D A B : Finset (Vertex d)), D ⊆ centeredBox d (3*n) →
      A ⊆ section9FiniteEndCube i n 0 →
      B ⊆ section9FiniteEndCube i n (2*(n : ℝ)) →
      (∑ e ∈ orientedLatticePairs (section9FiniteMiddle i n),
        ∑ f ∈ orientedLatticePairs (section9FiniteMiddle i n),
          (percolation d (criticalPoint d)).real
            (section9CrossJointEvent D e.1 f.2 A B)) ≤
      K*(n : ℝ)^((10 : ℝ)-(d : ℝ))*(A.card : ℝ)*(B.card : ℝ) := by
  have hd2 : 2 ≤ d := by omega
  obtain ⟨G,hG,green⟩ := criticalSupGreenUpper_of_asymptotics hd2 asymptotics
  let J : ℝ := 2*(d : ℝ)*3^(d-1)
  let N₀ : ℝ := G*(1+49*J)
  let M₀ : ℝ := 2*(d : ℝ)*N₀
  let C₄ : ℝ := G^2*((4 : ℝ)^((d : ℝ)-2)*(2+19*J))
  let C₆ : ℝ := G^3*((4 : ℝ)^((d : ℝ)-2)*(2+19*J)) *
    ((4 : ℝ)^((d : ℝ)-2)*(82+91*J))
  let K : ℝ := M₀^2*N₀*C₄/8^((4 : ℝ)-(d : ℝ)) +
    2*M₀^2*C₆/8^((6 : ℝ)-(d : ℝ))
  have hN₀ : 0 ≤ N₀ := by dsimp [N₀,J]; positivity
  have hM₀ : 0 ≤ M₀ := mul_nonneg (by positivity) hN₀
  have hC₄ : 0 ≤ C₄ := by dsimp [C₄,J]; positivity
  have hC₆ : 0 ≤ C₆ := by dsimp [C₆,J]; positivity
  have hK : 0 ≤ K := by
    dsimp only [K]
    exact add_nonneg
      (div_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) hN₀) hC₄)
        (Real.rpow_nonneg (by norm_num) _))
      (div_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) hC₆)
        (Real.rpow_nonneg (by norm_num) _))
  refine ⟨K,hK,?_⟩
  intro i n hn D A B hD hA hB
  let E := orientedLatticePairs (section9FiniteMiddle i n)
  let N : ℝ := G*(1+J*((6*n : ℕ)+1 : ℝ)^2)
  let M : ℝ := 2*(d : ℝ)*N
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hN : 0 ≤ N := by dsimp [N,J]; positivity
  have hM : 0 ≤ M := mul_nonneg (by positivity) hN
  have hNs : N ≤ N₀*(n : ℝ)^(2 : ℝ) := by
    rw [Real.rpow_two]
    exact section9_case_three_mass_normalization (K := J) hG.le
      (by dsimp [J]; positivity) hn
  have hMs : M ≤ M₀*(n : ℝ)^(2 : ℝ) := by
    have hm := mul_le_mul_of_nonneg_left hNs (by positivity : 0 ≤ 2*(d : ℝ))
    simpa only [M,M₀,mul_assoc] using hm
  have hTail (u : Vertex d) (hu : u ∈ D) :
      ∑ e ∈ E, section9RightArm D e.1 u ≤ M :=
    section9_middle_tail_mass_le hd2 hG.le green i n D u (hD hu)
  have hHead (u : Vertex d) (hu : u ∈ D) :
      ∑ e ∈ E, section9RightArm D e.2 u ≤ M := by
    have hh := section9_middle_head_mass_le hd2 hG.le green i n D u (hD hu)
    simp_rw [section9RightArm_symm D u] at hh
    exact hh
  have hFree (v : Vertex d) (hv : v ∈ D) :
      ∑ u ∈ D, section9RightArm D u v ≤ N := by
    simp_rw [section9RightArm_symm D _ v]
    exact section9_restricted_arm_mass_le hd2 hG.le green (D : Set (Vertex d)) D v (6*n)
      (fun u hu => section9_distance_le_of_mem_centeredBox (hD hv) (hD hu))
  have hbudget := section9_quartet_candidate_sum_budgets_le E D A B M N hM hTail hHead hFree
  have hdR : (9 : ℝ) ≤ d := by exact_mod_cast hd
  have hk (q : ℝ) (hq : q ≤ 9) (x y : Vertex d)
      (hxy : (n : ℝ)/8 ≤ latticeDistance x y) :
      (max 1 (latticeDistance x y))^(q-(d : ℝ)) ≤
        ((n : ℝ)/8)^(q-(d : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos (by positivity)
      (hxy.trans (le_max_right _ _)) (by linarith)
  have hpoint (x : Vertex d) (hx : x ∈ A) (y : Vertex d) (hy : y ∈ B) :
      N*(∑ v ∈ D, section9RightArm D x v*section9RightArm D y v) +
      (∑ u ∈ D, ∑ v ∈ D, section9RightArm D x u*section9RightArm D u v*section9RightArm D y v) +
      (∑ u ∈ D, ∑ v ∈ D, section9RightArm D y u*section9RightArm D u v*section9RightArm D x v) ≤
      N*C₄*((n : ℝ)/8)^((4 : ℝ)-(d : ℝ)) +
        2*C₆*((n : ℝ)/8)^((6 : ℝ)-(d : ℝ)) := by
    have hxy := section9_end_cubes_collision_separation i n (hA hx) (hB hy)
    have hyx : (n : ℝ)/8 ≤ latticeDistance y x := by
      simpa only [latticeDistance_comm] using hxy
    have hb := section9_restricted_bubble_le (by omega : 5 ≤ d) hG.le green D x y
    have ht := section9_finite_restricted_triple_le (by omega : 7 ≤ d) hG.le green D x y
    have ht' := section9_finite_restricted_triple_le (by omega : 7 ≤ d) hG.le green D y x
    have hb' : (∑ v ∈ D, section9RightArm D x v*section9RightArm D y v) ≤
        C₄*((n : ℝ)/8)^((4 : ℝ)-(d : ℝ)) := by
      apply hb.trans
      simpa only [C₄,J,mul_assoc] using
        mul_le_mul_of_nonneg_left (hk 4 (by norm_num) x y hxy) hC₄
    have htxy : (∑ u ∈ D, ∑ v ∈ D,
        section9RightArm D x u*section9RightArm D u v*section9RightArm D y v) ≤
        C₆*((n : ℝ)/8)^((6 : ℝ)-(d : ℝ)) :=
      ht.trans (mul_le_mul_of_nonneg_left (hk 6 (by norm_num) x y hxy) hC₆)
    have htyx : (∑ u ∈ D, ∑ v ∈ D,
        section9RightArm D y u*section9RightArm D u v*section9RightArm D x v) ≤
        C₆*((n : ℝ)/8)^((6 : ℝ)-(d : ℝ)) :=
      ht'.trans (mul_le_mul_of_nonneg_left (hk 6 (by norm_num) y x hyx) hC₆)
    have hh := add_le_add (add_le_add (mul_le_mul_of_nonneg_left hb' hN) htxy) htyx
    nlinarith only [hh]
  have hscale := quartet_source_scale (d := d) hnR hM hN hM₀ hN₀ hC₄ hC₆ hMs hNs
  calc
    _ ≤ M^2*∑ x ∈ A, ∑ y ∈ B,
        (N*C₄*((n : ℝ)/8)^((4 : ℝ)-(d : ℝ)) +
          2*C₆*((n : ℝ)/8)^((6 : ℝ)-(d : ℝ))) :=
      hbudget.trans (mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum fun x hx => Finset.sum_le_sum fun y hy => hpoint x hx y hy)
        (sq_nonneg _))
    _ = (M^2*(N*C₄*((n : ℝ)/8)^((4 : ℝ)-(d : ℝ)) +
          2*C₆*((n : ℝ)/8)^((6 : ℝ)-(d : ℝ))))*(A.card : ℝ)*(B.card : ℝ) := by
      simp only [Finset.sum_const,nsmul_eq_mul]
      ring
    _ ≤ (K*(n : ℝ)^((10 : ℝ)-(d : ℝ)))*(A.card : ℝ)*(B.card : ℝ) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hscale (Nat.cast_nonneg _))
        (Nat.cast_nonneg _)
    _ = _ := by ring

end NearCritical
