module
public import NearCritical.Section9OverlapSameLeft
public import NearCritical.Section9OverlapMatching
public import NearCritical.Section9SameSideScale

/-! Source Case I summation of actual singleton-overlap probabilities. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory
open scoped Classical BigOperators

/-- Actual conditioned singleton-overlap probabilities are summed using two
candidate-tail masses and one root mass. All quantitative budgets are explicit. -/
theorem section9_same_left_only_sum_budgets_le {d : ℕ}
    (E : Finset (Vertex d × Vertex d))
    (L R Q₁ H₁ F₁ Q₃ H₃ F₃ A B : Finset (Vertex d))
    (hH₁ : H₁ ⊆ Q₁) (hH₃ : H₃ ⊆ Q₃)
    (hpos : percolation d (criticalPoint d) (section9RevealEvent Q₁ H₁ Q₃ H₃ F₁ F₃) ≠ 0)
    (hLQ₃ : Disjoint L Q₃) (hRQ₁ : Disjoint R Q₁)
    (H M N : ℝ) (hH : 0 ≤ H) (hM : 0 ≤ M)
    (hRight : ∀ e ∈ E, (percolation d (criticalPoint d)).real
      (connectionToSetEvent (R : Set (Vertex d)) e.2 (B : Set (Vertex d))) ≤ H)
    (hMass : ∀ u ∈ L, ∑ e ∈ E, section9RightArm L e.1 u ≤ M)
    (hRoot : ∀ x ∈ A, ∑ u ∈ L, section9RightArm L x u ≤ N) :
    let ν := section9RevealedLaw (criticalPoint d) Q₁ H₁ Q₃ H₃ F₁ F₃
    (∑ e ∈ E, ∑ f ∈ E, ν.real (section9SameLeftOnlyEvent L R Q₁ F₁ Q₃ F₃ A B e f)) ≤
      (H*M)^2*N*(A.card : ℝ) := by
  intro ν
  let P := section9RightArm L
  let T := fun e f : Vertex d × Vertex d => ∑ x ∈ A, ∑ u ∈ L,
    P e.1 u * (P f.1 u * P x u)
  have hP (a b : Vertex d) : 0 ≤ P a b := measureReal_nonneg
  have hT (e f : Vertex d × Vertex d) : 0 ≤ T e f :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
      mul_nonneg (hP _ _) (mul_nonneg (hP _ _) (hP _ _))
  have heach (e : Vertex d × Vertex d) (he : e ∈ E) (f : Vertex d × Vertex d) (hf : f ∈ E) :
      ν.real (section9SameLeftOnlyEvent L R Q₁ F₁ Q₃ F₃ A B e f) ≤ H^2*T e f := by
    have hb := section9_conditioned_same_left_only_tree_bound (criticalPoint d)
      L R Q₁ H₁ F₁ Q₃ H₃ F₃ A B hH₁ hH₃ hpos hLQ₃ hRQ₁ e f
    dsimp only at hb
    have ht : (∑ x ∈ A, ∑ u ∈ L, P e.1 u * (P u f.1 * P x u)) = T e f := by
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro u _
      rw [show P u f.1 = P f.1 u from section9RightArm_symm L u f.1]
    have hb' : ν.real (section9SameLeftOnlyEvent L R Q₁ F₁ Q₃ F₃ A B e f) ≤
        (∑ x ∈ A, ∑ u ∈ L, P e.1 u * (P u f.1 * P x u)) *
          ((percolation d (criticalPoint d)).real (connectionToSetEvent (R : Set (Vertex d)) e.2 (B : Set (Vertex d))) *
           (percolation d (criticalPoint d)).real (connectionToSetEvent (R : Set (Vertex d)) f.2 (B : Set (Vertex d)))) := by
      simpa only [ν,P,section9RightArm] using hb
    rw [ht] at hb' 
    calc
      _ ≤ T e f *
          ((percolation d (criticalPoint d)).real (connectionToSetEvent (R : Set (Vertex d)) e.2 (B : Set (Vertex d))) *
           (percolation d (criticalPoint d)).real (connectionToSetEvent (R : Set (Vertex d)) f.2 (B : Set (Vertex d)))) := hb'
      _ ≤ T e f*(H*H) := mul_le_mul_of_nonneg_left
        (mul_le_mul (hRight e he) (hRight f hf) measureReal_nonneg hH) (hT e f)
      _ = _ := by ring
  have hfactor : (∑ e ∈ E, ∑ f ∈ E, T e f) =
      ∑ x ∈ A, ∑ u ∈ L, (∑ e ∈ E, P e.1 u)*(∑ f ∈ E, P f.1 u)*P x u := by
    calc
      _ = ∑ e ∈ E, ∑ x ∈ A, ∑ u ∈ L, ∑ f ∈ E,
          P e.1 u*(P f.1 u*P x u) := by
        apply Finset.sum_congr rfl
        intro e _
        dsimp only [T]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro x _
        rw [Finset.sum_comm]
      _ = ∑ x ∈ A, ∑ u ∈ L, ∑ e ∈ E, ∑ f ∈ E,
          P e.1 u*(P f.1 u*P x u) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro x _
        rw [Finset.sum_comm]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro x _
        apply Finset.sum_congr rfl
        intro u _
        calc
          _ = ∑ e ∈ E, P e.1 u*((∑ f ∈ E, P f.1 u)*P x u) := by
            apply Finset.sum_congr rfl
            intro e _
            rw [Finset.sum_mul,Finset.mul_sum]
          _ = (∑ e ∈ E, P e.1 u)*((∑ f ∈ E, P f.1 u)*P x u) :=
            (Finset.sum_mul _ _ _).symm
          _ = _ := by ring
  calc
    _ ≤ ∑ e ∈ E, ∑ f ∈ E, H^2*T e f :=
      Finset.sum_le_sum fun e he => Finset.sum_le_sum fun f hf => heach e he f hf
    _ = H^2*(∑ e ∈ E, ∑ f ∈ E, T e f) := by simp only [Finset.mul_sum]
    _ = H^2*(∑ x ∈ A, ∑ u ∈ L, (∑ e ∈ E, P e.1 u)*(∑ f ∈ E, P f.1 u)*P x u) := by rw [hfactor]
    _ ≤ H^2*(∑ x ∈ A, ∑ u ∈ L, M^2*P x u) := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg H)
      apply Finset.sum_le_sum
      intro x _
      apply Finset.sum_le_sum
      intro u hu
      apply mul_le_mul_of_nonneg_right _ (hP x u)
      simpa only [pow_two] using mul_le_mul (hMass u hu) (hMass u hu)
        (Finset.sum_nonneg fun e _ => hP e.1 u) hM
    _ = H^2*(M^2*(∑ x ∈ A, ∑ u ∈ L, P x u)) := by simp only [Finset.mul_sum]
    _ ≤ H^2*(M^2*((A.card : ℝ)*N)) := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg H)
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg M)
      simpa only [Finset.sum_const,nsmul_eq_mul] using
        Finset.sum_le_sum (fun x hx => hRoot x hx)
    _ = _ := by ring

/-- The additional root mass contributes n² on top of the already proved
same-side arm/mass scale, giving the source Case I exponent. -/
theorem section9_same_left_only_scale {d : ℕ} {n a b C M M₀ N N₀ : ℝ}
    (hn : 0 < n) (ha : 0 ≤ a) (hb : 0 ≤ b) (hC : 0 ≤ C) (hM : 0 ≤ M) (hN : 0 ≤ N)
    (hMass : M ≤ M₀*n^(2 : ℝ)) (hRoot : N ≤ N₀*n^(2 : ℝ)) :
    ((b*(C*(n/8)^((2 : ℝ)-(d : ℝ))))*M)^2*N*a ≤
      (((C/8^((2 : ℝ)-(d : ℝ)))*M₀)^2*N₀) * n^((10 : ℝ)-2*(d : ℝ))*a*b^2 := by
  have hs := section9_same_side_scale (d := d) hn hb hC hM hMass
  have hnp : 0 ≤ n^((8 : ℝ)-2*(d : ℝ)) := Real.rpow_nonneg hn.le _
  calc
    _ ≤ ((((C/8^((2 : ℝ)-(d : ℝ)))*M₀)^2 * n^((8 : ℝ)-2*(d : ℝ))*b^2) *
        (N₀*n^(2 : ℝ)))*a :=
      mul_le_mul_of_nonneg_right (mul_le_mul hs hRoot hN (mul_nonneg
        (mul_nonneg (sq_nonneg _) hnp) (sq_nonneg b))) ha
    _ = (((C/8^((2 : ℝ)-(d : ℝ)))*M₀)^2*N₀) *
        (n^((8 : ℝ)-2*(d : ℝ))*n^(2 : ℝ))*a*b^2 := by ring
    _ = _ := by
      have he : ((8 : ℝ)-2*(d : ℝ))+2 = (10 : ℝ)-2*(d : ℝ) := by ring
      rw [← Real.rpow_add hn,he]

/-- Source Case I with the actual conditioned event and all geometric
arm and mass budgets discharged. -/
theorem section9_same_left_only_source_sum_bound {d : ℕ} (hd : 9 ≤ d)
    (asymptotics : TwoPointAsymptotics d) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (i : Fin d) (n : ℕ), 0 < n →
      ∀ (L R Q₁ H₁ F₁ Q₃ H₃ F₃ A B : Finset (Vertex d)),
      H₁ ⊆ Q₁ → H₃ ⊆ Q₃ →
      percolation d (criticalPoint d) (section9RevealEvent Q₁ H₁ Q₃ H₃ F₁ F₃) ≠ 0 →
      Disjoint L Q₃ → Disjoint R Q₁ → L ⊆ centeredBox d (3*n) →
      A ⊆ section9FiniteEndCube i n 0 → B ⊆ section9FiniteEndCube i n (2*(n:ℝ)) →
      let ν := section9RevealedLaw (criticalPoint d) Q₁ H₁ Q₃ H₃ F₁ F₃
      let E := orientedLatticePairs (section9FiniteMiddle i n)
      (∑ e ∈ E, ∑ f ∈ E, ν.real (section9SameLeftOnlyEvent L R Q₁ F₁ Q₃ F₃ A B e f)) ≤
        K*(n : ℝ)^((10 : ℝ)-2*(d : ℝ))*(A.card : ℝ)*(B.card : ℝ)^2 := by
  have hd2 : 2 ≤ d := by omega
  obtain ⟨C,hC,hArm⟩ := section9_case_one_right_arm_le hd2 asymptotics
  obtain ⟨G,hG,green⟩ := criticalSupGreenUpper_of_asymptotics hd2 asymptotics
  let J : ℝ := 2*(d : ℝ)*3^(d-1)
  let N₀ : ℝ := G*(1+49*J)
  let M₀ : ℝ := (2*(d : ℝ))*N₀
  let K : ℝ := ((C/8^((2 : ℝ)-(d : ℝ)))*M₀)^2*N₀
  have hN₀ : 0 ≤ N₀ := by dsimp [N₀,J]; positivity
  refine ⟨K,mul_nonneg (sq_nonneg _) hN₀,?_⟩
  intro i n hn L R Q₁ H₁ F₁ Q₃ H₃ F₃ A B hH₁ hH₃ hpos hLQ₃ hRQ₁ hL hA hB ν E
  let H : ℝ := (B.card : ℝ)*(C*((n : ℝ)/8)^((2 : ℝ)-(d : ℝ)))
  let N : ℝ := G*(1+J*((6*n : ℕ)+1 : ℝ)^2)
  let M : ℝ := (2*(d : ℝ))*N
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hN : 0 ≤ N := by dsimp [N,J]; positivity
  have hM : 0 ≤ M := mul_nonneg (by positivity) hN
  have hNscale : N ≤ N₀*(n : ℝ)^(2 : ℝ) := by
    rw [Real.rpow_two]
    exact section9_case_three_mass_normalization (K := J) hG.le (by dsimp [J]; positivity) hn
  have hMscale : M ≤ M₀*(n : ℝ)^(2 : ℝ) := by
    have hm := mul_le_mul_of_nonneg_left hNscale (by positivity : 0 ≤ 2*(d : ℝ))
    simpa only [M,M₀,mul_assoc] using hm
  have hRoot (x : Vertex d) (hx : x ∈ A) : ∑ u ∈ L, section9RightArm L x u ≤ N :=
    section9_restricted_arm_mass_le hd2 hG.le green (L : Set (Vertex d)) L x (6*n)
      (fun u hu => section9_distance_le_of_mem_centeredBox
        (Finset.mem_filter.mp (hA hx)).1 (hL hu))
  have hs := section9_same_left_only_sum_budgets_le E L R Q₁ H₁ F₁ Q₃ H₃ F₃ A B
    hH₁ hH₃ hpos hLQ₃ hRQ₁ H M N hH hM
    (fun e he => hArm i n hn R B e.2 ((mem_orientedLatticePairs _ _ _).mp he).2.1 hB)
    (fun u hu => section9_middle_tail_mass_le hd2 hG.le green i n L u (hL hu)) hRoot
  have hscale := section9_same_left_only_scale (d := d) (by exact_mod_cast hn)
    (Nat.cast_nonneg A.card) (Nat.cast_nonneg B.card) hC.le hM hN hMscale hNscale
  exact hs.trans hscale

/-- The exact source single-left matrix pattern is a subevent of the
broader same-left/disjoint-right event just estimated. -/
theorem section9_single_left_pattern_source_sum_bound {d : ℕ} (hd : 9 ≤ d)
    (asymptotics : TwoPointAsymptotics d) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (i : Fin d) (n : ℕ), 0 < n →
      ∀ (L R Q₁ H₁ F₁ Q₃ H₃ F₃ A B : Finset (Vertex d)),
      H₁ ⊆ Q₁ → H₃ ⊆ Q₃ →
      percolation d (criticalPoint d) (section9RevealEvent Q₁ H₁ Q₃ H₃ F₁ F₃) ≠ 0 →
      Disjoint L Q₃ → Disjoint R Q₁ → L ⊆ centeredBox d (3*n) →
      A ⊆ section9FiniteEndCube i n 0 → B ⊆ section9FiniteEndCube i n (2*(n:ℝ)) →
      let ν := section9RevealedLaw (criticalPoint d) Q₁ H₁ Q₃ H₃ F₁ F₃
      let E := orientedLatticePairs (section9FiniteMiddle i n)
      (∑ e ∈ E, ∑ f ∈ E, ν.real (section9OverlapPatternEvent .singleLeft L R Q₁ F₁ Q₃ F₃ A B e f)) ≤
        K*(n : ℝ)^((10 : ℝ)-2*(d : ℝ))*(A.card : ℝ)*(B.card : ℝ)^2 := by
  obtain ⟨K,hK,hbound⟩ := section9_same_left_only_source_sum_bound hd asymptotics
  refine ⟨K,hK,?_⟩
  intro i n hn L R Q₁ H₁ F₁ Q₃ H₃ F₃ A B hH₁ hH₃ hpos hLQ₃ hRQ₁ hL hA hB ν E
  letI : IsProbabilityMeasure ν := section9RevealedLaw_isProbability (criticalPoint d)
    Q₁ H₁ Q₃ H₃ F₁ F₃ hpos
  have hsub (e f : Vertex d × Vertex d) :
      section9OverlapPatternEvent .singleLeft L R Q₁ F₁ Q₃ F₃ A B e f ⊆
        section9SameLeftOnlyEvent L R Q₁ F₁ Q₃ F₃ A B e f := by
    rintro ω ⟨he,hf,hLL,hLR,hRL,hRR⟩
    exact ⟨he,hf,hLL,hRR⟩
  calc
    _ ≤ ∑ e ∈ E, ∑ f ∈ E, ν.real (section9SameLeftOnlyEvent L R Q₁ F₁ Q₃ F₃ A B e f) :=
      Finset.sum_le_sum fun e _ => Finset.sum_le_sum fun f _ =>
        measureReal_mono (hsub e f) (measure_ne_top _ _)
    _ ≤ _ := hbound i n hn L R Q₁ H₁ F₁ Q₃ H₃ F₃ A B hH₁ hH₃ hpos hLQ₃ hRQ₁ hL hA hB

end NearCritical
