module
public import NearCritical.Section9OverlapSameLeftSum
public import NearCritical.Section9RightMarkedBounds

/-! Source Case VI via literal side, reveal-law and candidate swaps. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory
open scoped Classical BigOperators

/-- Singleton-overlap source estimate for either-end target families with the actual conditioned event and all geometric
arm and mass budgets discharged. -/
theorem section9_same_left_either_end_source_sum_bound {d : ℕ} (hd : 9 ≤ d)
    (asymptotics : TwoPointAsymptotics d) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (i : Fin d) (n : ℕ), 0 < n →
      ∀ (L R Q₁ H₁ F₁ Q₃ H₃ F₃ A B : Finset (Vertex d)),
      H₁ ⊆ Q₁ → H₃ ⊆ Q₃ →
      percolation d (criticalPoint d) (section9RevealEvent Q₁ H₁ Q₃ H₃ F₁ F₃) ≠ 0 →
      Disjoint L Q₃ → Disjoint R Q₁ → L ⊆ centeredBox d (3*n) →
      A ⊆ section9FiniteEndCube i n 0 ∪ section9FiniteEndCube i n (2*(n:ℝ)) →
      B ⊆ section9FiniteEndCube i n 0 ∪ section9FiniteEndCube i n (2*(n:ℝ)) →
      let ν := section9RevealedLaw (criticalPoint d) Q₁ H₁ Q₃ H₃ F₁ F₃
      let E := orientedLatticePairs (section9FiniteMiddle i n)
      (∑ e ∈ E, ∑ f ∈ E, ν.real (section9SameLeftOnlyEvent L R Q₁ F₁ Q₃ F₃ A B e f)) ≤
        K*(n : ℝ)^((10 : ℝ)-2*(d : ℝ))*(A.card : ℝ)*(B.card : ℝ)^2 := by
  have hd2 : 2 ≤ d := by omega
  obtain ⟨C,hC,hArm⟩ := section9_middle_to_either_end_arm_le hd2 asymptotics
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
        ((Finset.mem_union.mp (hA hx)).elim
          (fun hc => (Finset.mem_filter.mp hc).1) (fun hc => (Finset.mem_filter.mp hc).1)) (hL hu))
  have hs := section9_same_left_only_sum_budgets_le E L R Q₁ H₁ F₁ Q₃ H₃ F₃ A B
    hH₁ hH₃ hpos hLQ₃ hRQ₁ H M N hH hM
    (fun e he => hArm i n hn R B e.2 ((mem_orientedLatticePairs _ _ _).mp he).2.1 hB)
    (fun u hu => section9_middle_tail_mass_le hd2 hG.le green i n L u (hL hu)) hRoot
  have hscale := section9_same_left_only_scale (d := d) (by exact_mod_cast hn)
    (Nat.cast_nonneg A.card) (Nat.cast_nonneg B.card) hC.le hM hN hMscale hNscale
  exact hs.trans hscale

private theorem overlap_candidate_sum_swap {d : ℕ} (E : Finset (Vertex d × Vertex d))
    (hswap : ∀ e ∈ E, e.swap ∈ E) (g : (Vertex d × Vertex d) → ℝ) :
    (∑ e ∈ E, g e.swap) = ∑ e ∈ E, g e := by
  apply Finset.sum_bij (fun e _ => e.swap)
  · exact hswap
  · intro a _ b _ hab
    exact congrArg Prod.swap hab
  · intro e he
    exact ⟨e.swap,hswap e he,rfl⟩
  · intro e _
    rfl

set_option maxHeartbeats 400000 in
/-- The exact original single-right pattern has the reflected source
bound, derived with actual reveal-law and ordered-candidate swaps. -/
theorem section9_single_right_pattern_source_sum_bound {d : ℕ} (hd : 9 ≤ d)
    (asymptotics : TwoPointAsymptotics d) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (i : Fin d) (n : ℕ), 0 < n →
      ∀ (L R Q₁ H₁ F₁ Q₃ H₃ F₃ A B : Finset (Vertex d)),
      H₁ ⊆ Q₁ → H₃ ⊆ Q₃ →
      percolation d (criticalPoint d) (section9RevealEvent Q₁ H₁ Q₃ H₃ F₁ F₃) ≠ 0 →
      Disjoint L Q₃ → Disjoint R Q₁ → R ⊆ centeredBox d (3*n) →
      A ⊆ section9FiniteEndCube i n 0 → B ⊆ section9FiniteEndCube i n (2*(n:ℝ)) →
      let ν := section9RevealedLaw (criticalPoint d) Q₁ H₁ Q₃ H₃ F₁ F₃
      let E := orientedLatticePairs (section9FiniteMiddle i n)
      (∑ e ∈ E, ∑ f ∈ E, ν.real (section9OverlapPatternEvent .singleRight L R Q₁ F₁ Q₃ F₃ A B e f)) ≤
        K*(n : ℝ)^((10 : ℝ)-2*(d : ℝ))*(A.card : ℝ)^2*(B.card : ℝ) := by
  obtain ⟨K,hK,hbound⟩ := section9_same_left_either_end_source_sum_bound hd asymptotics
  refine ⟨K,hK,?_⟩
  intro i n hn L R Q₁ H₁ F₁ Q₃ H₃ F₃ A B hH₁ hH₃ hpos hLQ₃ hRQ₁ hR hA hB ν E
  letI : IsProbabilityMeasure ν := section9RevealedLaw_isProbability (criticalPoint d)
    Q₁ H₁ Q₃ H₃ F₁ F₃ hpos
  have hpos' : percolation d (criticalPoint d) (section9RevealEvent Q₃ H₃ Q₁ H₁ F₃ F₁) ≠ 0 := by
    rwa [← section9RevealEvent_swap Q₁ H₁ Q₃ H₃ F₁ F₃]
  have hb := hbound i n hn R L Q₃ H₃ F₃ Q₁ H₁ F₁ B A hH₃ hH₁ hpos' hRQ₁ hLQ₃ hR
    (hB.trans Finset.subset_union_right) (hA.trans Finset.subset_union_left)
  dsimp only at hb
  rw [← section9RevealedLaw_swap (criticalPoint d) Q₁ H₁ Q₃ H₃ F₁ F₃] at hb
  let g := fun e f : Vertex d × Vertex d => ν.real
    (section9SameLeftOnlyEvent R L Q₃ F₃ Q₁ F₁ B A e f)
  have hswap : ∀ e ∈ E, e.swap ∈ E := fun e he =>
    (mem_orientedLatticePairs_swap_iff (section9FiniteMiddle i n) e).mpr he
  have hsub (e f : Vertex d × Vertex d) :
      section9OverlapPatternEvent .singleRight L R Q₁ F₁ Q₃ F₃ A B e f ⊆
        section9SameLeftOnlyEvent R L Q₃ F₃ Q₁ F₁ B A e.swap f.swap := by
    rintro ω ⟨he,hf,hLL,hLR,hRL,hRR⟩
    exact ⟨(sprinklingPivotalPair_swap_iff ω L R Q₁ F₁ Q₃ F₃ A B e).mp he,
      (sprinklingPivotalPair_swap_iff ω L R Q₁ F₁ Q₃ F₃ A B f).mp hf,hRR,hLL⟩
  calc
    _ ≤ ∑ e ∈ E, ∑ f ∈ E, g e.swap f.swap :=
      Finset.sum_le_sum fun e _ => Finset.sum_le_sum fun f _ =>
        measureReal_mono (hsub e f) (measure_ne_top _ _)
    _ = ∑ e ∈ E, ∑ f ∈ E, g e.swap f := by
      apply Finset.sum_congr rfl
      intro e _
      exact overlap_candidate_sum_swap E hswap (g e.swap)
    _ = ∑ e ∈ E, ∑ f ∈ E, g e f :=
      overlap_candidate_sum_swap E hswap (fun e => ∑ f ∈ E, g e f)
    _ ≤ K*(n : ℝ)^((10 : ℝ)-2*(d : ℝ))*(B.card : ℝ)*(A.card : ℝ)^2 := hb
    _ = _ := by ring

end NearCritical
