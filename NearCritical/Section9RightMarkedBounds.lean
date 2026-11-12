module
public import NearCritical.Section9ReplacementMoment
public import NearCritical.Section9PivotalSwap

/-! Right-side marked envelopes, retaining actual conditional laws and candidate
orientations. These are the reflected inputs for right/right and mixed collisions. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory
open scoped Classical BigOperators

private theorem right_marked_sum_swap {d : ℕ} (E : Finset (Vertex d × Vertex d))
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

/-- The original right-marked pivotal sum has a right-domain bubble envelope.
The mass premise counts actual candidate heads, rather than tails. -/
theorem section9_conditioned_right_marked_pivot_sum_twoPoint_le {d : ℕ}
    (E : Finset (Vertex d × Vertex d)) (hswap : ∀ e ∈ E, e.swap ∈ E)
    (L R Q₁ H₁ F₁ Q₃ H₃ F₃ A B : Finset (Vertex d))
    (hH₁ : H₁ ⊆ Q₁) (hH₃ : H₃ ⊆ Q₃)
    (hpos : percolation d (criticalPoint d) (section9RevealEvent Q₁ H₁ Q₃ H₃ F₁ F₃) ≠ 0)
    (hLQ₃ : Disjoint L Q₃) (hRQ₁ : Disjoint R Q₁)
    (H M : ℝ) (hH : 0 ≤ H) (hM : 0 ≤ M)
    (hLeft : ∀ e ∈ E, (percolation d (criticalPoint d)).real
      (connectionToSetEvent (L : Set (Vertex d)) e.1 (A : Set (Vertex d))) ≤ H)
    (hMass : ∀ v ∈ R, ∑ e ∈ E, (percolation d (criticalPoint d)).real
      (connectionToSetEvent (R : Set (Vertex d)) e.2 {v}) ≤ M)
    (w : Vertex d) :
    let ν := section9RevealedLaw (criticalPoint d) Q₁ H₁ Q₃ H₃ F₁ F₃
    (∑ e ∈ E, ν.real {ω | sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ A B e ∧
      w ∈ sprinklingUnexploredCluster ω R Q₃ F₃ e.2}) ≤
      (H*M) * ∑ y ∈ B, ∑ v ∈ R,
        twoPoint d (criticalPoint d) y v * twoPoint d (criticalPoint d) w v := by
  intro ν
  have hpos' : percolation d (criticalPoint d) (section9RevealEvent Q₃ H₃ Q₁ H₁ F₃ F₁) ≠ 0 := by
    rwa [← section9RevealEvent_swap Q₁ H₁ Q₃ H₃ F₁ F₃]
  have hMass' (v : Vertex d) (hv : v ∈ R) : ∑ e ∈ E,
      (percolation d (criticalPoint d)).real
        (connectionToSetEvent (R : Set (Vertex d)) e.1 {v}) ≤ M := by
    calc
      _ = ∑ e ∈ E, (percolation d (criticalPoint d)).real
          (connectionToSetEvent (R : Set (Vertex d)) e.2 {v}) :=
        (right_marked_sum_swap E hswap (fun e => (percolation d (criticalPoint d)).real
          (connectionToSetEvent (R : Set (Vertex d)) e.1 {v}))).symm
      _ ≤ M := hMass v hv
  have hb := section9_conditioned_marked_pivot_sum_twoPoint_le E
    R L Q₃ H₃ F₃ Q₁ H₁ F₁ B A hH₃ hH₁ hpos' hRQ₁ hLQ₃ H M hH hM
    (fun e he => hLeft e.swap (hswap e he)) hMass' w
  dsimp only at hb
  rw [← section9RevealedLaw_swap (criticalPoint d) Q₁ H₁ Q₃ H₃ F₁ F₃] at hb
  let g := fun e : Vertex d × Vertex d => ν.real {ω |
    sprinklingPivotalPair ω R L Q₃ F₃ Q₁ F₁ B A e ∧
      w ∈ sprinklingUnexploredCluster ω R Q₃ F₃ e.1}
  calc
    _ = ∑ e ∈ E, g e.swap := by
      apply Finset.sum_congr rfl
      intro e _
      congr 1
      ext ω
      exact and_congr (sprinklingPivotalPair_swap_iff ω L R Q₁ F₁ Q₃ F₃ A B e) Iff.rfl
    _ = ∑ e ∈ E, g e := right_marked_sum_swap E hswap g
    _ ≤ _ := hb

/-- Replacement right-arm witness sums have the same envelope, without a
replacement pivotality assumption. -/
theorem section9_conditioned_right_marked_arm_sum_twoPoint_le {d : ℕ}
    (E : Finset (Vertex d × Vertex d)) (hswap : ∀ e ∈ E, e.swap ∈ E)
    (L R Q₁ H₁ F₁ Q₃ H₃ F₃ A B : Finset (Vertex d))
    (hH₁ : H₁ ⊆ Q₁) (hH₃ : H₃ ⊆ Q₃)
    (hpos : percolation d (criticalPoint d) (section9RevealEvent Q₁ H₁ Q₃ H₃ F₁ F₃) ≠ 0)
    (hLQ₃ : Disjoint L Q₃) (hRQ₁ : Disjoint R Q₁)
    (H M : ℝ) (hH : 0 ≤ H) (hM : 0 ≤ M)
    (hLeft : ∀ e ∈ E, (percolation d (criticalPoint d)).real
      (connectionToSetEvent (L : Set (Vertex d)) e.1 (A : Set (Vertex d))) ≤ H)
    (hMass : ∀ v ∈ R, ∑ e ∈ E, (percolation d (criticalPoint d)).real
      (connectionToSetEvent (R : Set (Vertex d)) e.2 {v}) ≤ M)
    (w : Vertex d) :
    let ν := section9RevealedLaw (criticalPoint d) Q₁ H₁ Q₃ H₃ F₁ F₃
    (∑ e ∈ E, ν.real (section9LeftMarkedArmOccurrence R L Q₃ F₃ Q₁ F₁ B A e.swap w)) ≤
      (H*M) * ∑ y ∈ B, ∑ v ∈ R,
        twoPoint d (criticalPoint d) y v * twoPoint d (criticalPoint d) w v := by
  intro ν
  have hpos' : percolation d (criticalPoint d) (section9RevealEvent Q₃ H₃ Q₁ H₁ F₃ F₁) ≠ 0 := by
    rwa [← section9RevealEvent_swap Q₁ H₁ Q₃ H₃ F₁ F₃]
  have hMass' (v : Vertex d) (hv : v ∈ R) : ∑ e ∈ E,
      (percolation d (criticalPoint d)).real
        (connectionToSetEvent (R : Set (Vertex d)) e.1 {v}) ≤ M := by
    calc
      _ = ∑ e ∈ E, (percolation d (criticalPoint d)).real
          (connectionToSetEvent (R : Set (Vertex d)) e.2 {v}) :=
        (right_marked_sum_swap E hswap (fun e => (percolation d (criticalPoint d)).real
          (connectionToSetEvent (R : Set (Vertex d)) e.1 {v}))).symm
      _ ≤ M := hMass v hv
  have hb := section9_conditioned_marked_arm_sum_twoPoint_le E
    R L Q₃ H₃ F₃ Q₁ H₁ F₁ B A hH₃ hH₁ hpos' hRQ₁ hLQ₃ H M hH hM
    (fun e he => hLeft e.swap (hswap e he)) hMass' w
  dsimp only at hb
  rw [← section9RevealedLaw_swap (criticalPoint d) Q₁ H₁ Q₃ H₃ F₁ F₃] at hb
  calc
    _ = ∑ e ∈ E, ν.real (section9LeftMarkedArmOccurrence R L Q₃ F₃ Q₁ F₁ B A e w) :=
      right_marked_sum_swap E hswap _
    _ ≤ _ := hb

/-- A single separated-arm constant works for target families contained in
either source end cube, or in their union. -/
theorem section9_middle_to_either_end_arm_le {d : ℕ} (hd : 2 ≤ d)
    (asymptotics : TwoPointAsymptotics d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (i : Fin d) (n : ℕ), 0 < n →
      ∀ (D T : Finset (Vertex d)) (v : Vertex d),
      v ∈ section9FiniteMiddle i n →
      T ⊆ section9FiniteEndCube i n 0 ∪ section9FiniteEndCube i n (2*(n:ℝ)) →
      (percolation d (criticalPoint d)).real
        (connectionToSetEvent (D : Set (Vertex d)) v (T : Set (Vertex d))) ≤
        (T.card : ℝ) * (C*((n : ℝ)/8)^((2 : ℝ)-(d : ℝ))) := by
  obtain ⟨C,hC,hdecay⟩ := section9TwoPoint_middle_end_bounds hd asymptotics
  refine ⟨C,hC,?_⟩
  intro i n hn D T v hv hT
  refine (connectionToSet_probability_le_twoPoint_sum (criticalPoint d) _ v T).trans ?_
  calc
    _ ≤ ∑ _z ∈ T, C*((n : ℝ)/8)^((2 : ℝ)-(d : ℝ)) :=
      Finset.sum_le_sum fun z hz => hdecay i n hn v hv z (Finset.mem_union.mp (hT hz))
    _ = _ := by rw [Finset.sum_const,nsmul_eq_mul]

end NearCritical
