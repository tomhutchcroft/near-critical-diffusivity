module

public import NearCritical.Section9CoalescenceExpectation
public import NearCritical.Section9CoalescenceCaseOneRegular
public import NearCritical.Section9CoalescenceCaseTwoConditional
public import NearCritical.Section9CoalescenceConditionalScale

@[expose] public section
namespace NearCritical
open MeasureTheory
open scoped Classical

/-- Source coalescence expectation on the actual positive reveal atom. -/
theorem section9_coalescence_expectation_upper {d : ℕ} (hd : 5 ≤ d)
    (asymptotics : TwoPointAsymptotics d) (q₀ : ℝ) (r : ℕ) (hr : 1 ≤ r) (δ : ℝ) :
    ∃ C₁ C₂ : ℝ, ∀ (i : Fin d) (n : ℕ), 0 < n →
      ∀ (q : unitInterval), (q : ℝ) ≤ q₀ * (n : ℝ)^(-2 : ℝ) →
      ∀ (L R Q₁ F₁ Q₃ F₃ B H₁ H₃ X Y S boundary : Finset (Vertex d)),
        H₁ ⊆ Q₁ → H₃ ⊆ Q₃ → Disjoint L Q₃ → Disjoint R Q₁ →
        percolation d (criticalPoint d) (section9RevealEvent Q₁ H₁ Q₃ H₃ F₁ F₃) ≠ 0 →
        L ⊆ centeredBox d (3*n) → R ⊆ centeredBox d (3*n) →
        B ⊆ section9FiniteEndCube i n (2*(n:ℝ)) →
        X ⊆ section9FiniteEndCube i n 0 → Y ⊆ section9FiniteEndCube i n 0 →
        (∀ x ∈ X, sourceRegularPoint F₁ S boundary r δ x) →
        (∀ y ∈ Y, sourceRegularPoint F₁ S boundary r δ y) →
        let P := orientedLatticePairs (section9FiniteMiddle i n)
        let μ := (section9RevealedLaw (criticalPoint d) Q₁ H₁ Q₃ H₃ F₁ F₃).prod (percolation d q)
        (∫ ξη, (section9CoalescenceCount ξη.1 ξη.2 P L R Q₁ F₁ Q₃ F₃ X Y B : ℝ) ∂μ) ≤
          C₁ * (B.card : ℝ) * (min X.card Y.card : ℕ) * (n:ℝ)^((2:ℝ)-(d:ℝ)) +
          C₂ * (B.card : ℝ) * (X.card : ℝ) * (Y.card : ℝ) * (n:ℝ)^(6-2*(d:ℝ)) := by
  have hd2 : 2 ≤ d := (by decide : 2 ≤ 5).trans hd
  obtain ⟨C₁, h₁⟩ := section9_case_one_regular_sum_le hd asymptotics q₀ r hr δ
  obtain ⟨C₂, h₂⟩ := section9_case_two_revealed_event_scaled hd asymptotics q₀
  obtain ⟨C₃, h₃⟩ := section9_case_three_revealed_event_scaled hd2 asymptotics q₀
  refine ⟨C₁, 2 * C₂ + C₃, ?_⟩
  intro i n hn q hq L R Q₁ F₁ Q₃ F₃ B H₁ H₃ X Y S boundary hH₁ hH₃ hLQ₃ hRQ₁
    hpos hL hR hB hX hY hXreg hYreg P μ
  letI := section9RevealedLaw_isProbability (criticalPoint d) Q₁ H₁ Q₃ H₃ F₁ F₃ hpos
  have hBbox : B ⊆ centeredBox d (3*n) := fun z hz => (Finset.mem_filter.mp (hB hz)).1
  refine (integral_section9_coalescence_le_cases μ P L R Q₁ F₁ Q₃ F₃ X Y B).trans ?_
  refine (show _ ≤
      C₁ * (B.card : ℝ) * (min X.card Y.card : ℕ) * (n:ℝ)^((2:ℝ)-(d:ℝ)) +
      (C₂ * (B.card : ℝ) * (X.card : ℝ) * (Y.card : ℝ) * (n:ℝ)^(6-2*(d:ℝ)) +
      (C₂ * (B.card : ℝ) * (X.card : ℝ) * (Y.card : ℝ) * (n:ℝ)^(6-2*(d:ℝ)) +
        C₃ * (B.card : ℝ) * (X.card : ℝ) * (Y.card : ℝ) * (n:ℝ)^(6-2*(d:ℝ))))
      from ?_).trans_eq ?_
  · refine add_le_add
      (h₁ i n hn q hq L R Q₁ F₁ Q₃ F₃ B H₁ H₃ X Y S boundary hH₁ hH₃ hLQ₃ hRQ₁
        hpos hL hB hXreg hYreg)
      (add_le_add ?_ (add_le_add ?_ ?_))
    · refine (section9_sum_root_pairs_le X Y _
        ((B.card : ℝ) * C₂ * (n:ℝ)^(6-2*(d:ℝ))) ?_).trans_eq ?_
      · intro x hx y hy
        exact h₂ i n hn q hq L R Q₁ F₁ Q₃ F₃ B H₁ H₃ hH₁ hH₃ hLQ₃ hRQ₁ hpos hB
          x y (hX hx) (hY hy)
      · ring
    · refine (section9_sum_root_pairs_le Y X _
        ((B.card : ℝ) * C₂ * (n:ℝ)^(6-2*(d:ℝ))) ?_).trans_eq ?_
      · intro y hy x hx
        exact h₂ i n hn q hq L R Q₁ F₁ Q₃ F₃ B H₁ H₃ hH₁ hH₃ hLQ₃ hRQ₁ hpos hB
          y x (hY hy) (hX hx)
      · ring
    · refine (section9_sum_root_pairs_le X Y _
        ((B.card : ℝ) * C₃ * (n:ℝ)^(6-2*(d:ℝ))) ?_).trans_eq ?_
      · intro x hx y hy
        have hb := h₃ i n hn q hq L R Q₁ F₁ Q₃ F₃ B H₁ H₃ hH₁ hH₃ hLQ₃ hRQ₁ hpos hR hBbox
          x y (hX hx) (hY hy)
        have he : -(2:ℝ)*(d:ℝ)+6 = 6-2*(d:ℝ) := by ring
        simpa only [he, Set.mem_setOf_eq, P, μ] using hb
      · ring
  · ring

/-- The improved source expectation for macroscopically separated root families. -/
theorem section9_coalescence_expectation_separated_upper {d : ℕ} (hd : 5 ≤ d)
    (asymptotics : TwoPointAsymptotics d) (q₀ c : ℝ) (hc : 0 < c) :
    ∃ C : ℝ, ∀ (i : Fin d) (n : ℕ), 0 < n →
      ∀ (q : unitInterval), (q : ℝ) ≤ q₀ * (n : ℝ)^(-2 : ℝ) →
      ∀ (L R Q₁ F₁ Q₃ F₃ B H₁ H₃ X Y : Finset (Vertex d)),
        H₁ ⊆ Q₁ → H₃ ⊆ Q₃ → Disjoint L Q₃ → Disjoint R Q₁ →
        percolation d (criticalPoint d) (section9RevealEvent Q₁ H₁ Q₃ H₃ F₁ F₃) ≠ 0 →
        L ⊆ centeredBox d (3*n) → R ⊆ centeredBox d (3*n) →
        B ⊆ section9FiniteEndCube i n (2*(n:ℝ)) →
        X ⊆ section9FiniteEndCube i n 0 → Y ⊆ section9FiniteEndCube i n 0 →
        (∀ x ∈ X, ∀ y ∈ Y, c * (n:ℝ) ≤ latticeDistance x y) →
        let P := orientedLatticePairs (section9FiniteMiddle i n)
        let μ := (section9RevealedLaw (criticalPoint d) Q₁ H₁ Q₃ H₃ F₁ F₃).prod (percolation d q)
        (∫ ξη, (section9CoalescenceCount ξη.1 ξη.2 P L R Q₁ F₁ Q₃ F₃ X Y B : ℝ) ∂μ) ≤
          C * (B.card : ℝ) * (X.card : ℝ) * (Y.card : ℝ) * (n:ℝ)^(6-2*(d:ℝ)) := by
  have hd2 : 2 ≤ d := (by decide : 2 ≤ 5).trans hd
  obtain ⟨C₁, h₁⟩ := section9_case_one_separated_sum_le hd asymptotics q₀ c hc
  obtain ⟨C₂, h₂⟩ := section9_case_two_revealed_event_scaled hd asymptotics q₀
  obtain ⟨C₃, h₃⟩ := section9_case_three_revealed_event_scaled hd2 asymptotics q₀
  refine ⟨C₁ + 2 * C₂ + C₃, ?_⟩
  intro i n hn q hq L R Q₁ F₁ Q₃ F₃ B H₁ H₃ X Y hH₁ hH₃ hLQ₃ hRQ₁
    hpos hL hR hB hX hY hsep P μ
  letI := section9RevealedLaw_isProbability (criticalPoint d) Q₁ H₁ Q₃ H₃ F₁ F₃ hpos
  have hBbox : B ⊆ centeredBox d (3*n) := fun z hz => (Finset.mem_filter.mp (hB hz)).1
  refine (integral_section9_coalescence_le_cases μ P L R Q₁ F₁ Q₃ F₃ X Y B).trans ?_
  refine (show _ ≤
      C₁ * (B.card : ℝ) * (X.card : ℝ) * (Y.card : ℝ) * (n:ℝ)^(6-2*(d:ℝ)) +
      (C₂ * (B.card : ℝ) * (X.card : ℝ) * (Y.card : ℝ) * (n:ℝ)^(6-2*(d:ℝ)) +
      (C₂ * (B.card : ℝ) * (X.card : ℝ) * (Y.card : ℝ) * (n:ℝ)^(6-2*(d:ℝ)) +
        C₃ * (B.card : ℝ) * (X.card : ℝ) * (Y.card : ℝ) * (n:ℝ)^(6-2*(d:ℝ))))
      from ?_).trans_eq ?_
  · refine add_le_add
      (h₁ i n hn q hq L R Q₁ F₁ Q₃ F₃ B H₁ H₃ X Y hH₁ hH₃ hLQ₃ hRQ₁
        hpos hL hB hsep)
      (add_le_add ?_ (add_le_add ?_ ?_))
    · refine (section9_sum_root_pairs_le X Y _
        ((B.card : ℝ) * C₂ * (n:ℝ)^(6-2*(d:ℝ))) ?_).trans_eq ?_
      · intro x hx y hy
        exact h₂ i n hn q hq L R Q₁ F₁ Q₃ F₃ B H₁ H₃ hH₁ hH₃ hLQ₃ hRQ₁ hpos hB
          x y (hX hx) (hY hy)
      · ring
    · refine (section9_sum_root_pairs_le Y X _
        ((B.card : ℝ) * C₂ * (n:ℝ)^(6-2*(d:ℝ))) ?_).trans_eq ?_
      · intro y hy x hx
        exact h₂ i n hn q hq L R Q₁ F₁ Q₃ F₃ B H₁ H₃ hH₁ hH₃ hLQ₃ hRQ₁ hpos hB
          y x (hY hy) (hX hx)
      · ring
    · refine (section9_sum_root_pairs_le X Y _
        ((B.card : ℝ) * C₃ * (n:ℝ)^(6-2*(d:ℝ))) ?_).trans_eq ?_
      · intro x hx y hy
        have hb := h₃ i n hn q hq L R Q₁ F₁ Q₃ F₃ B H₁ H₃ hH₁ hH₃ hLQ₃ hRQ₁ hpos hR hBbox
          x y (hX hx) (hY hy)
        have he : -(2:ℝ)*(d:ℝ)+6 = 6-2*(d:ℝ) := by ring
        simpa only [he, Set.mem_setOf_eq, P, μ] using hb
      · ring
  · ring

end NearCritical
