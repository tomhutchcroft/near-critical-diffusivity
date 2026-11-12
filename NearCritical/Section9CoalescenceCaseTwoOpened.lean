module

public import NearCritical.Section9CoalescenceCaseTwoFinite
public import NearCritical.Section9CoalescenceSingleOpening
public import NearCritical.Section9CoalescenceCaseThree

@[expose] public section
namespace NearCritical
open MeasureTheory
open scoped Classical

/-- The Case 2 bound after the single independent opening. -/
theorem section9_case_two_opened_sum_le {d : ℕ} (hd : 5 ≤ d)
    (asymptotics : TwoPointAsymptotics d) :
    ∃ C G : ℝ, 0 < C ∧ 0 < G ∧
      ∀ (i : Fin d) (n : ℕ), 0 < n →
      ∀ (L R Q₁ F₁ Q₃ F₃ B : Finset (Vertex d)) (x y : Vertex d),
      x ∈ section9FiniteEndCube i n 0 → y ∈ section9FiniteEndCube i n 0 →
      B ⊆ section9FiniteEndCube i n (2*(n:ℝ)) →
      ∀ (q : unitInterval) (bond : (Vertex d × Vertex d) → Bond d),
      let P := orientedLatticePairs (section9FiniteMiddle i n)
      let A := fun e : Vertex d × Vertex d => {ω : Configuration d |
        ∃ f : Vertex d × Vertex d,
          sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ {x} B e ∧
          sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ {y} B f ∧
          Disjoint (sprinklingUnexploredCluster ω L Q₁ F₁ e.1)
            (sprinklingUnexploredCluster ω L Q₁ F₁ f.1) ∧
          (sprinklingUnexploredCluster ω R Q₃ F₃ e.2 ∩
            sprinklingUnexploredCluster ω L Q₁ F₁ f.1).Nonempty}
      (∑ e ∈ P, ((percolation d (criticalPoint d)).prod (percolation d q)).real
        (A e ×ˢ {η | η (bond e) = true})) ≤
        ((2 * (d : ℝ)) * (G * (1 + (2 * (d : ℝ) * 3^(d-1)) * ((6*n : ℕ)+1 : ℝ)^2))) *
          ((B.card : ℝ) * (C * ((n:ℝ)/8) ^ (6 - 2 * (d : ℝ)))) * (q : ℝ) := by
  obtain ⟨C, G, hC, hG, h⟩ := section9_case_two_finite_critical_sum_le hd asymptotics
  refine ⟨C, G, hC, hG, ?_⟩
  intro i n hn L R Q₁ F₁ Q₃ F₃ B x y hx hy hB q bond P A
  rw [section9_single_opening_sum q P A bond]
  exact mul_le_mul_of_nonneg_right (h i n hn L R Q₁ F₁ Q₃ F₃ B x y hx hy hB) q.property.1

/-- The single sprinkle cancels the quadratic pivot mass in Case 2. -/
theorem section9_case_two_opened_sum_scaled {d : ℕ} (hd : 5 ≤ d)
    (asymptotics : TwoPointAsymptotics d) (q₀ : ℝ) :
    ∃ K : ℝ,
      ∀ (i : Fin d) (n : ℕ), 0 < n →
      ∀ (L R Q₁ F₁ Q₃ F₃ B : Finset (Vertex d)) (x y : Vertex d),
      x ∈ section9FiniteEndCube i n 0 → y ∈ section9FiniteEndCube i n 0 →
      B ⊆ section9FiniteEndCube i n (2*(n:ℝ)) →
      ∀ (q : unitInterval), (q : ℝ) ≤ q₀ * (n : ℝ) ^ (-2 : ℝ) →
      ∀ (bond : (Vertex d × Vertex d) → Bond d),
      let P := orientedLatticePairs (section9FiniteMiddle i n)
      let A := fun e : Vertex d × Vertex d => {ω : Configuration d |
        ∃ f : Vertex d × Vertex d,
          sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ {x} B e ∧
          sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ {y} B f ∧
          Disjoint (sprinklingUnexploredCluster ω L Q₁ F₁ e.1)
            (sprinklingUnexploredCluster ω L Q₁ F₁ f.1) ∧
          (sprinklingUnexploredCluster ω R Q₃ F₃ e.2 ∩
            sprinklingUnexploredCluster ω L Q₁ F₁ f.1).Nonempty}
      (∑ e ∈ P, ((percolation d (criticalPoint d)).prod (percolation d q)).real
        (A e ×ˢ {η | η (bond e) = true})) ≤
        (B.card : ℝ) * K * (n : ℝ) ^ (6 - 2 * (d : ℝ)) := by
  obtain ⟨C, G, hC, hG, h⟩ := section9_case_two_opened_sum_le hd asymptotics
  let J : ℝ := 2 * (d : ℝ) * 3^(d-1)
  let M₀ := (2 * (d : ℝ)) * (G * (1 + 49 * J))
  refine ⟨M₀ * q₀ * (C / 8 ^ (6 - 2 * (d : ℝ))), ?_⟩
  intro i n hn L R Q₁ F₁ Q₃ F₃ B x y hx hy hB q hq bond P A
  let M := (2 * (d : ℝ)) * (G * (1 + J * ((6*n : ℕ)+1 : ℝ)^2))
  let H := (B.card : ℝ) * (C * ((n:ℝ)/8) ^ (6 - 2 * (d : ℝ)))
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have hM : M ≤ M₀ * (n : ℝ) ^ (2 : ℝ) := by
    rw [Real.rpow_two]
    dsimp only [M, M₀]
    have hJ : 0 ≤ J := by dsimp [J]; positivity
    have hD : 0 ≤ 2 * (d : ℝ) := by positivity
    simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_left (section9_case_three_mass_normalization hG.le hJ hn) hD
  have hMq := section9_single_opening_mass_le hn' (by dsimp [M, J]; positivity)
    q.property.1 hM hq
  calc
    _ ≤ M * H * (q : ℝ) := h i n hn L R Q₁ F₁ Q₃ F₃ B x y hx hy hB q bond
    _ = (M * (q : ℝ)) * H := by ring
    _ ≤ (M₀ * q₀) * H := mul_le_mul_of_nonneg_right hMq (by dsimp [H]; positivity)
    _ = _ := by
      dsimp only [H]
      rw [Real.div_rpow hn'.le (by norm_num : (0 : ℝ) ≤ 8)]
      ring

end NearCritical
