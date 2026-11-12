module

public import NearCritical.Section9MeanUpperScale
public import NearCritical.Section9CoalescenceOpenedSum
public import NearCritical.Section9PhysicalBond

/-! Section 10 (H1) on the actual opened pivotal event. -/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open MeasureTheory Set
open scoped Classical

/-- A target hit requires at least one critical pivotal pair with an
independently open sprinkling bond. -/
theorem offspring_probability_le_sprinkled_mean {d : ℕ}
    (μ : Measure (Configuration d)) [IsFiniteMeasure μ] (q : unitInterval)
    (P : Finset (Vertex d × Vertex d)) (L R Q₁ F₁ Q₃ F₃ A B : Finset (Vertex d))
    (bond : (Vertex d × Vertex d) → Bond d)
    (hbond : ∀ e ∈ P, s((bond e).1, bondTip (bond e)) = s(e.1, e.2)) :
    (μ.prod (percolation d q)).real {ξη |
      (sprinkledPivotalPairs ξη.1 ξη.2 P L R Q₁ F₁ Q₃ F₃ A B).Nonempty} ≤
      section9PivotalMean μ P L R Q₁ F₁ Q₃ F₃ A B * (q : ℝ) := by
  let F (e : Vertex d × Vertex d) :=
    {ω : Configuration d | sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ A B e} ×ˢ
      {η : Configuration d | η (bond e) = true}
  have hcover : {ξη : Configuration d × Configuration d |
      (sprinkledPivotalPairs ξη.1 ξη.2 P L R Q₁ F₁ Q₃ F₃ A B).Nonempty} ⊆ ⋃ e ∈ P, F e := by
    rintro ⟨ω, η⟩ ⟨e, he⟩
    obtain ⟨he₀, hopen⟩ := Finset.mem_filter.mp he
    obtain ⟨heP, hpivot⟩ := Finset.mem_filter.mp he₀
    exact Set.mem_iUnion.mpr ⟨e, Set.mem_iUnion.mpr ⟨heP,
      ⟨hpivot, section9_bond_open_of_adj (hbond e heP) hopen⟩⟩⟩
  calc
    _ ≤ (μ.prod (percolation d q)).real (⋃ e ∈ P, F e) :=
      measureReal_mono hcover (measure_ne_top _ _)
    _ ≤ ∑ e ∈ P, (μ.prod (percolation d q)).real (F e) :=
      measureReal_biUnion_finset_le P F
    _ = _ := by
      unfold section9PivotalMean
      rw [integral_section9PivotalCount, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro e _
      simp only [F, Measure.real, Measure.prod_prod, ENNReal.toReal_mul,
        percolation_open_bond, ENNReal.toReal_ofReal q.property.1]

/-- For source-size patches on the two opposite end cubes, the conditional
probability of hitting one target cluster has scale n^(6-d). -/
theorem offspring_probability_upper_scale {d : ℕ} (hd : 2 ≤ d)
    (asymp : TwoPointAsymptotics d) (q₀ A₀ : ℝ) :
    ∃ K : ℝ, ∀ (i : Fin d) (n : ℕ), 0 < n →
      ∀ (q : unitInterval), (q : ℝ) ≤ q₀ * (n:ℝ)^(-2:ℝ) →
      ∀ (H₁ H₃ F₁ F₃ A B : Finset (Vertex d)),
      let Q₁ := section9FiniteEndCube i n 0
      let Q₃ := section9FiniteEndCube i n (2*(n:ℝ))
      H₁ ⊆ Q₁ → H₃ ⊆ Q₃ → A ⊆ Q₁ → B ⊆ Q₃ →
      percolation d (criticalPoint d) (section9RevealEvent Q₁ H₁ Q₃ H₃ F₁ F₃) ≠ 0 →
      (A.card : ℝ) ≤ A₀ * (n:ℝ)^(2:ℝ) → (B.card : ℝ) ≤ A₀ * (n:ℝ)^(2:ℝ) →
      let L := section9FiniteTube i n (-(5:ℝ)/8) (3/8)
      let R := section9FiniteTube i n (-(3:ℝ)/8) (5/8)
      let P := orientedLatticePairs (section9FiniteMiddle i n)
      let μ := (section9RevealedLaw (criticalPoint d) Q₁ H₁ Q₃ H₃ F₁ F₃).prod (percolation d q)
      μ.real {ξη | (sprinkledPivotalPairs ξη.1 ξη.2 P L R Q₁ F₁ Q₃ F₃ A B).Nonempty} ≤
        K * (n:ℝ)^(6-(d:ℝ)) := by
  obtain ⟨D, hD, hmean⟩ := section9ConditionalMean_upper_scale hd asymp
  refine ⟨D * A₀ * A₀ * q₀, ?_⟩
  intro i n hn q hq H₁ H₃ F₁ F₃ A B Q₁ Q₃ hH₁ hH₃ hA hB hpos hAc hBc L R P μ
  let ν := section9RevealedLaw (criticalPoint d) Q₁ H₁ Q₃ H₃ F₁ F₃
  letI : IsProbabilityMeasure ν := section9RevealedLaw_isProbability (criticalPoint d) Q₁ H₁ Q₃ H₃ F₁ F₃ hpos
  obtain ⟨bond, hbond⟩ := section9_middle_candidate_bond_map i n
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have hscale : (n:ℝ)^(4-(d:ℝ)) * (n:ℝ)^(2:ℝ) * (n:ℝ)^(2:ℝ) *
      (n:ℝ)^(-2:ℝ) = (n:ℝ)^(6-(d:ℝ)) := by
    simp only [← Real.rpow_add hn']
    congr 1
    ring
  calc
    _ ≤ section9PivotalMean ν P L R Q₁ F₁ Q₃ F₃ A B * (q : ℝ) :=
      offspring_probability_le_sprinkled_mean ν q P L R Q₁ F₁ Q₃ F₃ A B bond hbond
    _ ≤ (D * (n:ℝ)^(4-(d:ℝ)) * (A.card:ℝ) * (B.card:ℝ)) * (q : ℝ) :=
      mul_le_mul_of_nonneg_right (hmean i n hn H₁ H₃ F₁ F₃ A B hH₁ hH₃ hA hB hpos) q.property.1
    _ ≤ (D * (n:ℝ)^(4-(d:ℝ)) * (A₀ * (n:ℝ)^(2:ℝ)) * (A₀ * (n:ℝ)^(2:ℝ))) *
        (q₀ * (n:ℝ)^(-2:ℝ)) := by
      have hA₀ := (Nat.cast_nonneg A.card).trans hAc
      have hB₀ := (Nat.cast_nonneg B.card).trans hBc
      have hDpow : 0 ≤ D * (n:ℝ)^(4-(d:ℝ)) := mul_nonneg hD.le (Real.rpow_nonneg hn'.le _)
      refine mul_le_mul ?_ hq q.property.1 (mul_nonneg (mul_nonneg hDpow hA₀) hB₀)
      exact mul_le_mul (mul_le_mul_of_nonneg_left hAc hDpow) hBc
        (Nat.cast_nonneg B.card) (mul_nonneg hDpow hA₀)
    _ = D * A₀ * A₀ * q₀ *
        ((n:ℝ)^(4-(d:ℝ)) * (n:ℝ)^(2:ℝ) * (n:ℝ)^(2:ℝ) * (n:ℝ)^(-2:ℝ)) := by ring
    _ = _ := by rw [hscale]

end NearCritical.Section10
