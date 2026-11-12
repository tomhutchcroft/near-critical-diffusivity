module

public import NearCritical.Section10CoalescenceScale

/-! Convert the source coalescence count to bridge-intersection probabilities,
including the sum over a disjoint family of target roots. -/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open MeasureTheory Set
open scoped Classical

/-- The probability that two whole sprinkling bridges meet is bounded by
the expected number of coalescing ordered pairs of their roots. -/
theorem bridge_intersection_probability_le_coalescence {d : ℕ}
    (μ : Measure (Configuration d × Configuration d)) [IsFiniteMeasure μ]
    (E : Finset (Vertex d × Vertex d)) (L R Q₁ F₁ Q₃ F₃ X Y B : Finset (Vertex d)) :
    μ.real {ξη |
      (section9SprinklingCluster ξη.1 ξη.2 E L R Q₁ F₁ Q₃ F₃ X B ∩
        section9SprinklingCluster ξη.1 ξη.2 E L R Q₁ F₁ Q₃ F₃ Y B).Nonempty} ≤
      ∫ ξη, (section9CoalescenceCount ξη.1 ξη.2 E L R Q₁ F₁ Q₃ F₃ X Y B : ℝ) ∂μ := by
  let A (xy : Vertex d × Vertex d) := {ξη : Configuration d × Configuration d |
    (section9SprinklingCluster ξη.1 ξη.2 E L R Q₁ F₁ Q₃ F₃ {xy.1} B ∩
      section9SprinklingCluster ξη.1 ξη.2 E L R Q₁ F₁ Q₃ F₃ {xy.2} B).Nonempty}
  have hcover : {ξη : Configuration d × Configuration d |
      (section9SprinklingCluster ξη.1 ξη.2 E L R Q₁ F₁ Q₃ F₃ X B ∩
        section9SprinklingCluster ξη.1 ξη.2 E L R Q₁ F₁ Q₃ F₃ Y B).Nonempty} ⊆
      ⋃ xy ∈ X.product Y, A xy := by
    rintro ξη ⟨z, hz⟩
    obtain ⟨hzX, hzY⟩ := Finset.mem_inter.mp hz
    obtain ⟨x, hx, hxz⟩ := sprinklingCluster_exists_singleton_root ξη.1 ξη.2 E L R Q₁ F₁ Q₃ F₃ X B hzX
    obtain ⟨y, hy, hyz⟩ := sprinklingCluster_exists_singleton_root ξη.1 ξη.2 E L R Q₁ F₁ Q₃ F₃ Y B hzY
    exact Set.mem_iUnion.mpr ⟨(x, y), Set.mem_iUnion.mpr ⟨Finset.mem_product.mpr ⟨hx, hy⟩,
      ⟨z, Finset.mem_inter.mpr ⟨hxz, hyz⟩⟩⟩⟩
  calc
    _ ≤ μ.real (⋃ xy ∈ X.product Y, A xy) := measureReal_mono hcover (measure_ne_top _ _)
    _ ≤ ∑ xy ∈ X.product Y, μ.real (A xy) := measureReal_biUnion_finset_le _ _
    _ = _ := by
      rw [integral_section9_coalescence_count, Finset.product_eq_sprod, Finset.sum_product]

/-- Sum a row of bridge-intersection probabilities using a single
coalescence expectation on the disjoint union of the other root sets. -/
theorem bridge_intersection_probability_row_le {d : ℕ} {ι : Type*}
    (μ : Measure (Configuration d × Configuration d)) [IsFiniteMeasure μ]
    (E : Finset (Vertex d × Vertex d)) (L R Q₁ F₁ Q₃ F₃ X B : Finset (Vertex d))
    (S : Finset ι) (Y : ι → Finset (Vertex d)) (hY : (S : Set ι).PairwiseDisjoint Y) :
    (∑ j ∈ S, μ.real {ξη |
      (section9SprinklingCluster ξη.1 ξη.2 E L R Q₁ F₁ Q₃ F₃ X B ∩
        section9SprinklingCluster ξη.1 ξη.2 E L R Q₁ F₁ Q₃ F₃ (Y j) B).Nonempty}) ≤
      ∫ ξη, (section9CoalescenceCount ξη.1 ξη.2 E L R Q₁ F₁ Q₃ F₃ X (S.biUnion Y) B : ℝ) ∂μ := by
  calc
    _ ≤ ∑ j ∈ S, ∫ ξη, (section9CoalescenceCount ξη.1 ξη.2 E L R Q₁ F₁ Q₃ F₃ X (Y j) B : ℝ) ∂μ :=
      Finset.sum_le_sum fun j _ => bridge_intersection_probability_le_coalescence μ E L R Q₁ F₁ Q₃ F₃ X (Y j) B
    _ = _ := by
      simp_rw [integral_section9_coalescence_count μ E L R Q₁ F₁ Q₃ F₃]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.sum_biUnion hY]

/-- The separated part of (H3), for the actual law conditioned on the heart clusters. -/
theorem bridge_intersection_probability_separated {d : ℕ} (hd : 5 ≤ d)
    (asymp : TwoPointAsymptotics d) (q₀ c : ℝ) (hc : 0 < c) (A₀ F₀ : ℝ) :
    ∃ K : ℝ, ∀ (i : Fin d) (n : ℕ), 0 < n →
      ∀ (q : unitInterval), (q : ℝ) ≤ q₀ * (n : ℝ)^(-2 : ℝ) →
      ∀ (L R Q₁ F₁ Q₃ F₃ B H₁ H₃ X Y : Finset (Vertex d)),
        H₁ ⊆ Q₁ → H₃ ⊆ Q₃ → Disjoint L Q₃ → Disjoint R Q₁ →
        percolation d (criticalPoint d) (section9RevealEvent Q₁ H₁ Q₃ H₃ F₁ F₃) ≠ 0 →
        L ⊆ centeredBox d (3*n) → R ⊆ centeredBox d (3*n) →
        B ⊆ section9FiniteEndCube i n (2*(n:ℝ)) →
        X ⊆ section9FiniteEndCube i n 0 → Y ⊆ section9FiniteEndCube i n 0 →
        (∀ x ∈ X, ∀ y ∈ Y, c * (n:ℝ) ≤ latticeDistance x y) →
        (X.card : ℝ) ≤ A₀ * (n:ℝ)^(2:ℝ) → (Y.card : ℝ) ≤ A₀ * (n:ℝ)^(2:ℝ) →
        (B.card : ℝ) ≤ F₀ * (n:ℝ)^((d:ℝ)-4) →
        let P := orientedLatticePairs (section9FiniteMiddle i n)
        let μ := (section9RevealedLaw (criticalPoint d) Q₁ H₁ Q₃ H₃ F₁ F₃).prod (percolation d q)
        μ.real {ξη |
          (section9SprinklingCluster ξη.1 ξη.2 P L R Q₁ F₁ Q₃ F₃ X B ∩
            section9SprinklingCluster ξη.1 ξη.2 P L R Q₁ F₁ Q₃ F₃ Y B).Nonempty} ≤
          K * (n:ℝ)^(6-(d:ℝ)) := by
  obtain ⟨C, hC⟩ := section9_coalescence_expectation_separated_upper hd asymp q₀ c hc
  refine ⟨max 0 C * F₀ * A₀ * A₀, ?_⟩
  intro i n hn q hq L R Q₁ F₁ Q₃ F₃ B H₁ H₃ X Y hH₁ hH₃ hLQ₃ hRQ₁
    hpos hL hR hB hX hY hsep hXc hYc hBc P μ
  letI := section9RevealedLaw_isProbability (criticalPoint d) Q₁ H₁ Q₃ H₃ F₁ F₃ hpos
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have hscale : (n:ℝ)^((d:ℝ)-4) * (n:ℝ)^(2:ℝ) * (n:ℝ)^(2:ℝ) *
      (n:ℝ)^(6-2*(d:ℝ)) = (n:ℝ)^(6-(d:ℝ)) := by
    simp only [← Real.rpow_add hn']
    congr 1
    ring
  refine (bridge_intersection_probability_le_coalescence μ P L R Q₁ F₁ Q₃ F₃ X Y B).trans ?_
  refine (hC i n hn q hq L R Q₁ F₁ Q₃ F₃ B H₁ H₃ X Y hH₁ hH₃ hLQ₃ hRQ₁
    hpos hL hR hB hX hY hsep).trans ?_
  calc
    _ ≤ max 0 C * (F₀ * (n:ℝ)^((d:ℝ)-4)) * (A₀ * (n:ℝ)^(2:ℝ)) *
        (A₀ * (n:ℝ)^(2:ℝ)) * (n:ℝ)^(6-2*(d:ℝ)) := by
      have hcoeff : C ≤ max 0 C := le_max_right 0 C
      have hX₀ := (Nat.cast_nonneg X.card).trans hXc
      have hB₀ := (Nat.cast_nonneg B.card).trans hBc
      gcongr <;> positivity
    _ = max 0 C * F₀ * A₀ * A₀ *
        ((n:ℝ)^((d:ℝ)-4) * (n:ℝ)^(2:ℝ) * (n:ℝ)^(2:ℝ) * (n:ℝ)^(6-2*(d:ℝ))) := by ring
    _ = _ := by rw [hscale]

/-- The row part of (H3), with the disjoint patches combined before using
the conditional regular coalescence estimate. -/
theorem bridge_intersection_probability_row_uniform {d : ℕ} {ι : Type*} (hd : 5 ≤ d)
    (asymp : TwoPointAsymptotics d) (q₀ : ℝ) (r : ℕ) (hr : 1 ≤ r) (δ A₀ F₀ : ℝ) :
    ∃ K : ℝ, ∀ (i : Fin d) (n : ℕ), 0 < n →
      ∀ (q : unitInterval), (q : ℝ) ≤ q₀ * (n : ℝ)^(-2 : ℝ) →
      ∀ (L R Q₁ F₁ Q₃ F₃ B H₁ H₃ X S boundary : Finset (Vertex d))
        (J : Finset ι) (Y : ι → Finset (Vertex d)), (J : Set ι).PairwiseDisjoint Y →
        H₁ ⊆ Q₁ → H₃ ⊆ Q₃ → Disjoint L Q₃ → Disjoint R Q₁ →
        percolation d (criticalPoint d) (section9RevealEvent Q₁ H₁ Q₃ H₃ F₁ F₃) ≠ 0 →
        L ⊆ centeredBox d (3*n) → R ⊆ centeredBox d (3*n) →
        B ⊆ section9FiniteEndCube i n (2*(n:ℝ)) →
        X ⊆ section9FiniteEndCube i n 0 → J.biUnion Y ⊆ section9FiniteEndCube i n 0 →
        (∀ x ∈ X, sourceRegularPoint F₁ S boundary r δ x) →
        (∀ y ∈ J.biUnion Y, sourceRegularPoint F₁ S boundary r δ y) →
        (X.card : ℝ) ≤ A₀ * (n:ℝ)^(2:ℝ) →
        ((J.biUnion Y).card : ℝ) ≤ F₀ * (n:ℝ)^((d:ℝ)-4) →
        (B.card : ℝ) ≤ F₀ * (n:ℝ)^((d:ℝ)-4) →
        let P := orientedLatticePairs (section9FiniteMiddle i n)
        let μ := (section9RevealedLaw (criticalPoint d) Q₁ H₁ Q₃ H₃ F₁ F₃).prod (percolation d q)
        (∑ j ∈ J, μ.real {ξη |
          (section9SprinklingCluster ξη.1 ξη.2 P L R Q₁ F₁ Q₃ F₃ X B ∩
            section9SprinklingCluster ξη.1 ξη.2 P L R Q₁ F₁ Q₃ F₃ (Y j) B).Nonempty}) ≤ K := by
  obtain ⟨C₁, C₂, hC⟩ := section9_coalescence_expectation_upper hd asymp q₀ r hr δ
  let D₁ := max 0 C₁
  let D₂ := max 0 C₂
  refine ⟨D₁ * F₀ * A₀ + D₂ * F₀^2 * A₀, ?_⟩
  intro i n hn q hq L R Q₁ F₁ Q₃ F₃ B H₁ H₃ X S boundary J Y hY hH₁ hH₃ hLQ₃ hRQ₁
    hpos hL hR hB hX hJ hXreg hJreg hXc hJc hBc P μ
  letI := section9RevealedLaw_isProbability (criticalPoint d) Q₁ H₁ Q₃ H₃ F₁ F₃ hpos
  refine (bridge_intersection_probability_row_le μ P L R Q₁ F₁ Q₃ F₃ X B J Y hY).trans ?_
  refine (hC i n hn q hq L R Q₁ F₁ Q₃ F₃ B H₁ H₃ X (J.biUnion Y) S boundary
    hH₁ hH₃ hLQ₃ hRQ₁ hpos hL hR hB hX hJ hXreg hJreg).trans ?_
  have hscale := bridge_coalescence_scale_le (d := d) (by exact_mod_cast hn)
    (Nat.cast_nonneg X.card) (Nat.cast_nonneg (J.biUnion Y).card) (Nat.cast_nonneg B.card)
    (le_max_left 0 C₁) (le_max_left 0 C₂) hXc hJc hBc
  refine le_trans ?_ hscale
  rw [Nat.cast_min]
  calc
    _ ≤ D₁ * (B.card : ℝ) * min (X.card : ℝ) ((J.biUnion Y).card : ℝ) *
        (n:ℝ)^((2:ℝ)-(d:ℝ)) +
        D₂ * (B.card : ℝ) * (X.card : ℝ) * ((J.biUnion Y).card : ℝ) *
          (n:ℝ)^(6-2*(d:ℝ)) := by
      gcongr <;> exact le_max_right _ _
    _ = _ := by ring

/-- The representative can depend on the tube. The union bound ranges over
all possible representatives in the two nests, as in Step 4 of the pair estimate. -/
theorem bridge_intersection_probability_nests_le {d : ℕ} {ι ι' : Type*}
    (μ : Measure (Configuration d × Configuration d)) [IsFiniteMeasure μ]
    (E : Finset (Vertex d × Vertex d)) (L R Q₁ F₁ Q₃ F₃ B : Finset (Vertex d))
    (J : Finset ι) (J' : Finset ι') (X : ι → Finset (Vertex d)) (Y : ι' → Finset (Vertex d))
    (k : ℝ)
    (hpair : ∀ x ∈ J, ∀ y ∈ J', μ.real {ξη |
      (section9SprinklingCluster ξη.1 ξη.2 E L R Q₁ F₁ Q₃ F₃ (X x) B ∩
        section9SprinklingCluster ξη.1 ξη.2 E L R Q₁ F₁ Q₃ F₃ (Y y) B).Nonempty} ≤ k) :
    μ.real {ξη | ∃ x ∈ J, ∃ y ∈ J',
      (section9SprinklingCluster ξη.1 ξη.2 E L R Q₁ F₁ Q₃ F₃ (X x) B ∩
        section9SprinklingCluster ξη.1 ξη.2 E L R Q₁ F₁ Q₃ F₃ (Y y) B).Nonempty} ≤
      (J.card : ℝ) * (J'.card : ℝ) * k := by
  let A (xy : ι × ι') := {ξη : Configuration d × Configuration d |
    (section9SprinklingCluster ξη.1 ξη.2 E L R Q₁ F₁ Q₃ F₃ (X xy.1) B ∩
      section9SprinklingCluster ξη.1 ξη.2 E L R Q₁ F₁ Q₃ F₃ (Y xy.2) B).Nonempty}
  calc
    _ ≤ μ.real (⋃ xy ∈ J.product J', A xy) := by
      refine measureReal_mono ?_ (measure_ne_top _ _)
      rintro ξη ⟨x, hx, y, hy, hmeet⟩
      exact Set.mem_iUnion.mpr ⟨(x, y), Set.mem_iUnion.mpr ⟨Finset.mem_product.mpr ⟨hx, hy⟩, hmeet⟩⟩
    _ ≤ ∑ xy ∈ J.product J', μ.real (A xy) := measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _xy ∈ J.product J', k := by
      refine Finset.sum_le_sum fun xy hxy => ?_
      obtain ⟨hx, hy⟩ := Finset.mem_product.mp hxy
      exact hpair xy.1 hx xy.2 hy
    _ = _ := by simp [Finset.card_product, nsmul_eq_mul, Nat.cast_mul]

end NearCritical.Section10
