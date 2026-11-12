module

public import NearCritical.Section10DisjointOffspringScale

/-! Bounding the creation of a shared offspring on a cleaning step. -/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open MeasureTheory Set
open scoped Classical

/-- This event ranges over all possible representatives, so the chosen
representatives may themselves depend on the tube configuration. -/
theorem common_disjoint_offspring_probability_le {d : ℕ} {ι ι' τ : Type*}
    (μ : Measure (Configuration d × Configuration d)) [IsFiniteMeasure μ]
    (P : Finset (Vertex d × Vertex d)) (L R Q₁ F₁ Q₃ F₃ B : Finset (Vertex d))
    (J : Finset ι) (J' : Finset ι') (T : Finset τ)
    (X : ι → Finset (Vertex d)) (Y : ι' → Finset (Vertex d)) (Z : τ → Finset (Vertex d))
    {K : ℝ}
    (hK : ∀ x ∈ J, ∀ y ∈ J', ∀ z ∈ T, μ.real
      (disjointOffspringEvent P L R Q₁ F₁ Q₃ F₃ (X x) (Y y) (Z z) (Z z) B) ≤ K) :
    μ.real {ξη | ∃ x ∈ J, ∃ y ∈ J', ∃ z ∈ T,
      ξη ∈ disjointOffspringEvent P L R Q₁ F₁ Q₃ F₃ (X x) (Y y) (Z z) (Z z) B} ≤
      (J.card : ℝ) * (J'.card : ℝ) * (T.card : ℝ) * K := by
  let I := (J.product J').product T
  let F (u : (ι × ι') × τ) :=
    disjointOffspringEvent P L R Q₁ F₁ Q₃ F₃ (X u.1.1) (Y u.1.2) (Z u.2) (Z u.2) B
  have hcover : {ξη | ∃ x ∈ J, ∃ y ∈ J', ∃ z ∈ T,
      ξη ∈ disjointOffspringEvent P L R Q₁ F₁ Q₃ F₃ (X x) (Y y) (Z z) (Z z) B} ⊆
      ⋃ u ∈ I, F u := by
    rintro ξη ⟨x, hx, y, hy, z, hz, hf⟩
    exact Set.mem_iUnion.mpr ⟨((x, y), z), Set.mem_iUnion.mpr
      ⟨Finset.mem_product.mpr ⟨Finset.mem_product.mpr ⟨hx, hy⟩, hz⟩, hf⟩⟩
  calc
    _ ≤ μ.real (⋃ u ∈ I, F u) := measureReal_mono hcover (measure_ne_top _ _)
    _ ≤ ∑ u ∈ I, μ.real (F u) := measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _u ∈ I, K := by
      apply Finset.sum_le_sum
      intro u hu
      obtain ⟨hxy, hz⟩ := Finset.mem_product.mp hu
      obtain ⟨hx, hy⟩ := Finset.mem_product.mp hxy
      exact hK u.1.1 hx u.1.2 hy u.2 hz
    _ = _ := by simp [I, Finset.card_product, nsmul_eq_mul, Nat.cast_mul]

/-- The probability of a shared offspring on a step with disjoint bridges
is at most a constant times n^(6−d). The target family can be all typical
clusters of the next cube. -/
theorem common_disjoint_offspring_probability_upper_scale {d : ℕ} {ι ι' τ : Type*}
    (hd : 2 ≤ d) (asymp : TwoPointAsymptotics d) (q₀ A₀ C₀ : ℝ) (κ : ℕ) :
    ∃ D : ℝ, ∀ (i : Fin d) (n : ℕ), 0 < n →
      ∀ (q : unitInterval), (q : ℝ) ≤ q₀ * (n:ℝ)^(-2:ℝ) →
      ∀ (H₁ H₃ F₁ F₃ B : Finset (Vertex d)),
      let Q₁ := section9FiniteEndCube i n 0
      let Q₃ := section9FiniteEndCube i n (2*(n:ℝ))
      H₁ ⊆ Q₁ → H₃ ⊆ Q₃ → B ⊆ Q₃ →
      percolation d (criticalPoint d) (section9RevealEvent Q₁ H₁ Q₃ H₃ F₁ F₃) ≠ 0 →
      ∀ (J : Finset ι) (J' : Finset ι') (T : Finset τ)
        (X : ι → Finset (Vertex d)) (Y : ι' → Finset (Vertex d)) (Z : τ → Finset (Vertex d)),
      J.card ≤ κ → J'.card ≤ κ → (T.card:ℝ) ≤ C₀ * (n:ℝ)^((d:ℝ)-6) →
      (∀ x ∈ J, X x ⊆ Q₁ ∧ ((X x).card:ℝ) ≤ A₀ * (n:ℝ)^(2:ℝ)) →
      (∀ y ∈ J', Y y ⊆ Q₁ ∧ ((Y y).card:ℝ) ≤ A₀ * (n:ℝ)^(2:ℝ)) →
      (∀ z ∈ T, Z z ⊆ B ∧ ((Z z).card:ℝ) ≤ A₀ * (n:ℝ)^(2:ℝ)) →
      let L := section9FiniteTube i n (-(5:ℝ)/8) (3/8)
      let R := section9FiniteTube i n (-(3:ℝ)/8) (5/8)
      let P := orientedLatticePairs (section9FiniteMiddle i n)
      let μ := (section9RevealedLaw (criticalPoint d) Q₁ H₁ Q₃ H₃ F₁ F₃).prod (percolation d q)
      μ.real {ξη | ∃ x ∈ J, ∃ y ∈ J', ∃ z ∈ T,
        ξη ∈ disjointOffspringEvent P L R Q₁ F₁ Q₃ F₃ (X x) (Y y) (Z z) (Z z) B} ≤
        D * (n:ℝ)^(6-(d:ℝ)) := by
  obtain ⟨K, hK⟩ := disjoint_offspring_probability_upper_scale hd asymp q₀ A₀
  refine ⟨(κ:ℝ)^2 * C₀ * max 0 K, ?_⟩
  intro i n hn q hq H₁ H₃ F₁ F₃ B Q₁ Q₃ hH₁ hH₃ hB hpos J J' T X Y Z hJ hJ' hT hX hY hZ L R P μ
  letI := section9RevealedLaw_isProbability (criticalPoint d) Q₁ H₁ Q₃ H₃ F₁ F₃ hpos
  have hn' : 0 < (n:ℝ) := by exact_mod_cast hn
  let k := max 0 K * (n:ℝ)^(12-2*(d:ℝ))
  have hk : 0 ≤ k := mul_nonneg (le_max_left _ _) (Real.rpow_nonneg hn'.le _)
  have hprob (x : ι) (hx : x ∈ J) (y : ι') (hy : y ∈ J') (z : τ) (hz : z ∈ T) :
      μ.real (disjointOffspringEvent P L R Q₁ F₁ Q₃ F₃ (X x) (Y y) (Z z) (Z z) B) ≤ k :=
    (hK i n hn q hq H₁ H₃ F₁ F₃ (X x) (Y y) (Z z) (Z z) B hH₁ hH₃
      (hX x hx).1 (hY y hy).1 (hZ z hz).1 (hZ z hz).1 hB hpos
      (hX x hx).2 (hY y hy).2 (hZ z hz).2 (hZ z hz).2).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hn'.le _))
  have hJJ : (J.card:ℝ) * (J'.card:ℝ) ≤ (κ:ℝ)^2 := by
    rw [pow_two]
    exact mul_le_mul (by exact_mod_cast hJ) (by exact_mod_cast hJ') (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hpow : (n:ℝ)^((d:ℝ)-6) * (n:ℝ)^(12-2*(d:ℝ)) = (n:ℝ)^(6-(d:ℝ)) := by
    rw [← Real.rpow_add hn']
    congr 1
    ring
  calc
    _ ≤ (J.card:ℝ) * (J'.card:ℝ) * (T.card:ℝ) * k :=
      common_disjoint_offspring_probability_le μ P L R Q₁ F₁ Q₃ F₃ B J J' T X Y Z hprob
    _ ≤ (κ:ℝ)^2 * (C₀ * (n:ℝ)^((d:ℝ)-6)) * k :=
      mul_le_mul_of_nonneg_right (mul_le_mul hJJ hT (Nat.cast_nonneg _) (sq_nonneg _)) hk
    _ = (κ:ℝ)^2 * C₀ * max 0 K * ((n:ℝ)^((d:ℝ)-6) * (n:ℝ)^(12-2*(d:ℝ))) := by
      dsimp only [k]
      ring
    _ = _ := by rw [hpow]

end NearCritical.Section10
