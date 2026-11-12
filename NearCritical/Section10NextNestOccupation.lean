module

public import NearCritical.Section10ActualBridgeEvents
public import NearCritical.Section10OffspringUpperProbability

/-! One-step occupation bound for an actual next nest, used for a fresh
arrival in Step 2 of the pair estimate. -/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open MeasureTheory Set
open scoped Classical

/-- A child can enter the next nest only if at least one incoming cluster
has a sprinkled pivot to it. The bound allows the representative choice
and the subset choice to depend on the entire tube outcome. -/
theorem svNext_occupation_probability_le {d : ℕ}
    (μ : Measure (Configuration d × Configuration d)) [IsFiniteMeasure μ]
    (M L R Q₁ F₁ Q₃ F₃ : Finset (Vertex d))
    (hML : M ⊆ L) (hMQ : Disjoint (M : Set (Vertex d)) (Q₁ : Set (Vertex d)))
    (nest cand : Finset (Finset (Vertex d)))
    (src tgt : Finset (Vertex d) → Finset (Vertex d))
    (k : ℕ) (P : Finset (Finset (Finset (Vertex d)))) (c : Finset (Vertex d))
    {K : ℝ} (hK : ∀ a ∈ nest, μ.real {z |
      (sprinkledPivotalPairs z.1 z.2 (orientedLatticePairs M) L R Q₁ F₁ Q₃ F₃
        (src a) (tgt c)).Nonempty} ≤ K) :
    μ.real {z | ∃ N' ∈ svNext (stepView M L R Q₁ F₁ Q₃ F₃ z) nest cand src tgt k P,
      c ∈ N'.val} ≤ (nest.card : ℝ) * K := by
  let F (a : Finset (Vertex d)) := {z : Configuration d × Configuration d |
    (sprinkledPivotalPairs z.1 z.2 (orientedLatticePairs M) L R Q₁ F₁ Q₃ F₃
      (src a) (tgt c)).Nonempty}
  have hcover : {z : Configuration d × Configuration d |
      ∃ N' ∈ svNext (stepView M L R Q₁ F₁ Q₃ F₃ z) nest cand src tgt k P, c ∈ N'.val} ⊆
      ⋃ a ∈ nest, F a := by
    rintro ⟨ω, η⟩ ⟨N', hN', hc⟩
    obtain ⟨_, a, ha, hhit⟩ := svNext_member_has_opened_target ω η M L R Q₁ F₁ Q₃ F₃
      hML hMQ nest cand src tgt hN' hc
    exact Set.mem_iUnion.mpr ⟨a, Set.mem_iUnion.mpr ⟨ha, hhit⟩⟩
  calc
    _ ≤ μ.real (⋃ a ∈ nest, F a) := measureReal_mono hcover (measure_ne_top _ _)
    _ ≤ ∑ a ∈ nest, μ.real (F a) := measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _a ∈ nest, K := Finset.sum_le_sum hK
    _ = _ := by simp [nsmul_eq_mul]

/-- Under the actual two-heart reveal, a prescribed child can occupy a
next nest through a fresh tube with probability O(n^(6−d)). -/
theorem svNext_occupation_probability_upper_scale {d : ℕ} (hd : 2 ≤ d)
    (asymp : TwoPointAsymptotics d) (q₀ A₀ : ℝ) (κ : ℕ) :
    ∃ K : ℝ, ∀ (i : Fin d) (n : ℕ), 0 < n →
      ∀ (q : unitInterval), (q : ℝ) ≤ q₀ * (n:ℝ)^(-2:ℝ) →
      ∀ (H₁ H₃ F₁ F₃ : Finset (Vertex d)),
      let Q₁ := section9FiniteEndCube i n 0
      let Q₃ := section9FiniteEndCube i n (2*(n:ℝ))
      H₁ ⊆ Q₁ → H₃ ⊆ Q₃ →
      percolation d (criticalPoint d) (section9RevealEvent Q₁ H₁ Q₃ H₃ F₁ F₃) ≠ 0 →
      ∀ (nest cand : Finset (Finset (Vertex d))) (src tgt : Finset (Vertex d) → Finset (Vertex d))
        (P : Finset (Finset (Finset (Vertex d)))) (c : Finset (Vertex d)),
      nest.card ≤ κ →
      (∀ a ∈ nest, src a ⊆ Q₁ ∧ ((src a).card:ℝ) ≤ A₀ * (n:ℝ)^(2:ℝ)) →
      tgt c ⊆ Q₃ → ((tgt c).card:ℝ) ≤ A₀ * (n:ℝ)^(2:ℝ) →
      let M := section9FiniteMiddle i n
      let L := section9FiniteTube i n (-(5:ℝ)/8) (3/8)
      let R := section9FiniteTube i n (-(3:ℝ)/8) (5/8)
      let μ := (section9RevealedLaw (criticalPoint d) Q₁ H₁ Q₃ H₃ F₁ F₃).prod (percolation d q)
      μ.real {z | ∃ N' ∈ svNext (stepView M L R Q₁ F₁ Q₃ F₃ z) nest cand src tgt κ P,
        c ∈ N'.val} ≤ K * (n:ℝ)^(6-(d:ℝ)) := by
  obtain ⟨C, hC⟩ := offspring_probability_upper_scale hd asymp q₀ A₀
  refine ⟨(κ:ℝ) * max 0 C, ?_⟩
  intro i n hn q hq H₁ H₃ F₁ F₃ Q₁ Q₃ hH₁ hH₃ hpos nest cand src tgt P c
    hnest hsrc htgt htgtc M L R μ
  letI := section9RevealedLaw_isProbability (criticalPoint d) Q₁ H₁ Q₃ H₃ F₁ F₃ hpos
  have hML : M ⊆ L := by
    dsimp only [M, L]
    rw [section9FiniteMiddle_eq_inter]
    exact Finset.inter_subset_left
  have hMQ : Disjoint (M : Set (Vertex d)) (Q₁ : Set (Vertex d)) := by
    apply Set.disjoint_left.mpr
    intro z hz hq
    exact Finset.disjoint_left.mp (section9FiniteMiddle_disjoint_first i hn) hz hq
  let K := max 0 C * (n:ℝ)^(6-(d:ℝ))
  have hpow : 0 ≤ (n:ℝ)^(6-(d:ℝ)) := Real.rpow_nonneg (by positivity) _
  have hK : 0 ≤ K := mul_nonneg (le_max_left _ _) hpow
  have hhit (a : Finset (Vertex d)) (ha : a ∈ nest) :
      μ.real {z | (sprinkledPivotalPairs z.1 z.2 (orientedLatticePairs M) L R Q₁ F₁ Q₃ F₃
        (src a) (tgt c)).Nonempty} ≤ K :=
    (hC i n hn q hq H₁ H₃ F₁ F₃ (src a) (tgt c) hH₁ hH₃ (hsrc a ha).1 htgt
      hpos (hsrc a ha).2 htgtc).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hpow)
  calc
    _ ≤ (nest.card : ℝ) * K :=
      svNext_occupation_probability_le μ M L R Q₁ F₁ Q₃ F₃ hML hMQ nest cand src tgt κ P c hhit
    _ ≤ (κ:ℝ) * K := mul_le_mul_of_nonneg_right (by exact_mod_cast hnest) hK
    _ = _ := by simp only [K, mul_assoc]

end NearCritical.Section10
