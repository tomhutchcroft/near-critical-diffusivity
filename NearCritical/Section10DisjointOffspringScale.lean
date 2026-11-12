module

public import NearCritical.Section10DisjointOffspringProbability

/-! Source-scale joint offspring probability for the pair estimate. -/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open MeasureTheory
open scoped Classical

private theorem pivot_arm_sum_le {d : ℕ} (p : unitInterval)
    (S A B : Finset (Vertex d)) {K : ℝ} (hK : 0 ≤ K)
    (hA : ∀ z ∈ S, ∀ x ∈ A, twoPoint d p z x ≤ K)
    (hB : ∀ z ∈ S, ∀ y ∈ B, twoPoint d p z y ≤ K) :
    (∑ e ∈ orientedLatticePairs S,
      (∑ x ∈ A, twoPoint d p e.1 x) * (∑ y ∈ B, twoPoint d p e.2 y)) ≤
      (2 * (S.card * d) : ℕ) * (((A.card : ℝ) * K) * ((B.card : ℝ) * K)) := by
  calc
    _ ≤ ∑ _e ∈ orientedLatticePairs S, ((A.card : ℝ) * K) * ((B.card : ℝ) * K) := by
      apply Finset.sum_le_sum
      intro e he
      obtain ⟨hl, hr, _⟩ := (mem_orientedLatticePairs S e.1 e.2).mp he
      have ha : (∑ x ∈ A, twoPoint d p e.1 x) ≤ (A.card : ℝ) * K := by
        simpa only [Finset.sum_const, nsmul_eq_mul] using
          Finset.sum_le_sum (fun x hx => hA e.1 hl x hx)
      have hb : (∑ y ∈ B, twoPoint d p e.2 y) ≤ (B.card : ℝ) * K := by
        simpa only [Finset.sum_const, nsmul_eq_mul] using
          Finset.sum_le_sum (fun y hy => hB e.2 hr y hy)
      exact mul_le_mul ha hb (Finset.sum_nonneg fun _ _ => twoPoint_nonneg _ _ _)
        (mul_nonneg (Nat.cast_nonneg _) hK)
    _ ≤ _ := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast orientedLatticePairs_card_le S

private theorem sprayed_arm_envelope_le {d : ℕ} {n C A B q q₀ A₀ : ℝ}
    (hn : 0 < n) (hC : 0 ≤ C) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hq₀ : 0 ≤ q) (hq : q ≤ q₀ * n ^ (-2 : ℝ))
    (hAc : A ≤ A₀ * n ^ (2 : ℝ)) (hBc : B ≤ A₀ * n ^ (2 : ℝ)) :
    (C * n ^ (4-(d:ℝ)) * A * B) * q ≤ (C * A₀ * A₀ * q₀) * n ^ (6-(d:ℝ)) := by
  have hAA := hA.trans hAc
  have hBB := hB.trans hBc
  have hCpow : 0 ≤ C * n ^ (4-(d:ℝ)) := mul_nonneg hC (Real.rpow_nonneg hn.le _)
  have hscale : n ^ (4-(d:ℝ)) * n ^ (2 : ℝ) * n ^ (2 : ℝ) * n ^ (-2 : ℝ) =
      n ^ (6-(d:ℝ)) := by
    simp only [← Real.rpow_add hn]
    congr 1
    ring
  calc
    _ ≤ (C * n ^ (4-(d:ℝ)) * (A₀ * n ^ (2 : ℝ)) * (A₀ * n ^ (2 : ℝ))) *
        (q₀ * n ^ (-2 : ℝ)) := by
      refine mul_le_mul ?_ hq hq₀ (mul_nonneg (mul_nonneg hCpow hAA) hBB)
      exact mul_le_mul (mul_le_mul_of_nonneg_left hAc hCpow) hBc hB (mul_nonneg hCpow hAA)
    _ = C * A₀ * A₀ * q₀ *
        (n ^ (4-(d:ℝ)) * n ^ (2 : ℝ) * n ^ (2 : ℝ) * n ^ (-2 : ℝ)) := by ring
    _ = _ := by rw [hscale]

/-- Under the actual conditional law, two disjoint offspring hits on source
patches of size at most a constant times n² have probability O(n^(12−2d)).
The statement permits coincident source clusters with opposite face signs. -/
theorem disjoint_offspring_probability_upper_scale {d : ℕ} (hd : 2 ≤ d)
    (asymp : TwoPointAsymptotics d) (q₀ A₀ : ℝ) :
    ∃ D : ℝ, ∀ (i : Fin d) (n : ℕ), 0 < n →
      ∀ (q : unitInterval), (q : ℝ) ≤ q₀ * (n:ℝ)^(-2:ℝ) →
      ∀ (H₁ H₃ F₁ F₃ A₁ A₂ B₁ B₂ B : Finset (Vertex d)),
      let Q₁ := section9FiniteEndCube i n 0
      let Q₃ := section9FiniteEndCube i n (2*(n:ℝ))
      H₁ ⊆ Q₁ → H₃ ⊆ Q₃ → A₁ ⊆ Q₁ → A₂ ⊆ Q₁ → B₁ ⊆ B → B₂ ⊆ B → B ⊆ Q₃ →
      percolation d (criticalPoint d) (section9RevealEvent Q₁ H₁ Q₃ H₃ F₁ F₃) ≠ 0 →
      (A₁.card : ℝ) ≤ A₀ * (n:ℝ)^(2:ℝ) → (A₂.card : ℝ) ≤ A₀ * (n:ℝ)^(2:ℝ) →
      (B₁.card : ℝ) ≤ A₀ * (n:ℝ)^(2:ℝ) → (B₂.card : ℝ) ≤ A₀ * (n:ℝ)^(2:ℝ) →
      let L := section9FiniteTube i n (-(5:ℝ)/8) (3/8)
      let R := section9FiniteTube i n (-(3:ℝ)/8) (5/8)
      let P := orientedLatticePairs (section9FiniteMiddle i n)
      let μ := (section9RevealedLaw (criticalPoint d) Q₁ H₁ Q₃ H₃ F₁ F₃).prod (percolation d q)
      μ.real (disjointOffspringEvent P L R Q₁ F₁ Q₃ F₃ A₁ A₂ B₁ B₂ B) ≤
        D * (n:ℝ)^(12-2*(d:ℝ)) := by
  obtain ⟨C, hC, hTwo⟩ := section9TwoPoint_middle_end_bounds hd asymp
  let K₀ : ℝ := 2 * (d:ℝ) * (7:ℝ)^d * (C * (1/8:ℝ)^((2:ℝ)-(d:ℝ)))^2
  let K₁ : ℝ := K₀ * A₀ * A₀ * q₀
  refine ⟨K₁^2, ?_⟩
  intro i n hn q hq H₁ H₃ F₁ F₃ A₁ A₂ B₁ B₂ B Q₁ Q₃
    hH₁ hH₃ hA₁ hA₂ hB₁ hB₂ hB hpos hAc₁ hAc₂ hBc₁ hBc₂ L R P μ
  obtain ⟨bond, hbond⟩ := section9_middle_candidate_bond_map i n
  let K : ℝ := C * ((n:ℝ)/8)^((2:ℝ)-(d:ℝ))
  have hK : 0 ≤ K := mul_nonneg hC.le (Real.rpow_nonneg (by positivity) _)
  have hK₀ : 0 ≤ K₀ := by dsimp [K₀]; positivity
  have hn' : 0 < (n:ℝ) := by exact_mod_cast hn
  have hn1 : 1 ≤ (n:ℝ) := by exact_mod_cast (show 1 ≤ n from hn)
  let W (A T : Finset (Vertex d)) :=
    (∑ e ∈ P, (∑ x ∈ A, twoPoint d (criticalPoint d) e.1 x) *
      (∑ y ∈ T, twoPoint d (criticalPoint d) e.2 y)) * (q:ℝ)
  have hW₀ (A T : Finset (Vertex d)) : 0 ≤ W A T :=
    mul_nonneg (Finset.sum_nonneg fun _ _ => mul_nonneg
      (Finset.sum_nonneg fun _ _ => twoPoint_nonneg _ _ _)
      (Finset.sum_nonneg fun _ _ => twoPoint_nonneg _ _ _)) q.property.1
  have hW (A T : Finset (Vertex d)) (hA : A ⊆ Q₁) (hT : T ⊆ Q₃)
      (hAc : (A.card:ℝ) ≤ A₀ * (n:ℝ)^(2:ℝ)) (hTc : (T.card:ℝ) ≤ A₀ * (n:ℝ)^(2:ℝ)) :
      W A T ≤ K₁ * (n:ℝ)^(6-(d:ℝ)) := by
    have hsum := pivot_arm_sum_le (criticalPoint d) (section9FiniteMiddle i n) A T hK
      (fun z hz x hx => hTwo i n hn z hz x (Or.inl (hA hx)))
      (fun z hz y hy => hTwo i n hn z hz y (Or.inr (hT hy)))
    have hcard : 2 * ((section9FiniteMiddle i n).card * d) ≤ 2 * ((6*n+1)^d * d) :=
      Nat.mul_le_mul_left 2 (Nat.mul_le_mul_right d (section9FiniteMiddle_card_le i n))
    have hnum := section9MeanEnvelope_normalize d (n:ℝ) C (A.card:ℝ) (T.card:ℝ)
      hn1 hC.le (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    have hcard' : ((2 * ((section9FiniteMiddle i n).card * d) : ℕ):ℝ) ≤
        ((2 * ((6*n+1)^d * d) : ℕ):ℝ) := by exact_mod_cast hcard
    have hsum' : _ ≤ K₀ * (n:ℝ)^(4-(d:ℝ)) * (A.card:ℝ) * (T.card:ℝ) :=
      hsum.trans ((mul_le_mul_of_nonneg_right hcard' (by positivity)).trans
        (by simpa only [K, K₀, Nat.cast_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_ofNat,
          Nat.cast_one, mul_assoc] using hnum))
    exact (mul_le_mul_of_nonneg_right hsum' q.property.1).trans
      (sprayed_arm_envelope_le hn' hK₀ (Nat.cast_nonneg _) (Nat.cast_nonneg _)
        q.property.1 hq hAc hTc)
  have h₁ := hW A₁ B₁ hA₁ (hB₁.trans hB) hAc₁ hBc₁
  have h₂ := hW A₂ B₂ hA₂ (hB₂.trans hB) hAc₂ hBc₂
  have hpow : (n:ℝ)^(6-(d:ℝ)) * (n:ℝ)^(6-(d:ℝ)) = (n:ℝ)^(12-2*(d:ℝ)) := by
    rw [← Real.rpow_add hn']
    congr 1
    ring
  calc
    _ ≤ W A₁ B₁ * W A₂ B₂ :=
      disjoint_offspring_probability_le (criticalPoint d) q P L R Q₁ H₁ F₁ Q₃ H₃ F₃
        A₁ A₂ B₁ B₂ B hB₁ hB₂ hH₁ hH₃ (section9FiniteLeftTube_disjoint_third i hn)
        (section9FiniteRightTube_disjoint_first i hn) hpos bond hbond
    _ ≤ (K₁ * (n:ℝ)^(6-(d:ℝ))) * (K₁ * (n:ℝ)^(6-(d:ℝ))) :=
      mul_le_mul h₁ h₂ (hW₀ _ _) ((hW₀ _ _).trans h₁)
    _ = K₁^2 * ((n:ℝ)^(6-(d:ℝ)) * (n:ℝ)^(6-(d:ℝ))) := by ring
    _ = _ := by rw [hpow]

end NearCritical.Section10
