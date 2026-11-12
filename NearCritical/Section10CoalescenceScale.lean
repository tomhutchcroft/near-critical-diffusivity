module

public import NearCritical.Section9CoalescenceProposition
public import NearCritical.Section10CoalescenceReduction

@[expose] public section
namespace NearCritical.Section10
open MeasureTheory
open scoped Classical ENNReal

/-- The Section 9 coalescence powers cancel against the source patch
and two regular-face cardinality bounds. -/
theorem bridge_coalescence_scale_le {d : ℕ} {n X Y B A F C₁ C₂ : ℝ}
    (hn : 0 < n) (hX : 0 ≤ X) (hY : 0 ≤ Y) (hB : 0 ≤ B)
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hx : X ≤ A * n ^ (2 : ℝ))
    (hy : Y ≤ F * n ^ ((d : ℝ) - 4)) (hb : B ≤ F * n ^ ((d : ℝ) - 4)) :
    C₁ * B * min X Y * n ^ ((2 : ℝ) - (d : ℝ)) +
      C₂ * B * X * Y * n ^ (6 - 2 * (d : ℝ)) ≤ C₁ * F * A + C₂ * F^2 * A := by
  have hA : 0 ≤ A * n ^ (2 : ℝ) := hX.trans hx
  have hF : 0 ≤ F * n ^ ((d : ℝ) - 4) := hY.trans hy
  have hMin := (min_le_left X Y).trans hx
  calc
    _ ≤ C₁ * (F * n ^ ((d : ℝ) - 4)) * (A * n ^ (2 : ℝ)) * n ^ ((2 : ℝ) - (d : ℝ)) +
        C₂ * (F * n ^ ((d : ℝ) - 4)) * (A * n ^ (2 : ℝ)) *
          (F * n ^ ((d : ℝ) - 4)) * n ^ (6 - 2 * (d : ℝ)) := by
      gcongr
    _ = _ := by
      have h₁ : n ^ ((d : ℝ) - 4) * n ^ (2 : ℝ) * n ^ ((2 : ℝ) - (d : ℝ)) = 1 := by
        simp only [← Real.rpow_add hn]
        have h : (d : ℝ) - 4 + 2 + (2 - (d : ℝ)) = 0 := by ring
        rw [h, Real.rpow_zero]
      have h₂ : n ^ ((d : ℝ) - 4) * n ^ (2 : ℝ) * n ^ ((d : ℝ) - 4) *
          n ^ (6 - 2 * (d : ℝ)) = 1 := by
        simp only [← Real.rpow_add hn]
        have h : (d : ℝ) - 4 + 2 + ((d : ℝ) - 4) + (6 - 2 * (d : ℝ)) = 0 := by ring
        rw [h, Real.rpow_zero]
      calc
        _ = C₁ * F * A * (n ^ ((d : ℝ) - 4) * n ^ (2 : ℝ) * n ^ ((2 : ℝ) - (d : ℝ))) +
            C₂ * F^2 * A * (n ^ ((d : ℝ) - 4) * n ^ (2 : ℝ) * n ^ ((d : ℝ) - 4) *
              n ^ (6 - 2 * (d : ℝ))) := by ring
        _ = _ := by rw [h₁, h₂, mul_one, mul_one]

/-- The ordered-pair count dominating the bridge-site count has a uniform
conditional first moment at the source patch and face scales. -/
theorem bridge_coalescence_pairs_expectation_le {d : ℕ} (hd : 5 ≤ d)
    (asymptotics : TwoPointAsymptotics d) (q₀ : ℝ) (r : ℕ) (hr : 1 ≤ r) (δ A₀ F₀ : ℝ) :
    ∃ K : ℝ, ∀ (i : Fin d) (n : ℕ), 0 < n →
      ∀ (q : unitInterval), (q : ℝ) ≤ q₀ * (n : ℝ)^(-2 : ℝ) →
      ∀ (L R Q₁ F₁ Q₃ F₃ B H₁ H₃ A face S boundary : Finset (Vertex d)),
        H₁ ⊆ Q₁ → H₃ ⊆ Q₃ → Disjoint L Q₃ → Disjoint R Q₁ →
        percolation d (criticalPoint d) (section9RevealEvent Q₁ H₁ Q₃ H₃ F₁ F₃) ≠ 0 →
        L ⊆ centeredBox d (3*n) → R ⊆ centeredBox d (3*n) →
        B ⊆ section9FiniteEndCube i n (2*(n:ℝ)) →
        A ⊆ section9FiniteEndCube i n 0 → face ⊆ section9FiniteEndCube i n 0 →
        (∀ x ∈ A, sourceRegularPoint F₁ S boundary r δ x) →
        (∀ x ∈ face, sourceRegularPoint F₁ S boundary r δ x) →
        (A.card : ℝ) ≤ A₀ * (n:ℝ)^(2:ℝ) →
        ((face \ A).card : ℝ) ≤ F₀ * (n:ℝ)^((d:ℝ)-4) →
        (B.card : ℝ) ≤ F₀ * (n:ℝ)^((d:ℝ)-4) →
        let P := orientedLatticePairs (section9FiniteMiddle i n)
        let μ := (section9RevealedLaw (criticalPoint d) Q₁ H₁ Q₃ H₃ F₁ F₃).prod (percolation d q)
        (∫⁻ ξη, (section9CoalescenceCount ξη.1 ξη.2 P L R Q₁ F₁ Q₃ F₃ (face \ A) A B : ENNReal) ∂μ) ≤
          ENNReal.ofReal K := by
  obtain ⟨C₁, C₂, h⟩ := section9_coalescence_expectation_upper hd asymptotics q₀ r hr δ
  let D₁ := max 0 C₁
  let D₂ := max 0 C₂
  refine ⟨D₁ * F₀ * A₀ + D₂ * F₀^2 * A₀, ?_⟩
  intro i n hn q hq L R Q₁ F₁ Q₃ F₃ B H₁ H₃ A face S boundary hH₁ hH₃ hLQ₃ hRQ₁
    hpos hL hR hB hA hface hAreg hFreg hAc hFc hBc P μ
  letI := section9RevealedLaw_isProbability (criticalPoint d) Q₁ H₁ Q₃ H₃ F₁ F₃ hpos
  rw [lintegral_section9_coalescence_count_eq_ofReal]
  apply ENNReal.ofReal_le_ofReal
  have hbase := h i n hn q hq L R Q₁ F₁ Q₃ F₃ B H₁ H₃ (face \ A) A S boundary
    hH₁ hH₃ hLQ₃ hRQ₁ hpos hL hR hB
    (fun z hz => hface (Finset.mem_sdiff.mp hz).1) hA
    (fun z hz => hFreg z (Finset.mem_sdiff.mp hz).1) hAreg
  have hscale := bridge_coalescence_scale_le (d := d) (by exact_mod_cast hn)
    (Nat.cast_nonneg A.card) (Nat.cast_nonneg (face \ A).card) (Nat.cast_nonneg B.card)
    (le_max_left 0 C₁) (le_max_left 0 C₂) hAc hFc hBc
  refine hbase.trans (le_trans ?_ hscale)
  have hMin : ((min (face \ A).card A.card : ℕ) : ℝ) =
      min (A.card : ℝ) ((face \ A).card : ℝ) := by rw [Nat.cast_min, min_comm]
  rw [← hMin]
  calc
    _ ≤ D₁ * (B.card : ℝ) * (min (face \ A).card A.card : ℕ) * (n:ℝ)^((2:ℝ)-(d:ℝ)) +
        D₂ * (B.card : ℝ) * ((face \ A).card : ℝ) * (A.card : ℝ) *
          (n:ℝ)^(6-2*(d:ℝ)) := by
      gcongr <;> exact le_max_right _ _
    _ = _ := by ring

/-- The bridge coalescence failure event is dominated by the tail of
the measurable ordered-pair count. -/
theorem bridge_coalescing_sites_markov {d : ℕ}
    (μ : Measure (Configuration d × Configuration d))
    (P : Finset (Vertex d × Vertex d)) (L R Q₁ F₁ Q₃ F₃ A face B : Finset (Vertex d))
    (m : ℕ) :
    (m : ENNReal) * μ {ξη |
      m ≤ (bridgeCoalescingSites ξη.1 ξη.2 P L R Q₁ F₁ Q₃ F₃ A face B).card} ≤
      ∫⁻ ξη, (section9CoalescenceCount ξη.1 ξη.2 P L R Q₁ F₁ Q₃ F₃ (face \ A) A B : ENNReal) ∂μ := by
  let N := fun ξη : Configuration d × Configuration d =>
    (section9CoalescenceCount ξη.1 ξη.2 P L R Q₁ F₁ Q₃ F₃ (face \ A) A B : ENNReal)
  have hm : Measurable N := by
    have h := ENNReal.measurable_ofReal.comp
      (measurable_section9_coalescence_count P L R Q₁ F₁ Q₃ F₃ (face \ A) A B)
    simpa only [Function.comp_def, ENNReal.ofReal_natCast] using h
  refine (mul_le_mul_of_nonneg_left (measure_mono (t := {ξη | (m : ENNReal) ≤ N ξη}) ?_) zero_le).trans
    (mul_meas_ge_le_lintegral hm _)
  intro ξη hξη
  change m ≤ (bridgeCoalescingSites ξη.1 ξη.2 P L R Q₁ F₁ Q₃ F₃ A face B).card at hξη
  change (m : ENNReal) ≤
    (section9CoalescenceCount ξη.1 ξη.2 P L R Q₁ F₁ Q₃ F₃ (face \ A) A B : ENNReal)
  exact_mod_cast hξη.trans
    (bridgeCoalescingSites_card_le_pairs ξη.1 ξη.2 P L R Q₁ F₁ Q₃ F₃ A face B)

/-- The probability of failing the coalescence threshold is at most
a scale-independent constant divided by the threshold. -/
theorem bridge_coalescing_sites_uniform_tail {d : ℕ} (hd : 5 ≤ d)
    (asymptotics : TwoPointAsymptotics d) (q₀ : ℝ) (r : ℕ) (hr : 1 ≤ r) (δ A₀ F₀ : ℝ) :
    ∃ K : ℝ, ∀ (i : Fin d) (n : ℕ), 0 < n →
      ∀ (q : unitInterval), (q : ℝ) ≤ q₀ * (n : ℝ)^(-2 : ℝ) →
      ∀ (L R Q₁ F₁ Q₃ F₃ B H₁ H₃ A face S boundary : Finset (Vertex d)),
        H₁ ⊆ Q₁ → H₃ ⊆ Q₃ → Disjoint L Q₃ → Disjoint R Q₁ →
        percolation d (criticalPoint d) (section9RevealEvent Q₁ H₁ Q₃ H₃ F₁ F₃) ≠ 0 →
        L ⊆ centeredBox d (3*n) → R ⊆ centeredBox d (3*n) →
        B ⊆ section9FiniteEndCube i n (2*(n:ℝ)) →
        A ⊆ section9FiniteEndCube i n 0 → face ⊆ section9FiniteEndCube i n 0 →
        (∀ x ∈ A, sourceRegularPoint F₁ S boundary r δ x) →
        (∀ x ∈ face, sourceRegularPoint F₁ S boundary r δ x) →
        (A.card : ℝ) ≤ A₀ * (n:ℝ)^(2:ℝ) →
        ((face \ A).card : ℝ) ≤ F₀ * (n:ℝ)^((d:ℝ)-4) →
        (B.card : ℝ) ≤ F₀ * (n:ℝ)^((d:ℝ)-4) →
        let P := orientedLatticePairs (section9FiniteMiddle i n)
        let μ := (section9RevealedLaw (criticalPoint d) Q₁ H₁ Q₃ H₃ F₁ F₃).prod (percolation d q)
        ∀ m : ℕ, (m : ENNReal) * μ {ξη |
          m ≤ (bridgeCoalescingSites ξη.1 ξη.2 P L R Q₁ F₁ Q₃ F₃ A face B).card} ≤ ENNReal.ofReal K := by
  obtain ⟨K, hK⟩ := bridge_coalescence_pairs_expectation_le hd asymptotics q₀ r hr δ A₀ F₀
  refine ⟨K, ?_⟩
  intro i n hn q hq L R Q₁ F₁ Q₃ F₃ B H₁ H₃ A face S boundary hH₁ hH₃ hLQ₃ hRQ₁
    hpos hL hR hB hA hface hAreg hFreg hAc hFc hBc P μ m
  exact (bridge_coalescing_sites_markov μ P L R Q₁ F₁ Q₃ F₃ A face B m).trans
    (hK i n hn q hq L R Q₁ F₁ Q₃ F₃ B H₁ H₃ A face S boundary hH₁ hH₃ hLQ₃ hRQ₁
      hpos hL hR hB hA hface hAreg hFreg hAc hFc hBc)

/-- The source sprinkle parameter at p = p_c + λ n⁻² has the
quadratic envelope used by the conditional bridge estimate. -/
theorem source_sprinkle_rate_eq {p pc q rate n : ℝ}
    (hp : p = pc + rate * n ^ (-2 : ℝ))
    (hq : q = (p - pc) / (1 - pc)) :
    q = (rate / (1 - pc)) * n ^ (-2 : ℝ) := by
  rw [hq, hp]
  have h : pc + rate * n ^ (-2 : ℝ) - pc = rate * n ^ (-2 : ℝ) := by ring
  simp only [h, div_eq_mul_inv]
  ring

/-- A uniform first-moment constant determines one threshold for any
positive failure budget, independent of the microscopic scale. -/
theorem exists_bridge_coalescence_threshold (K ε : ℝ) (hε : 0 < ε) :
    ∃ m : ℕ, 0 < m ∧ ∀ a : ENNReal,
      (m : ENNReal) * a ≤ ENNReal.ofReal K → a ≤ ENNReal.ofReal ε := by
  obtain ⟨m, hm⟩ := exists_nat_gt (max 0 (K / ε))
  have hm0 : 0 < m := by
    exact_mod_cast (le_max_left 0 (K / ε)).trans_lt hm
  have hk : K ≤ ε * (m : ℝ) := by
    have h := (div_lt_iff₀ hε).mp ((le_max_right 0 (K / ε)).trans_lt hm)
    linarith
  refine ⟨m, hm0, fun a ha => ?_⟩
  have hne : (m : ENNReal) ≠ 0 := by exact_mod_cast hm0.ne'
  have htop : (m : ENNReal) ≠ ⊤ := by simp
  apply ((ENNReal.le_div_iff_mul_le (.inl hne) (.inl htop)).mpr
    (by simpa only [mul_comm a] using ha)).trans
  apply (ENNReal.div_le_iff hne htop).mpr
  simpa only [ENNReal.ofReal_mul hε.le, ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal hk

end NearCritical.Section10
