module

public import NearCritical.SlabUpperTheorem

/-! Coupled renormalisation for prop.slab.upper.

The source proof decides cube regularity from `p_c`-clusters and then sprinkles
inside tubes to reach `p = p_c + λ n⁻²`: the exploration lives on a COUPLING of
several percolation levels, not on the `p`-configuration alone.
`CoupledRenormalizedExploration` therefore takes an arbitrary probability space
`Ω₀` with a measurable `cfg : Ω₀ → Configuration d` of law `percolation d p`
(e.g. uniform edge labels thresholded at `p`), blocks `Φ : Ω₀ → ∀ i, Ω i` with
product law, and nest semantics stated for `cfg`.

Also: `slab_upper_inverse_square_of_reachFar`, the prop.slab.upper conclusion
from uniform far-reach lower bounds alone, of which both the uncoupled and the
coupled versions are corollaries; and the coupled thm.slab sandwich. -/

@[expose] public section
noncomputable section

namespace NearCritical

open MeasureTheory Function
open scoped ENNReal Classical

structure CoupledRenormalizedExploration (d : ℕ) (p : unitInterval) (S : Set (Vertex d))
    (F : Finset (Vertex d)) (N : ℕ) (θ : ℝ≥0∞) where
  Vx : Type
  Ed : Type
  [fintypeVx : Fintype Vx]
  [decEqVx : DecidableEq Vx]
  [fintypeEd : Fintype Ed]
  [decEqEd : DecidableEq Ed]
  ends : Ed → Vx × Vx
  root : Vx
  target : Finset Vx
  Ω₀ : Type
  [measΩ₀ : MeasurableSpace Ω₀]
  P : Measure Ω₀
  [probP : IsProbabilityMeasure P]
  cfg : Ω₀ → Configuration d
  measurable_cfg : Measurable cfg
  map_cfg : Measure.map cfg P = percolation d p
  Ω : Vx ⊕ Ed → Type
  [measΩ : ∀ i, MeasurableSpace (Ω i)]
  ν : ∀ i, Measure (Ω i)
  [probν : ∀ i, IsProbabilityMeasure (ν i)]
  [nonemptyΩ : ∀ i, Nonempty (Ω i)]
  κ : Measure Bool
  [probκ : IsProbabilityMeasure κ]
  Φ : Ω₀ → ∀ i, Ω i
  measurable_Φ : Measurable Φ
  map_Φ : Measure.map Φ P = Measure.pi ν
  succ : ExploreState Vx Ed → (∀ i, Ω i) → Bool
  local_succ : ∀ σ i (x x' : ∀ j, Ω j), ExploreInv ends root σ →
    exploreQuery ends root σ = some i →
      (∀ j ∈ insert i (exploreRevealed σ), x j = x' j) → succ σ x = succ σ x'
  measurable_succ : ∀ σ, Measurable (succ σ)
  prob_succ : ∀ σ i (x : ∀ j, Ω j), ExploreInv ends root σ →
    exploreQuery ends root σ = some i → κ {true} ≤ ν i {y | succ σ (update x i y) = true}
  good : ∀ ω₀, explorePayoff target (adaptiveRun (exploreQuery ends root)
    (exploreNext ends root) succ (Fintype.card (Vx ⊕ Ed)) ⟨∅, ∅, ∅, ∅, ∅⟩ (Φ ω₀)) ≠ 0 →
      cfg ω₀ ∈ restrictedReachFarEvent S F N
  mixed_ge : θ ≤ mixedValue ends root target κ ⟨∅, ∅, ∅, ∅, ∅⟩

theorem CoupledRenormalizedExploration.reachFar_ge {d : ℕ} {p : unitInterval}
    {S : Set (Vertex d)} {F : Finset (Vertex d)} {N : ℕ} {θ : ℝ≥0∞}
    (M : CoupledRenormalizedExploration d p S F N θ) :
    θ ≤ percolation d p (restrictedReachFarEvent S F N) := by
  letI := M.fintypeVx
  letI := M.decEqVx
  letI := M.fintypeEd
  letI := M.decEqEd
  letI := M.measΩ₀
  letI := M.probP
  letI := M.measΩ
  letI := M.probν
  letI := M.nonemptyΩ
  letI := M.probκ
  have hf := measurable_payoff_adaptiveRun (exploreQuery M.ends M.root)
    (exploreNext M.ends M.root) M.succ (explorePayoff M.target) M.measurable_succ
    (Fintype.card (M.Vx ⊕ M.Ed)) ⟨∅, ∅, ∅, ∅, ∅⟩
  have hR := measurableSet_restrictedReachFarEvent S F N
  refine M.mixed_ge.trans ?_
  calc mixedValue M.ends M.root M.target M.κ ⟨∅, ∅, ∅, ∅, ∅⟩
      ≤ ∫⁻ x, explorePayoff M.target (adaptiveRun (exploreQuery M.ends M.root)
          (exploreNext M.ends M.root) M.succ (Fintype.card (M.Vx ⊕ M.Ed))
          ⟨∅, ∅, ∅, ∅, ∅⟩ x) ∂Measure.pi M.ν :=
        exploration_dominates_mixed M.ends M.root M.target M.ν M.κ M.succ M.local_succ
          M.measurable_succ M.prob_succ
    _ = ∫⁻ ω₀, explorePayoff M.target (adaptiveRun (exploreQuery M.ends M.root)
          (exploreNext M.ends M.root) M.succ (Fintype.card (M.Vx ⊕ M.Ed))
          ⟨∅, ∅, ∅, ∅, ∅⟩ (M.Φ ω₀)) ∂M.P := by
        rw [← M.map_Φ, lintegral_map hf M.measurable_Φ]
    _ ≤ ∫⁻ ω₀, (restrictedReachFarEvent S F N).indicator 1 (M.cfg ω₀) ∂M.P := by
        refine lintegral_mono fun ω₀ ↦ ?_
        try dsimp only
        by_cases h0 : explorePayoff M.target (adaptiveRun (exploreQuery M.ends M.root)
            (exploreNext M.ends M.root) M.succ (Fintype.card (M.Vx ⊕ M.Ed))
            ⟨∅, ∅, ∅, ∅, ∅⟩ (M.Φ ω₀)) = 0
        · rw [h0]
          exact zero_le
        · rw [Set.indicator_of_mem (M.good ω₀ h0), Pi.one_apply]
          unfold explorePayoff
          split_ifs <;> simp
    _ = ∫⁻ ω, (restrictedReachFarEvent S F N).indicator 1 ω ∂percolation d p := by
        rw [← M.map_cfg, lintegral_map (measurable_one.indicator hR) M.measurable_cfg]
    _ = _ := lintegral_indicator_one hR

/-- prop.slab.upper from uniform far-reach lower bounds at `p = pc + c n⁻²`. -/
theorem slab_upper_inverse_square_of_reachFar {d : ℕ} {c : ℝ} (hc : 0 < c) (n₀ : ℕ)
    (hreach : ∀ n : ℕ, n₀ ≤ n → 1 ≤ n → ∀ p : unitInterval,
      (p : ℝ) = (criticalPoint d : ℝ) + c / (n : ℝ) ^ 2 →
        ∃ (F : Finset (Vertex d)) (θ : ℝ≥0∞), θ ≠ 0 ∧
          ∀ N, θ ≤ percolation d p (restrictedReachFarEvent (slabVertices d 2 n) F N)) :
    ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n →
      (restrictedCriticalPoint d (slabVertices d 2 n) : ℝ) - criticalPoint d ≤
        C / (n : ℝ) ^ 2 := by
  refine ⟨max c ((n₀ : ℝ) ^ 2), fun n hn ↦ ?_⟩
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hnpos : (0 : ℝ) < (n : ℝ) ^ 2 := pow_pos hn' 2
  have hpc0 : (0 : ℝ) ≤ criticalPoint d := (criticalPoint d).2.1
  have hs1 : (restrictedCriticalPoint d (slabVertices d 2 n) : ℝ) ≤ 1 :=
    (restrictedCriticalPoint d (slabVertices d 2 n)).2.2
  have hcC : c / (n : ℝ) ^ 2 ≤ max c ((n₀ : ℝ) ^ 2) / (n : ℝ) ^ 2 := by
    gcongr
    exact le_max_left _ _
  by_cases hn0 : n₀ ≤ n
  · by_cases hle : (criticalPoint d : ℝ) + c / (n : ℝ) ^ 2 ≤ 1
    · have hv0 : 0 ≤ (criticalPoint d : ℝ) + c / (n : ℝ) ^ 2 :=
        add_nonneg hpc0 (div_nonneg hc.le hnpos.le)
      let p : unitInterval := ⟨(criticalPoint d : ℝ) + c / (n : ℝ) ^ 2, hv0, hle⟩
      obtain ⟨F, θ, hθ, hM⟩ := hreach n hn0 hn p rfl
      have hp : 0 < (p : ℝ) := add_pos_of_nonneg_of_pos hpc0 (div_pos hc hnpos)
      have hcrit := slab_restrictedCriticalPoint_le_of_someInfinite d 2 n p hp
        (restrictedSomeInfinite_ne_zero_of_reachFar p _ F hθ hM)
      have hv : (restrictedCriticalPoint d (slabVertices d 2 n) : ℝ) ≤
          (criticalPoint d : ℝ) + c / (n : ℝ) ^ 2 := Subtype.coe_le_coe.mpr hcrit
      linarith
    · push_neg at hle
      linarith
  · have hnn : (n : ℝ) ≤ n₀ := by exact_mod_cast (Nat.le_of_lt (not_le.mp hn0))
    have hsq : (n : ℝ) ^ 2 ≤ (n₀ : ℝ) ^ 2 := by gcongr
    have h1 : (1 : ℝ) ≤ (n₀ : ℝ) ^ 2 / (n : ℝ) ^ 2 := by
      rw [le_div_iff₀ hnpos]
      linarith
    have hC : (n₀ : ℝ) ^ 2 / (n : ℝ) ^ 2 ≤ max c ((n₀ : ℝ) ^ 2) / (n : ℝ) ^ 2 := by
      gcongr
      exact le_max_right _ _
    linarith

/-- prop.slab.upper with COUPLED renormalised explorations (source form). -/
theorem slab_upper_inverse_square_coupled {d : ℕ} {c : ℝ} (hc : 0 < c) (n₀ : ℕ)
    (hmodel : ∀ n : ℕ, n₀ ≤ n → 1 ≤ n → ∀ p : unitInterval,
      (p : ℝ) = (criticalPoint d : ℝ) + c / (n : ℝ) ^ 2 →
        ∃ (F : Finset (Vertex d)) (θ : ℝ≥0∞), θ ≠ 0 ∧
          ∀ N, Nonempty (CoupledRenormalizedExploration d p (slabVertices d 2 n) F N θ)) :
    ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n →
      (restrictedCriticalPoint d (slabVertices d 2 n) : ℝ) - criticalPoint d ≤
        C / (n : ℝ) ^ 2 := by
  refine slab_upper_inverse_square_of_reachFar hc n₀ fun n hn0 hn p hp ↦ ?_
  obtain ⟨F, θ, hθ, hM⟩ := hmodel n hn0 hn p hp
  exact ⟨F, θ, hθ, fun N ↦ (hM N).some.reachFar_ge⟩

/-- Source Theorem 1.3 (thm.slab) sandwich with coupled renormalisation data.
CONDITIONAL: pioneer decay and the coupled data are inputs. -/
theorem slab_theorem_of_coupled_inputs {d : ℕ} (hd : 3 ≤ d)
    {C c : ℝ} (hC : 0 < C) (hc : 0 < c) (hpc : 0 < (criticalPoint d : ℝ))
    (hpc1 : (criticalPoint d : ℝ) < 1)
    (decay : WeightedPositiveHeightPioneerDecay (criticalPoint d)
      (⟨d-1, by omega⟩ : Fin d) C c)
    {lam : ℝ} (hlam : 0 < lam) (n₀ : ℕ)
    (hmodel : ∀ n : ℕ, n₀ ≤ n → 1 ≤ n → ∀ p : unitInterval,
      (p : ℝ) = (criticalPoint d : ℝ) + lam / (n : ℝ) ^ 2 →
        ∃ (F : Finset (Vertex d)) (θ : ℝ≥0∞), θ ≠ 0 ∧
          ∀ N, Nonempty (CoupledRenormalizedExploration d p (slabVertices d 2 n) F N θ)) :
    ∃ a A : ℝ, 0 < a ∧ ∀ n : ℕ, 1 ≤ n →
      a / (n : ℝ) ^ 2 ≤
          (restrictedCriticalPoint d (slabVertices d (d-1) n) : ℝ) - criticalPoint d ∧
        (restrictedCriticalPoint d (slabVertices d (d-1) n) : ℝ) - criticalPoint d ≤
          (restrictedCriticalPoint d (slabVertices d 2 n) : ℝ) - criticalPoint d ∧
        (restrictedCriticalPoint d (slabVertices d 2 n) : ℝ) - criticalPoint d ≤
          A / (n : ℝ) ^ 2 := by
  obtain ⟨a, ha, hlow⟩ :=
    slabCriticalPoint_lower_of_weighted (by omega) hC hc hpc hpc1 decay
  obtain ⟨A, hup⟩ := slab_upper_inverse_square_coupled hlam n₀ hmodel
  refine ⟨a, A, ha, fun n hn ↦ ⟨hlow n hn, ?_, hup n hn⟩⟩
  have : (restrictedCriticalPoint d (slabVertices d (d-1) n) : ℝ) ≤
      restrictedCriticalPoint d (slabVertices d 2 n) :=
    slabCriticalPoint_comparison d n hd
  linarith

end NearCritical
