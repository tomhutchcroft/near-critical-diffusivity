module

public import NearCritical.SlabUpperFarTarget

/-! thm.slab assembled down to the source's ONE-STEP inputs.

All the structure is fixed: the coarse box `centeredBox 2 R`, the blocks
`slabSprinkleBlocks`, the two-layer law at `orParameter p_c s`, and the
reach-far scale `2nR - n`. The block law, the disjointness, the far-target
geometry and the pigeonhole/threshold bridges are PROVED upstream. The remaining
inputs are collected in `SlabOneStepInputs`, plus cited grimmett1999 (`hθ`) and
pioneer decay:
* a per-step success rule `succ` that is local and measurable;
* its per-step success bound, which is source prop.sprinkling.AB.disjoint
  together with prop.regular_cube;
* the one-step nest-connection facts `hroot`/`hedge`. -/

@[expose] public section
noncomputable section

namespace NearCritical

open MeasureTheory unitInterval
open scoped ENNReal Classical

variable {d : ℕ}

theorem zero_mem_centeredBox_two (R : ℕ) : (0 : Vertex 2) ∈ centeredBox 2 R := by
  rw [mem_centeredBox]
  intro i
  simp

/-- The source one-step inputs on the coarse box of radius `R` at scale `n`. -/
structure SlabOneStepInputs (d n R : ℕ) (a s : I) (S : Set (Vertex d))
    (F : Finset (Vertex d)) (κ : Measure Bool) where
  A : Finset (Bond d)
  succ : ExploreState (centeredBox 2 R) (boxBonds (centeredBox 2 R)) →
    (∀ i, slabSprinkleBlocks (d := d) n A (centeredBox 2 R) i → Bool) → Bool
  local_succ : ∀ st i (x x' : ∀ j, slabSprinkleBlocks (d := d) n A (centeredBox 2 R) j → Bool),
    ExploreInv (boxEnds (centeredBox 2 R)) (⟨0, zero_mem_centeredBox_two R⟩ : centeredBox 2 R) st →
    exploreQuery (boxEnds (centeredBox 2 R))
      (⟨0, zero_mem_centeredBox_two R⟩ : centeredBox 2 R) st = some i →
    (∀ j ∈ insert i (exploreRevealed st), x j = x' j) → succ st x = succ st x'
  measurable_succ : ∀ st, Measurable (succ st)
  prob_succ : ∀ st i (x : ∀ j, slabSprinkleBlocks (d := d) n A (centeredBox 2 R) j → Bool),
    ExploreInv (boxEnds (centeredBox 2 R)) (⟨0, zero_mem_centeredBox_two R⟩ : centeredBox 2 R) st →
    exploreQuery (boxEnds (centeredBox 2 R))
      (⟨0, zero_mem_centeredBox_two R⟩ : centeredBox 2 R) st = some i →
    κ {true} ≤ Measure.pi (fun e : slabSprinkleBlocks (d := d) n A (centeredBox 2 R) i =>
        sprinkleLaw a s (e : Bond d × Bool))
      {y | succ st (Function.update x i y) = true}
  hroot : ∀ (ω : Bond d × Bool → Bool) st,
    ExploreInv (boxEnds (centeredBox 2 R)) (⟨0, zero_mem_centeredBox_two R⟩ : centeredBox 2 R) st →
    exploreMove (boxEnds (centeredBox 2 R))
      (⟨0, zero_mem_centeredBox_two R⟩ : centeredBox 2 R) st = some .root →
    succ st (blockFamily (slabSprinkleBlocks n A (centeredBox 2 R)) ω) = true →
    slabNestJoined n S F (sprinkleConfiguration ω) 0
  hedge : ∀ (ω : Bond d × Bool → Bool) st e z,
    ExploreInv (boxEnds (centeredBox 2 R)) (⟨0, zero_mem_centeredBox_two R⟩ : centeredBox 2 R) st →
    (∀ v ∈ st.A, slabNestJoined n S F (sprinkleConfiguration ω) (v : Vertex 2)) →
    exploreMove (boxEnds (centeredBox 2 R))
      (⟨0, zero_mem_centeredBox_two R⟩ : centeredBox 2 R) st = some (.edge e z) →
    succ st (blockFamily (slabSprinkleBlocks n A (centeredBox 2 R)) ω) = true →
    slabNestJoined n S F (sprinkleConfiguration ω) (z : Vertex 2)

/-- One-step inputs give coupled renormalisation data at scale `2nR - n`. -/
theorem SlabOneStepInputs.coupled (hd : 2 ≤ d) {n R : ℕ} (hn : 0 < n) {a s : I}
    {S : Set (Vertex d)} {F : Finset (Vertex d)} {κ : Measure Bool} [IsProbabilityMeasure κ]
    {θ : ℝ≥0∞} (hθ : MixedSiteBondPercolationInput 2 κ θ)
    (X : SlabOneStepInputs d n R a s S F κ) :
    Nonempty (CoupledRenormalizedExploration d (orParameter a s) S F (2 * n * R - n) θ) :=
  coupledRenormalizedExploration_of_slabBlocks hd hn a s S F (2 * n * R - n) X.A
    (centeredBox 2 R) (zero_mem_centeredBox_two R) κ hθ X.succ X.local_succ
    X.measurable_succ X.prob_succ
    (fun ω => slab_good_of_oneStep hd S F X.A (zero_mem_centeredBox_two R) X.succ ω
      (X.hroot ω) (X.hedge ω))

/-- Coupled data at a larger reach scale give it at any smaller one. -/
def CoupledRenormalizedExploration.mono {p : I} {S : Set (Vertex d)} {F : Finset (Vertex d)}
    {N M : ℕ} {θ : ℝ≥0∞} (hNM : N ≤ M) (X : CoupledRenormalizedExploration d p S F M θ) :
    CoupledRenormalizedExploration d p S F N θ :=
  { X with good := fun ω h => restrictedReachFarEvent_antitone S F hNM (X.good ω h) }

lemma le_two_mul_sub (N n : ℕ) (hn : 1 ≤ n) : N ≤ 2 * n * N - n := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  · have : N + n ≤ 2 * n * N := by nlinarith
    omega

/-- Source thm.slab (Theorem 1.3) from pioneer decay, cited grimmett1999, and
the source one-step inputs on the literal slab blocks. CONDITIONAL. -/
theorem slab_theorem_of_oneStep_inputs (hd : 3 ≤ d)
    {C c : ℝ} (hC : 0 < C) (hc : 0 < c) (hpc : 0 < (criticalPoint d : ℝ))
    (hpc1 : (criticalPoint d : ℝ) < 1)
    (decay : WeightedPositiveHeightPioneerDecay (criticalPoint d)
      (⟨d-1, by omega⟩ : Fin d) C c)
    {lam : ℝ} (hlam : 0 < lam) (n₀ : ℕ)
    (κ : Measure Bool) [IsProbabilityMeasure κ] {θ : ℝ≥0∞} (hθ0 : θ ≠ 0)
    (hθ : MixedSiteBondPercolationInput 2 κ θ)
    (hmodel : ∀ n : ℕ, n₀ ≤ n → 1 ≤ n → ∀ p : I,
      (p : ℝ) = (criticalPoint d : ℝ) + lam / (n : ℝ) ^ 2 →
        ∃ s : I, orParameter (criticalPoint d) s = p ∧ ∃ F : Finset (Vertex d),
          ∀ R, Nonempty (SlabOneStepInputs d n R (criticalPoint d) s (slabVertices d 2 n) F κ)) :
    ∃ a A : ℝ, 0 < a ∧ ∀ n : ℕ, 1 ≤ n →
      a / (n : ℝ) ^ 2 ≤
          (restrictedCriticalPoint d (slabVertices d (d-1) n) : ℝ) - criticalPoint d ∧
        (restrictedCriticalPoint d (slabVertices d (d-1) n) : ℝ) - criticalPoint d ≤
          (restrictedCriticalPoint d (slabVertices d 2 n) : ℝ) - criticalPoint d ∧
        (restrictedCriticalPoint d (slabVertices d 2 n) : ℝ) - criticalPoint d ≤
          A / (n : ℝ) ^ 2 := by
  refine slab_theorem_of_coupled_inputs hd hC hc hpc hpc1 decay hlam n₀ ?_
  intro n hn0 hn p hp
  obtain ⟨s, hsp, F, hX⟩ := hmodel n hn0 hn p hp
  refine ⟨F, θ, hθ0, fun N => ?_⟩
  obtain ⟨Y⟩ := (hX N).some.coupled (by omega) (by omega) hθ
  rw [← hsp]
  exact ⟨Y.mono (le_two_mul_sub N n hn)⟩

end NearCritical
