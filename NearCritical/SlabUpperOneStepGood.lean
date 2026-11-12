module

public import NearCritical.SlabUpperOneStepAssembly

/-! One-step slab inputs with a GENERAL per-site invariant.

`SlabOneStepInputs` fixes the invariant of the adaptive exploration to
`slabNestJoined` ("some point of the cube of `v` is joined to `F`"). That is too
weak to be propagated by a history-independent success rule: knowing that SOME
point of the parent cube is joined to `F` does not say that the cluster used by
the tube step is. The source propagates a stronger statement (a cluster OF THE
NEST of the cube is joined to the root nest; source 6097-6100).

`SlabOneStepGoodInputs` therefore carries an arbitrary invariant `Good ω v` with
`Good ω v -> slabNestJoined ... v`, and one-step facts for `Good`.
`slab_good_of_oneStep_good` and `SlabOneStepGoodInputs.coupled` rebuild the
coupled renormalised exploration, and `slab_theorem_of_oneStepGood_inputs` is
thm.slab from these inputs. `SlabOneStepInputs.toGood` shows the old structure
is the special case `Good = slabNestJoined`.

No probability is proved here; `prob_succ` is unchanged.
-/

@[expose] public section
noncomputable section

namespace NearCritical

open MeasureTheory unitInterval
open scoped ENNReal Classical

variable {d : ℕ}

/-- The `good` field from one-step facts for a general invariant. -/
theorem slab_good_of_oneStep_good (hd : 2 ≤ d) {n R : ℕ} (S : Set (Vertex d))
    (F : Finset (Vertex d)) (A : Finset (Bond d)) (h0 : (0 : Vertex 2) ∈ centeredBox 2 R)
    (succ : ExploreState (centeredBox 2 R) (boxBonds (centeredBox 2 R)) →
      (∀ i, slabSprinkleBlocks (d := d) n A (centeredBox 2 R) i → Bool) → Bool)
    (ω : Bond d × Bool → Bool) (Good : centeredBox 2 R → Prop)
    (hjoin : ∀ v, Good v → slabNestJoined n S F (sprinkleConfiguration ω) (v : Vertex 2))
    (hroot : ∀ st, ExploreInv (boxEnds (centeredBox 2 R)) (⟨0, h0⟩ : centeredBox 2 R) st →
      exploreMove (boxEnds (centeredBox 2 R)) (⟨0, h0⟩ : centeredBox 2 R) st = some .root →
      succ st (blockFamily (slabSprinkleBlocks n A (centeredBox 2 R)) ω) = true →
      Good ⟨0, h0⟩)
    (hedge : ∀ st e z, ExploreInv (boxEnds (centeredBox 2 R)) (⟨0, h0⟩ : centeredBox 2 R) st →
      (∀ v ∈ st.A, Good v) →
      exploreMove (boxEnds (centeredBox 2 R)) (⟨0, h0⟩ : centeredBox 2 R) st =
        some (.edge e z) →
      succ st (blockFamily (slabSprinkleBlocks n A (centeredBox 2 R)) ω) = true →
      Good z) :
    explorePayoff (boxInnerBoundary (centeredBox 2 R))
      (adaptiveRun (exploreQuery (boxEnds (centeredBox 2 R)) (⟨0, h0⟩ : centeredBox 2 R))
        (exploreNext (boxEnds (centeredBox 2 R)) (⟨0, h0⟩ : centeredBox 2 R)) succ
        (Fintype.card (centeredBox 2 R ⊕ boxBonds (centeredBox 2 R))) ⟨∅, ∅, ∅, ∅, ∅⟩
        (blockFamily (slabSprinkleBlocks (d := d) n A (centeredBox 2 R)) ω)) ≠ 0 →
      sprinkleConfiguration ω ∈ restrictedReachFarEvent S F (2 * n * R - n) := by
  intro h
  obtain ⟨v, hv, hG⟩ :=
    explorePayoff_ne_zero_good (boxEnds (centeredBox 2 R)) (⟨0, h0⟩ : centeredBox 2 R)
      (boxInnerBoundary (centeredBox 2 R)) succ
      (blockFamily (slabSprinkleBlocks n A (centeredBox 2 R)) ω) Good hroot hedge h
  obtain ⟨x, hx, w, hw, hr⟩ := hjoin v hG
  refine ⟨x, hx, w, ?_, hr⟩
  simp only [boxInnerBoundary, Finset.mem_filter] at hv
  obtain ⟨y, hy, hadj⟩ := hv.2
  obtain ⟨c, hc⟩ := exists_coord_abs_ge_of_innerBoundary v.2 hy hadj
  exact vertexSize_ge_of_mem_slabCube hd hc hw

/-- One-step inputs with a general invariant `Good`. -/
structure SlabOneStepGoodInputs (d n R : ℕ) (a s : I) (S : Set (Vertex d))
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
  Good : (Bond d × Bool → Bool) → centeredBox 2 R → Prop
  good_joined : ∀ ω v, Good ω v → slabNestJoined n S F (sprinkleConfiguration ω) (v : Vertex 2)
  hroot : ∀ (ω : Bond d × Bool → Bool) st,
    ExploreInv (boxEnds (centeredBox 2 R)) (⟨0, zero_mem_centeredBox_two R⟩ : centeredBox 2 R) st →
    exploreMove (boxEnds (centeredBox 2 R))
      (⟨0, zero_mem_centeredBox_two R⟩ : centeredBox 2 R) st = some .root →
    succ st (blockFamily (slabSprinkleBlocks n A (centeredBox 2 R)) ω) = true →
    Good ω ⟨0, zero_mem_centeredBox_two R⟩
  hedge : ∀ (ω : Bond d × Bool → Bool) st e z,
    ExploreInv (boxEnds (centeredBox 2 R)) (⟨0, zero_mem_centeredBox_two R⟩ : centeredBox 2 R) st →
    (∀ v ∈ st.A, Good ω v) →
    exploreMove (boxEnds (centeredBox 2 R))
      (⟨0, zero_mem_centeredBox_two R⟩ : centeredBox 2 R) st = some (.edge e z) →
    succ st (blockFamily (slabSprinkleBlocks n A (centeredBox 2 R)) ω) = true →
    Good ω z

/-- General-invariant one-step inputs give coupled renormalisation data. -/
theorem SlabOneStepGoodInputs.coupled (hd : 2 ≤ d) {n R : ℕ} (hn : 0 < n) {a s : I}
    {S : Set (Vertex d)} {F : Finset (Vertex d)} {κ : Measure Bool} [IsProbabilityMeasure κ]
    {θ : ℝ≥0∞} (hθ : MixedSiteBondPercolationInput 2 κ θ)
    (X : SlabOneStepGoodInputs d n R a s S F κ) :
    Nonempty (CoupledRenormalizedExploration d (orParameter a s) S F (2 * n * R - n) θ) :=
  coupledRenormalizedExploration_of_slabBlocks hd hn a s S F (2 * n * R - n) X.A
    (centeredBox 2 R) (zero_mem_centeredBox_two R) κ hθ X.succ X.local_succ
    X.measurable_succ X.prob_succ
    (fun ω => slab_good_of_oneStep_good hd S F X.A (zero_mem_centeredBox_two R) X.succ ω
      (X.Good ω) (X.good_joined ω) (X.hroot ω) (X.hedge ω))

/-- The original structure is the case `Good = slabNestJoined`. -/
def SlabOneStepInputs.toGood {n R : ℕ} {a s : I} {S : Set (Vertex d)}
    {F : Finset (Vertex d)} {κ : Measure Bool} (X : SlabOneStepInputs d n R a s S F κ) :
    SlabOneStepGoodInputs d n R a s S F κ where
  A := X.A
  succ := X.succ
  local_succ := X.local_succ
  measurable_succ := X.measurable_succ
  prob_succ := X.prob_succ
  Good := fun ω v => slabNestJoined n S F (sprinkleConfiguration ω) (v : Vertex 2)
  good_joined := fun _ _ h => h
  hroot := X.hroot
  hedge := X.hedge

/-- thm.slab from one-step inputs with a general invariant. -/
theorem slab_theorem_of_oneStepGood_inputs (hd : 3 ≤ d)
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
          ∀ R, Nonempty (SlabOneStepGoodInputs d n R (criticalPoint d) s
            (slabVertices d 2 n) F κ)) :
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
