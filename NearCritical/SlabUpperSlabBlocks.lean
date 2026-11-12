module

public import NearCritical.SlabUpperBlockGeometry
public import NearCritical.SlabUpperOrParameter
public import NearCritical.SlabUpperCoupled

/-! prop.slab.upper with the source block geometry and the Section 9 parameter
fixed. The block family is the literal `slabSprinkleBlocks n A Bx` (cube base bits,
tube sprinkle bits, tube base bits outside the box cubes), whose disjointness is
proved in `SlabUpperBlockGeometry`, and the law parameter is the
`orParameter a s = a + (1-a)s`. What remains as input is ONLY the per-step
exploration data on these blocks: locality, measurability, the per-step success
bound `κ{true} ≤ ν_i{succ}` (source prop.sprinkling.AB.disjoint + prop.regular_cube),
the nest semantics `good`, and the cited planar mixed input (grimmett1999). -/

@[expose] public section
noncomputable section

namespace NearCritical

open MeasureTheory unitInterval
open scoped ENNReal Classical

variable {d : ℕ}

/-- Coupled renormalisation data from the literal slab blocks at parameter
`orParameter a s`. -/
theorem coupledRenormalizedExploration_of_slabBlocks (hd : 2 ≤ d) {n : ℕ} (hn : 0 < n)
    (a s : I) (S : Set (Vertex d)) (F : Finset (Vertex d)) (N : ℕ)
    (A : Finset (Bond d)) (Bx : Finset (Vertex 2)) (h0 : (0 : Vertex 2) ∈ Bx)
    (κ : Measure Bool) [IsProbabilityMeasure κ] {θ : ℝ≥0∞}
    (hθ : MixedSiteBondPercolationInput 2 κ θ)
    (succ : ExploreState Bx (boxBonds Bx) →
      (∀ i, slabSprinkleBlocks (d := d) n A Bx i → Bool) → Bool)
    (local_succ : ∀ st i (x x' : ∀ j, slabSprinkleBlocks (d := d) n A Bx j → Bool),
      ExploreInv (boxEnds Bx) (⟨0, h0⟩ : Bx) st →
      exploreQuery (boxEnds Bx) (⟨0, h0⟩ : Bx) st = some i →
      (∀ j ∈ insert i (exploreRevealed st), x j = x' j) → succ st x = succ st x')
    (measurable_succ : ∀ st, Measurable (succ st))
    (prob_succ : ∀ st i (x : ∀ j, slabSprinkleBlocks (d := d) n A Bx j → Bool),
      ExploreInv (boxEnds Bx) (⟨0, h0⟩ : Bx) st →
      exploreQuery (boxEnds Bx) (⟨0, h0⟩ : Bx) st = some i →
      κ {true} ≤ Measure.pi (fun e : slabSprinkleBlocks (d := d) n A Bx i =>
          sprinkleLaw a s (e : Bond d × Bool))
        {y | succ st (Function.update x i y) = true})
    (good : ∀ ω : Bond d × Bool → Bool, explorePayoff (boxInnerBoundary Bx)
      (adaptiveRun (exploreQuery (boxEnds Bx) (⟨0, h0⟩ : Bx))
        (exploreNext (boxEnds Bx) (⟨0, h0⟩ : Bx)) succ
        (Fintype.card (Bx ⊕ boxBonds Bx)) ⟨∅, ∅, ∅, ∅, ∅⟩
        (blockFamily (slabSprinkleBlocks (d := d) n A Bx) ω)) ≠ 0 →
      sprinkleConfiguration ω ∈ restrictedReachFarEvent S F N) :
    Nonempty (CoupledRenormalizedExploration d (orParameter a s) S F N θ) :=
  coupledRenormalizedExploration_of_sprinkleBlocks a s (orParameter a s)
    (orParameter_eq_symm_mul a s) S F N Bx h0 (slabSprinkleBlocks n A Bx)
    (slabSprinkleBlocks_disjoint hd hn A Bx) κ hθ succ local_succ measurable_succ
    prob_succ good

end NearCritical
