module

public import NearCritical.SlabUpperAssembly
public import NearCritical.SlabUpperBlockLaw
public import NearCritical.SlabUpperMixedPlanar

/-! Constructor for the per-box renormalisation data of prop.slab.upper.

The coarse lattice is `ℤ²` (cube centres `2nℤ²×{0}^{d-2}` up to scaling); the
box graph `Bx ∋ 0` is the finite ℤ² box graph of `SlabUpperMixedPlanar`.
Supplying
* pairwise-disjoint bond blocks `B` (one per coarse site = cube, one per coarse
  bond = tube) — the block law is then PROVED (`percolation_map_blockRestrict`);
* the infinite-volume grimmett1999 input at law `κ` — `mixed_ge` is then PROVED
  (`mixedValue_box_ge`);
* the success rule with its locality, measurability and conditional bound
  (prop.regular_cube / prop.sprinkling.AB.disjoint) and the nest semantics `good`,
gives `RenormalizedExploration`. Only the last bullet remains for the source
renormalisation. -/

@[expose] public section
noncomputable section

namespace NearCritical

open MeasureTheory ProbabilityTheory
open scoped ENNReal

theorem renormalizedExploration_of_blocks {d : ℕ} (p : unitInterval) (S : Set (Vertex d))
    (F : Finset (Vertex d)) (N : ℕ) (Bx : Finset (Vertex 2)) (h0 : (0 : Vertex 2) ∈ Bx)
    (B : Bx ⊕ boxBonds Bx → Finset (Bond d))
    (hB : Pairwise fun i j => Disjoint (B i) (B j))
    (κ : Measure Bool) [IsProbabilityMeasure κ] {θ : ℝ≥0∞}
    (hθ : MixedSiteBondPercolationInput 2 κ θ)
    (succ : ExploreState Bx (boxBonds Bx) → (∀ i, B i → Bool) → Bool)
    (local_succ : ∀ σ i (x x' : ∀ j, B j → Bool),
      ExploreInv (boxEnds Bx) (⟨0, h0⟩ : Bx) σ →
      exploreQuery (boxEnds Bx) (⟨0, h0⟩ : Bx) σ = some i →
      (∀ j ∈ insert i (exploreRevealed σ), x j = x' j) → succ σ x = succ σ x')
    (measurable_succ : ∀ σ, Measurable (succ σ))
    (prob_succ : ∀ σ i (x : ∀ j, B j → Bool),
      ExploreInv (boxEnds Bx) (⟨0, h0⟩ : Bx) σ →
      exploreQuery (boxEnds Bx) (⟨0, h0⟩ : Bx) σ = some i →
      κ {true} ≤ Measure.pi (fun _ : B i => bernoulliMeasure true false p)
        {y | succ σ (Function.update x i y) = true})
    (good : ∀ ω, explorePayoff (boxInnerBoundary Bx)
      (adaptiveRun (exploreQuery (boxEnds Bx) (⟨0, h0⟩ : Bx))
        (exploreNext (boxEnds Bx) (⟨0, h0⟩ : Bx)) succ
        (Fintype.card (Bx ⊕ boxBonds Bx)) ⟨∅, ∅, ∅, ∅, ∅⟩ (blockRestrict B ω)) ≠ 0 →
      ω ∈ restrictedReachFarEvent S F N) :
    Nonempty (RenormalizedExploration d p S F N θ) :=
  ⟨{ Vx := Bx
     Ed := boxBonds Bx
     ends := boxEnds Bx
     root := ⟨0, h0⟩
     target := boxInnerBoundary Bx
     Ω := fun i => B i → Bool
     ν := fun i => Measure.pi (fun _ : B i => bernoulliMeasure true false p)
     κ := κ
     Φ := blockRestrict B
     measurable_Φ := measurable_blockRestrict B
     map_Φ := percolation_map_blockRestrict p B hB
     succ := succ
     local_succ := local_succ
     measurable_succ := measurable_succ
     prob_succ := prob_succ
     good := good
     mixed_ge := mixedValue_box_ge Bx h0 κ hθ }⟩

end NearCritical
