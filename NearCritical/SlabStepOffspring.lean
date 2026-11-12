module

public import NearCritical.SlabStepBlockCoverage
public import NearCritical.SlabResampledNestInputs

/-! The offspring selected by the slab rule uses the actual Section 9
unexplored graphs and opened middle pivots. -/
@[expose] public section
noncomputable section

namespace NearCritical

open MeasureTheory unitInterval Section10
open scoped Classical

/-- The pair of configurations available from the block of a coarse edge. -/
def slabTubePair {d : ℕ} (n : ℕ) (A : Finset (Bond d)) (R : ℕ)
    (e : boxBonds (centeredBox 2 R)) (y : rsΩ d n A R (Sum.inr e)) :
    Configuration d × Configuration d :=
  let B₁ := slabSprinkleBlocks n A (centeredBox 2 R) (Sum.inr e)
  let B₂ := slabStripBlocks n A (centeredBox 2 R) (Sum.inr e)
  (criticalLayer (tubeLayers B₁ B₂ y), sprinkleLayer (tubeLayers B₁ B₂ y))

/-- All target clusters reached by an opened middle pivot. -/
def slabStepOffspring {d : ℕ} (M L R Q₁ F₁ Q₃ F₃ S : Finset (Vertex d))
    (cand : Finset (Finset (Vertex d))) (patch : Finset (Vertex d) → Finset (Vertex d))
    (z : Configuration d × Configuration d) : Finset (Finset (Vertex d)) :=
  let v := stepView M L R Q₁ F₁ Q₃ F₃ z
  sprinklingOffspring v.1 v.2.1 S cand patch (v.2.2.1 S (sprinklingTargetBoundary cand patch))

theorem slabStepOffspring_readsOnly {d : ℕ} (M L R Q₁ F₁ Q₃ F₃ S : Finset (Vertex d))
    (cand : Finset (Finset (Vertex d))) (patch : Finset (Vertex d) → Finset (Vertex d)) :
    ReadsOnly (stepReadSet M L R Q₁ F₁ Q₃ F₃) (slabStepOffspring M L R Q₁ F₁ Q₃ F₃ S cand patch) :=
  (stepView_readsOnly M L R Q₁ F₁ Q₃ F₃).comp
    (fun v => sprinklingOffspring v.1 v.2.1 S cand patch
      (v.2.2.1 S (sprinklingTargetBoundary cand patch)))

/-- Transfer the failure estimate for the concrete offspring count to the
law of the edge block. The right and left halves can be supplied in either
order, as required by the direction of exploration. -/
theorem slab_edge_offspring_failure_eq {d : ℕ} (n : ℕ) (A : Finset (Bond d)) (R : ℕ)
    (e : boxBonds (centeredBox 2 R)) (a s : I)
    (M L V Q₁ F₁ Q₃ F₃ S : Finset (Vertex d))
    (hM : (M : Set (Vertex d)) ⊆ slabTube n e.1.1 e.1.2)
    (hL : (L : Set (Vertex d)) ⊆ slabTube n e.1.1 e.1.2)
    (hV : (V : Set (Vertex d)) ⊆ slabTube n e.1.1 e.1.2)
    (hA : ∀ b, bondIn (slabTube n e.1.1 e.1.2) b → b ∈ A)
    (cand : Finset (Finset (Vertex d))) (patch : Finset (Vertex d) → Finset (Vertex d)) (N : ℕ) :
    (rsν d n A R a s (Sum.inr e)).real
      {y | ¬ N ≤ (slabStepOffspring M L V Q₁ F₁ Q₃ F₃ S cand patch (slabTubePair n A R e y)).card} =
    ((percolation d a).prod (percolation d s)).real
      {z | ¬ N ≤ (slabStepOffspring M L V Q₁ F₁ Q₃ F₃ S cand patch z).card} := by
  exact congrArg ENNReal.toReal
    (slab_stepBlock_prob_eq_prod n A (centeredBox 2 R) e a s M L V Q₁ F₁ Q₃ F₃ hM hL hV hA
      (fun z => ¬ N ≤ (slabStepOffspring M L V Q₁ F₁ Q₃ F₃ S cand patch z).card)
      ((slabStepOffspring_readsOnly M L V Q₁ F₁ Q₃ F₃ S cand patch).comp
        (fun children => ¬ N ≤ children.card)))

end NearCritical
