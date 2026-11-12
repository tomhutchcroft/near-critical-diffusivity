module

public import NearCritical.SlabSiteProbability

/-! Site-step bound from the pre-good probability.

`cubeBlock_pregood_ge`: if `1 - η <= P_{p_c}[IsPreGoodCube typ n c]` at the
centre `c = coarseShift n v` (the form of the conclusion of
`Section10.pregood_eventually`), then the cube block law gives the event "the
block makes the cube pre-good" probability at least `1 - η`.

`cubeBlock_site_bound`: hence `κ{true} <=` that probability whenever
`κ{true} <= 1 - η`. This is the bound `psite` of the slab nest rule for the site
test `IsPreGoodCube ∘ blockConfig`.
-/

@[expose] public section
noncomputable section

namespace NearCritical

open MeasureTheory unitInterval Set ProbabilityTheory
open scoped Classical ENNReal
open Section10

variable {d : ℕ}

theorem cubeBlock_pregood_ge {n : ℕ} (hn : 0 < n) (s : I) (A : Finset (Bond d))
    (Bx : Finset (Vertex 2)) (v : Bx) (typ : TypicalParameters)
    (hA : ∀ b : Bond d, bondIn (slabCube n v.1) b → b ∈ A) {η : ℝ}
    (hpre : 1 - η ≤ ∫ ω, (if IsPreGoodCube typ n (coarseShift (d := d) n v.1) ω then (1:ℝ) else 0)
      ∂(percolation d (criticalPoint d))) :
    ENNReal.ofReal (1 - η) ≤
      Measure.pi (fun e : slabSprinkleBlocks (d := d) n A Bx (Sum.inl v) =>
          sprinkleLaw (criticalPoint d) s (e : Bond d × Bool))
        {y | IsPreGoodCube typ n (coarseShift (d := d) n v.1) (blockConfig _ y)} := by
  rw [cubeBlock_pregood_prob hn (criticalPoint d) s A Bx v typ hA]
  have hGm := measurableSet_isPreGoodCube typ n (coarseShift (d := d) n v.1)
  have heq : (fun ω : Configuration d =>
      if IsPreGoodCube typ n (coarseShift (d := d) n v.1) ω then (1:ℝ) else 0) =
      {ω | IsPreGoodCube typ n (coarseShift (d := d) n v.1) ω}.indicator (fun _ => (1:ℝ)) := by
    funext ω
    by_cases h : IsPreGoodCube typ n (coarseShift (d := d) n v.1) ω
    · rw [if_pos h, Set.indicator_of_mem (show ω ∈ {ω | IsPreGoodCube typ n _ ω} from h)]
    · rw [if_neg h, Set.indicator_of_notMem (show ω ∉ {ω | IsPreGoodCube typ n _ ω} from h)]
  rw [heq, integral_indicator_const _ hGm, smul_eq_mul, mul_one] at hpre
  calc ENNReal.ofReal (1 - η)
      ≤ ENNReal.ofReal ((percolation d (criticalPoint d)).real
          {ω | IsPreGoodCube typ n (coarseShift (d := d) n v.1) ω}) := ENNReal.ofReal_le_ofReal hpre
    _ = _ := ENNReal.ofReal_toReal (measure_ne_top _ _)

theorem cubeBlock_site_bound {n : ℕ} (hn : 0 < n) (s : I) (A : Finset (Bond d))
    (Bx : Finset (Vertex 2)) (v : Bx) (typ : TypicalParameters)
    (hA : ∀ b : Bond d, bondIn (slabCube n v.1) b → b ∈ A) {η : ℝ} (κ : Measure Bool)
    (hκ : κ {true} ≤ ENNReal.ofReal (1 - η))
    (hpre : 1 - η ≤ ∫ ω, (if IsPreGoodCube typ n (coarseShift (d := d) n v.1) ω then (1:ℝ) else 0)
      ∂(percolation d (criticalPoint d))) :
    κ {true} ≤
      Measure.pi (fun e : slabSprinkleBlocks (d := d) n A Bx (Sum.inl v) =>
          sprinkleLaw (criticalPoint d) s (e : Bond d × Bool))
        {y | IsPreGoodCube typ n (coarseShift (d := d) n v.1) (blockConfig _ y)} :=
  hκ.trans (cubeBlock_pregood_ge hn s A Bx v typ hA hpre)

end NearCritical
