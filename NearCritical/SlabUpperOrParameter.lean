module

public import NearCritical.SlabUpperSprinkleCoupling
public import NearCritical.Section9SprinkleOrLaw

/-! Bridge between the slab sprinkle coupling and the Section 9 enrichment
parameter: `orParameter a s = a + (1-a)s` is exactly the law parameter
`σ (σ a * σ s)` of `sprinkleConfiguration`. So a Section 9 choice of `q` with
`orParameter p_c q = p_c + Λ/n²` feeds `coupledRenormalizedExploration_of_sprinkleBlocks`
with base `a = p_c` and sprinkle `s = q` directly. -/

@[expose] public section
noncomputable section

namespace NearCritical

open MeasureTheory unitInterval
open scoped ENNReal

theorem orParameter_eq_symm_mul (a s : I) : orParameter a s = σ (σ a * σ s) := by
  apply Subtype.ext
  simp only [orParameter, coe_symm_eq, Set.Icc.coe_mul]
  ring

theorem map_sprinkleConfiguration_or {d : ℕ} (a s : I) :
    Measure.map sprinkleConfiguration (Measure.infinitePi (sprinkleLaw (d := d) a s)) =
      percolation d (orParameter a s) := by
  rw [orParameter_eq_symm_mul]
  exact map_sprinkleConfiguration a s

end NearCritical
