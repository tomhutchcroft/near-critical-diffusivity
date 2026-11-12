module

public import NearCritical.SpanningCorridor

/-! NEW lem.arm.2dspanning directional events at exact source side length
n=16m. No real-radius rounding or crossing-probability estimate is asserted. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Set
open scoped Classical

/-- Source signed coordinate x_i, with true the positive face. -/
def spanningSignedHeight {d : ℕ} (f : Fin d × Bool) (z : Vertex d) : ℤ :=
  if f.2 then z f.1 else -z f.1

/-- Source cuboid for n=16m: transverse n/8, signed height from -3n/8 to 3n. -/
def sourceSpanningCuboid {d : ℕ} (m : ℕ) (f : Fin d × Bool) : Set (Vertex d) :=
  {z | -((6*m:ℕ):ℤ) ≤ spanningSignedHeight f z ∧
    spanningSignedHeight f z ≤ ((48*m:ℕ):ℤ) ∧
      ∀ j, j ≠ f.1 → |z j| ≤ ((2*m:ℕ):ℤ)}

/-- Source target 2n e_i+[-n/8,n/8]^d at n=16m. -/
def sourceSpanningTarget {d : ℕ} (m : ℕ) (f : Fin d × Bool) : Set (Vertex d) :=
  {z | ((30*m:ℕ):ℤ) ≤ spanningSignedHeight f z ∧
    spanningSignedHeight f z ≤ ((34*m:ℕ):ℤ) ∧
      ∀ j, j ≠ f.1 → |z j| ≤ ((2*m:ℕ):ℤ)}

/-- The source narrow cuboid permits no wrong-face exit from the outer cube. -/
lemma sourceSpanningCuboid_subset_corridor {d : ℕ} (m : ℕ) (f : Fin d × Bool) :
    sourceSpanningCuboid m f ⊆ spanningCorridor (8*m) f := by
  intro z hz
  change (-((6*m:ℕ):ℤ) ≤ spanningSignedHeight f z ∧
    spanningSignedHeight f z ≤ ((48*m:ℕ):ℤ) ∧
      ∀ j, j ≠ f.1 → |z j| ≤ ((2*m:ℕ):ℤ)) at hz
  refine ⟨?_,?_⟩
  · have hlo := hz.1
    rcases f with ⟨i,s⟩
    cases s <;> simp_all [spanningSignedHeight]
    <;> omega
  · intro j hj
    exact (hz.2.2 j hj).trans (by omega)

/-- Every source target vertex lies strictly beyond the selected outer face. -/
lemma sourceSpanningTarget_subset_corridorTarget {d m : ℕ} (hm : 1 ≤ m)
    (f : Fin d × Bool) : sourceSpanningTarget m f ⊆ spanningCorridorTarget (8*m) f := by
  intro z hz
  have hlo : ((30*m:ℕ):ℤ) ≤ spanningSignedHeight f z := hz.1
  rcases f with ⟨i,s⟩
  cases s <;> simp_all [spanningSignedHeight, spanningCorridorTarget]
  <;> omega

/-- The paper's intersection of directional cuboid events implies actual
simultaneous spanning, at all positive exact integer scales n=16m. -/
theorem all_sourceSpanningCuboids_subset_spanning {d m : ℕ} (hm : 1 ≤ m)
    (x : Vertex d) (hx : x ∈ centeredBox d (8*m)) :
    {ω : Configuration d | ∀ f : Fin d × Bool,
      ω ∈ connectionToSetEvent (sourceSpanningCuboid m f) x (sourceSpanningTarget m f)} ⊆
        finiteRootSpanningEvent (centeredBox d (8*m)) (signedCubeFace d (8*m)) x := by
  apply Set.Subset.trans ?_ (all_spanningCorridors_subset_spanning x hx)
  intro ω hω f
  exact connectionToSetEvent_mono (sourceSpanningCuboid_subset_corridor m f)
    (sourceSpanningTarget_subset_corridorTarget hm f) x (hω f)

end NearCritical
