module

public import NearCritical.SlabConcreteChildNest
public import NearCritical.Section10Section9Regularity

/-! The face and pointwise regularity clauses of the guard follow directly
from the way the slab rule constructs its patches in parent coordinates. -/
@[expose] public section
noncomputable section

namespace NearCritical

open Section10
open scoped Classical

theorem slab_step_patch_conditions {d : ℕ} (typ : TypicalParameters) {n : ℕ} (hn : 0 < n)
    (i : Fin d) (D : SlabStepBoundaryData d) {δ : ℝ} (hδ : typ.regularTolerance ≤ δ) :
    let S := sprinklingTargetBoundary D.parentNest (D.source typ n i)
    let T := D.childCandidates.biUnion (D.target typ n i)
    (∀ x ∈ S, x ∈ section8ExtensionPositiveFaceCore i n) ∧
    (∀ x ∈ S, sourceRegularPoint D.parentHeart (section8ExtensionSmallCube i n)
      (typicalBoundary n 0) typ.regularRadius δ x) ∧
    (∀ y ∈ T, y ∈ section8ExtensionNegativeFaceCore i n) ∧
    (∀ y ∈ T, sourceRegularPoint D.childHeart
      ((section8ExtensionSmallCube i n).image (affineReflection (Pi.single i (2*(n : ℤ)))))
      (typicalBoundary n (farCenter n 0 i)) typ.regularRadius δ y) := by
  intro S T
  have hSource (x : Vertex d) (hx : x ∈ S) :
      x ∈ typicalSplitFace n 0 (i,true) true ∧
        sourceRegularPoint D.parentHeart (typicalInnerCube n 0) (typicalBoundary n 0)
          typ.regularRadius typ.regularTolerance x := by
    obtain ⟨C, _, hxC⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨hxF,hxR⟩ := Finset.mem_filter.mp hxC
    exact ⟨(Finset.mem_inter.mp hxF).2,hxR⟩
  have hTarget (y : Vertex d) (hy : y ∈ T) :
      ∃ plus : Bool, y ∈ typicalSplitFace n (farCenter n 0 i) (i,false) plus ∧
        sourceRegularPoint D.childHeart (typicalInnerCube n (farCenter n 0 i))
          (typicalBoundary n (farCenter n 0 i)) typ.regularRadius typ.regularTolerance y := by
    obtain ⟨C, _, hyC⟩ := Finset.mem_biUnion.mp hy
    rcases Finset.mem_union.mp hyC with hyC | hyC
    · obtain ⟨hyF,hyR⟩ := Finset.mem_filter.mp hyC
      exact ⟨true,(Finset.mem_inter.mp hyF).2,hyR⟩
    · obtain ⟨hyF,hyR⟩ := Finset.mem_filter.mp hyC
      exact ⟨false,(Finset.mem_inter.mp hyF).2,hyR⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx
    exact splitFace_subset_positiveFaceCore hn i true (hSource x hx).1
  · intro x hx
    rw [← typicalInnerCube_zero_eq_smallCube hn i]
    exact sourceRegularPoint_mono hδ (hSource x hx).2
  · intro y hy
    obtain ⟨plus,hyp,_⟩ := hTarget y hy
    exact splitFace_subset_negativeFaceCore hn i plus hyp
  · intro y hy
    obtain ⟨_,_,hyr⟩ := hTarget y hy
    rw [← typicalInnerCube_far_eq_reflected hn i]
    exact sourceRegularPoint_mono hδ hyr

end NearCritical
