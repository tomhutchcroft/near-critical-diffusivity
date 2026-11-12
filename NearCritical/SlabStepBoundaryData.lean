module

public import NearCritical.SlabChartCubes
public import NearCritical.SlabRootSite

/-! The edge rule gets its source clusters and reveal set from the stored
parent nest, and gets its target clusters and reveal set from the target block.
Both sets of data are placed in the chart of the edge. -/
@[expose] public section
noncomputable section

namespace NearCritical

open Section10
open scoped Classical

/-- A regular patch uses the heart union of the cube, which is stored in
the nest so that the parent cube block need not be read again. -/
def slabRegularPatch {d : ℕ} (typ : TypicalParameters) (n : ℕ) (c : Vertex d)
    (F C : Finset (Vertex d)) (face : Fin d × Bool) (plus : Bool) : Finset (Vertex d) :=
  (C ∩ typicalSplitFace n c face plus).filter
    (sourceRegularPoint F (typicalInnerCube n c) (typicalBoundary n c)
      typ.regularRadius typ.regularTolerance)

theorem slabRegularPatch_eq_typical {d : ℕ} (typ : TypicalParameters) (n : ℕ) (c : Vertex d)
    (ω : Configuration d) (C : Finset (Vertex d)) (face : Fin d × Bool) (plus : Bool) :
    slabRegularPatch typ n c (heartClusterUnion ω (typicalCube n c)
      (typicalHeart n c typ.heartRatio)) C face plus = typicalRegularPatch typ n c ω C face plus :=
  rfl

/-- A chart changes the vertex sets of clusters without changing their
cardinality or identifying distinct clusters. -/
def chartCluster {d : ℕ} (φ : Vertex d ≃ Vertex d) (C : Finset (Vertex d)) : Finset (Vertex d) :=
  C.map φ.toEmbedding

theorem chartCluster_injective {d : ℕ} (φ : Vertex d ≃ Vertex d) :
    Function.Injective (chartCluster φ) :=
  Finset.map_injective _

theorem chartCluster_symm {d : ℕ} (φ : Vertex d ≃ Vertex d) (C : Finset (Vertex d)) :
    chartCluster φ.symm (chartCluster φ C) = C := by
  ext x
  simp [chartCluster, Finset.mem_map, Equiv.symm_apply_eq]

structure SlabStepBoundaryData (d : ℕ) where
  parentHeart : Finset (Vertex d)
  childHeart : Finset (Vertex d)
  parentNest : Finset (Finset (Vertex d))
  childCandidates : Finset (Finset (Vertex d))

/-- The endpoint target determines whether the parent is the tip. -/
def slabEdgeReverse {R : ℕ} (e : boxBonds (centeredBox 2 R)) (z : centeredBox 2 R) : Bool :=
  decide (z.1 = e.1.1)

/-- Exact parent and target data read by the edge rule. -/
def slabStepBoundaryData {d : ℕ} (hd : 2 ≤ d) (n R : ℕ) (A : Finset (Bond d))
    (typ : TypicalParameters) (e : boxBonds (centeredBox 2 R)) (z : centeredBox 2 R)
    (ℓ : SlabNest d) (x : ∀ i, rsΩ d n A R i) : SlabStepBoundaryData d :=
  let φ := (slabChartEquiv hd n e.1 (slabEdgeReverse e z)).symm
  let c := coarseShift n z.1
  let ω := slabCubeConfig d n A R x z
  { parentHeart := chartCluster φ ℓ.2
    childHeart := chartCluster φ (heartClusterUnion ω (typicalCube n c) (typicalHeart n c typ.heartRatio))
    parentNest := ℓ.1.image (chartCluster φ)
    childCandidates := (typicalClusterFamily typ n c ω).image (chartCluster φ) }

theorem slabStepBoundaryData_local {d : ℕ} (hd : 2 ≤ d) (n R : ℕ) (A : Finset (Bond d))
    (typ : TypicalParameters) (e : boxBonds (centeredBox 2 R)) (z : centeredBox 2 R)
    (ℓ : SlabNest d) (x x' : ∀ i, rsΩ d n A R i)
    (h : x (Sum.inl z) = x' (Sum.inl z)) :
    slabStepBoundaryData hd n R A typ e z ℓ x = slabStepBoundaryData hd n R A typ e z ℓ x' := by
  unfold slabStepBoundaryData slabCubeConfig
  rw [h]

end NearCritical
