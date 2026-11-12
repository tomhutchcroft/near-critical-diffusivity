module

public import NearCritical.MaskedSupercriticalPrior
public import NearCritical.ProfileCountableBKStrict

/-! Two-arm probability products under the actual inhomogeneous law. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Set MeasureTheory
open scoped Classical

/-- Keep both ordered products under the original independent profile.
The two disjoint-occurrence events use the source's issued-domain arms. -/
theorem profile_sourceTwoArm_le_connectionProducts {d : ℕ}
    (U : Finset (Vertex d)) (i : Fin d) (e : IssuedBond U)
    (r : Bond d → unitInterval) (P : unitInterval) (hP : (P : ℝ) < 1)
    (hr : ∀ b, r b ≤ P) :
    let μ := percolationProfile d r
    let tail := (issuedNetwork U).tail e
    let head := (issuedNetwork U).head e
    μ.real {ω | sourceTwoArm U i ω e} ≤
      μ.real (latticeBoundaryConnectionEvent U tail (negativeFace U i)) *
        μ.real (latticeBoundaryConnectionEvent U head (positiveFace U i)) +
      μ.real (latticeBoundaryConnectionEvent U tail (positiveFace U i)) *
        μ.real (latticeBoundaryConnectionEvent U head (negativeFace U i)) := by
  dsimp only
  let A : Set (Configuration d) := {ω | DisjointOccurrence
    (latticeBoundaryConnectionEvent U ((issuedNetwork U).tail e) (negativeFace U i))
    (latticeBoundaryConnectionEvent U ((issuedNetwork U).head e) (positiveFace U i)) ω}
  let B : Set (Configuration d) := {ω | DisjointOccurrence
    (latticeBoundaryConnectionEvent U ((issuedNetwork U).tail e) (positiveFace U i))
    (latticeBoundaryConnectionEvent U ((issuedNetwork U).head e) (negativeFace U i)) ω}
  have heq : {ω | sourceTwoArm U i ω e} = A ∪ B := rfl
  rw [heq]
  exact (measureReal_union_le A B).trans (add_le_add
    (percolationProfile_bk_of_uniform_lt_one d r P hP hr _ _
      (latticeBoundaryConnectionEvent_increasing U _ _)
      (latticeBoundaryConnectionEvent_increasing U _ _))
    (percolationProfile_bk_of_uniform_lt_one d r P hP hr _ _
      (latticeBoundaryConnectionEvent_increasing U _ _)
      (latticeBoundaryConnectionEvent_increasing U _ _)))

/-- The source two-arm probability under the bulk law is bounded by the
sum of the two face products under that same law. -/
theorem bulk_sourceTwoArm_le_connectionProducts {d : ℕ}
    (U : Finset (Vertex d)) (i : Fin d) (h δ : ℝ) (p q P : unitInterval)
    (hP : (P : ℝ) < 1) (hpP : p ≤ P) (hqP : q ≤ P) (e : IssuedBond U) :
    let μ := bulkPercolation U i h δ p q
    let tail := (issuedNetwork U).tail e
    let head := (issuedNetwork U).head e
    μ.real {ω | sourceTwoArm U i ω e} ≤
      μ.real (latticeBoundaryConnectionEvent U tail (negativeFace U i)) *
        μ.real (latticeBoundaryConnectionEvent U head (positiveFace U i)) +
      μ.real (latticeBoundaryConnectionEvent U tail (positiveFace U i)) *
        μ.real (latticeBoundaryConnectionEvent U head (negativeFace U i)) := by
  exact profile_sourceTwoArm_le_connectionProducts U i e
    (fun b => if b ∈ internalBondSet (bulkVertices U i h δ) then q else p)
    P hP (fun b => by split <;> assumption)

end NearCritical
