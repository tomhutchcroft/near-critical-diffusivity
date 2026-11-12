module

public import NearCritical.NestRegularBoundary
public import NearCritical.SpanningBoundaryDiameter
public import NearCritical.ConductivityTranslation

/-! Literal finite Section10 typical clusters and pre-good cubes.
The mesh is ell0=2t. These are actual configuration observables, with locality
in the internal critical BONDS; no vertex-union measurability is asserted.
Probability estimates and selection of uniform constants remain separate. -/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open scoped Classical

/-- Source Q=Lambda_t(z), using strict coordinate cuts, including even t.
The ambient radius t only makes the defining set finite. -/
def typicalCube {d : ℕ} (t : ℕ) (z : Vertex d) : Finset (Vertex d) :=
  (translateSites z (centeredBox d t)).filter fun x =>
    ∀ j, 2 * |((x j - z j : ℤ) : ℝ)| < (t : ℝ)

/-- Source S=Lambda_(3t/4)(z). -/
def typicalInnerCube {d : ℕ} (t : ℕ) (z : Vertex d) : Finset (Vertex d) :=
  (typicalCube t z).filter fun x =>
    ∀ j, 8 * |((x j - z j : ℤ) : ℝ)| < 3 * (t : ℝ)

/-- Source H=Lambda_(cc*t)(z), for the source range 0<cc<1. -/
def typicalHeart {d : ℕ} (t : ℕ) (z : Vertex d) (cc : ℝ) : Finset (Vertex d) :=
  (typicalCube t z).filter fun x =>
    ∀ j, 2 * |((x j - z j : ℤ) : ℝ)| < cc * (t : ℝ)

/-- Signed actual integer face; the extremal offset is floor((t-1)/2).
The outer cube filter keeps the t=0 empty-cube convention. -/
def typicalFace {d : ℕ} (t : ℕ) (z : Vertex d) (face : Fin d × Bool) :
    Finset (Vertex d) :=
  (typicalCube t z).filter fun x =>
    x face.1 - z face.1 = if face.2 then (((t-1)/2 : ℕ) : ℤ) else -(((t-1)/2 : ℕ) : ℤ)

def typicalBoundary {d : ℕ} (t : ℕ) (z : Vertex d) : Finset (Vertex d) :=
  Finset.univ.biUnion (typicalFace t z)

/-- Source split subface: t/8<offset<t/4, or -t/4<offset<-t/8,
in EVERY transverse coordinate. The split sign is independent of face sign. -/
def typicalSplitFace {d : ℕ} (t : ℕ) (z : Vertex d)
    (face : Fin d × Bool) (plus : Bool) : Finset (Vertex d) :=
  (typicalFace t z face).filter fun x => ∀ j, j ≠ face.1 →
    if plus then
      (t : ℝ) < 8 * ((x j - z j : ℤ) : ℝ) ∧
        4 * ((x j - z j : ℤ) : ℝ) < (t : ℝ)
    else
      -(t : ℝ) < 4 * ((x j - z j : ℤ) : ℝ) ∧
        8 * ((x j - z j : ℤ) : ℝ) < -(t : ℝ)

/-- The source constants are raw parameters here; their positivity, choice
before scales, and uniform probability estimates have not been assumed. -/
structure TypicalParameters where
  regularRadius : ℕ
  heartRatio : ℝ
  regularTolerance : ℝ
  volumeLower : ℝ
  volumeUpper : ℝ
  boundaryLower : ℝ
  boundaryUpper : ℝ
  diameterUpper : ℝ
  countLower : ℝ
  countUpper : ℝ

/-- Regularity uses the WHOLE union fC of heart-touching critical components. -/
def typicalRegularPatch {d : ℕ} (a : TypicalParameters) (t : ℕ) (z : Vertex d)
    (ω : Configuration d) (C : Finset (Vertex d)) (face : Fin d × Bool)
    (plus : Bool) : Finset (Vertex d) :=
  (C ∩ typicalSplitFace t z face plus).filter
    (sourceRegularPoint (heartClusterUnion ω (typicalCube t z)
      (typicalHeart t z a.heartRatio)) (typicalInnerCube t z)
        (typicalBoundary t z) a.regularRadius a.regularTolerance)

/-- All five conditions of def.spanning.z, in addition to C being an actual
component contained in fC. rin is the distinct-face boundary diameter. -/
def IsTypicalCluster {d : ℕ} (a : TypicalParameters) (t : ℕ) (z : Vertex d)
    (ω : Configuration d) (C : Finset (Vertex d)) : Prop :=
  C ⊆ heartClusterUnion ω (typicalCube t z) (typicalHeart t z a.heartRatio) ∧
  (∀ face : Fin d × Bool, (C ∩ typicalFace t z face).Nonempty) ∧
  a.volumeLower * (2 * (t : ℝ))^4 < (C.card : ℝ) ∧
  (C.card : ℝ) < a.volumeUpper * (2 * (t : ℝ))^4 ∧
  (spanningFaceDiameter (restrictedGraph ω (typicalCube t z : Set (Vertex d)))
    C (typicalFace t z) : ℝ) ≤ a.diameterUpper * (2 * (t : ℝ))^2 ∧
  (∀ (face : Fin d × Bool) (plus : Bool),
    a.boundaryLower * (2 * (t : ℝ))^2 ≤ (typicalRegularPatch a t z ω C face plus).card ∧
    ((typicalRegularPatch a t z ω C face plus).card : ℝ) ≤
      a.boundaryUpper * (2 * (t : ℝ))^2) ∧
  (∀ face : Fin d × Bool,
    ((C ∩ typicalFace t z face).card : ℝ) ≤ a.boundaryUpper * (2 * (t : ℝ))^2)

/-- Deduplicated actual components, not a count of roots. -/
def typicalClusterFamily {d : ℕ} (a : TypicalParameters) (t : ℕ) (z : Vertex d)
    (ω : Configuration d) : Finset (Finset (Vertex d)) :=
  (finiteClusterFamily ω (typicalCube t z)).filter (IsTypicalCluster a t z ω)

/-- Source def.pregood. The natural exponent d-6 is used in the source range
d>=6; small dimensions are not asserted to satisfy any source estimate. -/
def IsPreGoodCube {d : ℕ} (a : TypicalParameters) (t : ℕ) (z : Vertex d)
    (ω : Configuration d) : Prop :=
  a.countLower * (2 * (t : ℝ))^(d-6) ≤ (typicalClusterFamily a t z ω).card ∧
  ((typicalClusterFamily a t z ω).card : ℝ) ≤ a.countUpper * (2 * (t : ℝ))^(d-6)

def preGoodIndicator {d : ℕ} (a : TypicalParameters) (t : ℕ) (z : Vertex d)
    (ω : Configuration d) : ℝ := if IsPreGoodCube a t z ω then 1 else 0

theorem mem_typicalClusterFamily {d : ℕ} (a : TypicalParameters) (t : ℕ)
    (z : Vertex d) (ω : Configuration d) (C : Finset (Vertex d)) :
    C ∈ typicalClusterFamily a t z ω ↔
      C ∈ finiteClusterFamily ω (typicalCube t z) ∧ IsTypicalCluster a t z ω C := by
  simp only [typicalClusterFamily, Finset.mem_filter]

/-- Finite decorated critical reveal locality, with no claim of locality in
the vertex union alone. Includes intrinsic graph distance and both energies. -/
theorem typicalClusterFamily_eq_of_internal_agree {d : ℕ} (a : TypicalParameters)
    (t : ℕ) (z : Vertex d) (ω η : Configuration d)
    (hagree : ∀ e ∈ internalBondSet (typicalCube t z), ω e = η e) :
    typicalClusterFamily a t z ω = typicalClusterFamily a t z η := by
  have hG := restrictedGraph_eq_of_internalBondSet_agree (typicalCube t z)
    (typicalCube t z : Set (Vertex d)) (by intro x hx; exact hx) ω η hagree
  have hF := heartClusterUnion_eq_of_internal_agree (typicalCube t z) (typicalCube t z)
    (typicalHeart t z a.heartRatio) (by intro x hx; exact hx) ω η hagree
  have hclusters : finiteClusterFamily ω (typicalCube t z) =
      finiteClusterFamily η (typicalCube t z) := by
    have hfun : finiteBoxCluster ω (typicalCube t z) = finiteBoxCluster η (typicalCube t z) := by
      funext root
      exact finiteBoxCluster_eq_of_internal_agree (typicalCube t z) (typicalCube t z)
        (by intro x hx; exact hx) ω η hagree root
    simp only [finiteClusterFamily, hfun]
  unfold typicalClusterFamily
  rw [hclusters]
  apply Finset.filter_congr
  intro C _
  simp only [IsTypicalCluster, typicalRegularPatch, hG, hF]

theorem isPreGoodCube_iff_of_internal_agree {d : ℕ} (a : TypicalParameters)
    (t : ℕ) (z : Vertex d) (ω η : Configuration d)
    (hagree : ∀ e ∈ internalBondSet (typicalCube t z), ω e = η e) :
    IsPreGoodCube a t z ω ↔ IsPreGoodCube a t z η := by
  simp only [IsPreGoodCube, typicalClusterFamily_eq_of_internal_agree a t z ω η hagree]

/-- Exact reconstruction from the finite internal critical bond mask. -/
theorem isPreGoodCube_reconstruct {d : ℕ} (a : TypicalParameters)
    (t : ℕ) (z : Vertex d) (ω : Configuration d) :
    IsPreGoodCube a t z ω ↔ IsPreGoodCube a t z
      (reconstructInterior (typicalCube t z) ((internalBondSet (typicalCube t z)).restrict ω)) :=
  isPreGoodCube_iff_of_internal_agree a t z ω _
    (reconstructInterior_restrict_agree (typicalCube t z) ω)

end NearCritical.Section10
