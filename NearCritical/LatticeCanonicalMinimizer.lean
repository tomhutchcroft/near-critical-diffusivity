module

public import NearCritical.LatticeDifferential
public import NearCritical.LatticeFaces
public import NearCritical.LatticePivotal
public import NearCritical.NetworkCanonicalMinimizer
public import NearCritical.AuxiliaryChoiceIndependence

/-! Exact source convention for the finite-volume minimizer: on boundary-free
components use the arithmetic average over ALL two-face boundary vertices.
This need not be the midpoint of the two face values. The two-arm auxiliary
term is proved independent of the original arbitrary selection of minimizers. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Set MeasureTheory
open scoped Classical

def sourceMinimizer {d : ℕ} (U : Finset (Vertex d)) (i : Fin d)
    (η : IssuedBond U → Bool) : DomainVertex U → ℝ :=
  (issuedNetwork U).boundaryAverageMinimizer (Network.binaryWeights_nonneg η)
    (twoFaceBoundary U i) (coordinateData i)

lemma sourceMinimizer_spec {d : ℕ} (U : Finset (Vertex d)) (i : Fin d) (η : IssuedBond U → Bool) :
    (issuedNetwork U).IsMinimizer (Network.binaryWeights η) (twoFaceBoundary U i)
      (coordinateData i) (sourceMinimizer U i η) :=
  (issuedNetwork U).boundaryAverageMinimizer_spec (Network.binaryWeights_nonneg η) _ _

lemma sourceMinimizer_boundary_free {d : ℕ} (U : Finset (Vertex d)) (i : Fin d)
    (η : IssuedBond U → Bool) (x : DomainVertex U)
    (hx : ¬(issuedNetwork U).HasBoundaryAccess (Network.binaryWeights η) (twoFaceBoundary U i) x) :
    sourceMinimizer U i η x = Network.boundaryDataAverage (twoFaceBoundary U i) (coordinateData i) :=
  (issuedNetwork U).boundaryAverageMinimizer_eq_constant (Network.binaryWeights_nonneg η) _ _ hx

/-- The source-prescribed selector has the full maximum-principle gradient bound. -/
lemma sourceMinimizer_gradient_bound {d : ℕ} {U : Finset (Vertex d)}
    {i : Fin d} {l h : DomainVertex U} (hl : l ∈ negativeFace U i) (hh : h ∈ positiveFace U i)
    (η : IssuedBond U → Bool) (e : IssuedBond U) :
    |(issuedNetwork U).gradient (sourceMinimizer U i η) e| ≤ coordinateData i h - coordinateData i l := by
  have hne : (twoFaceBoundary U i).Nonempty := by
    refine ⟨l, ?_⟩
    rw [twoFaceBoundary_eq_union]
    exact Or.inl hl
  exact (issuedNetwork U).boundaryAverageMinimizer_gradient_abs_le
    (Network.binaryWeights_nonneg η) (twoFaceBoundary U i) (coordinateData i) hne
    (fun x _ ↦ face_data_range hl hh x) e

/-- Each local b summand may use ANY same-data minimizer. On its support both
endpoints are boundary-connected, so even its closed-edge voltage is unique. -/
theorem localB_eq_for_minimizer {d : ℕ} (U : Finset (Vertex d)) (i : Fin d)
    (η : IssuedBond U → Bool) (u : DomainVertex U → ℝ)
    (hu : (issuedNetwork U).IsMinimizer (Network.binaryWeights η) (twoFaceBoundary U i)
      (coordinateData i) u) :
    localB U i η = (U.card : ℝ)⁻¹ * ∑ e,
      (1 - Network.binaryWeights η e) * ((issuedNetwork U).gradient u e) ^ 2 *
        if localTwoArm U i η e then 1 else 0 := by
  classical
  unfold localB
  congr 1
  apply Finset.sum_congr rfl
  intro e _
  by_cases hs : localTwoArm U i η e
  · have hmin := (issuedNetwork U).binaryMinimizer_spec (twoFaceBoundary U i) (coordinateData i) η
    have hmin' : (issuedNetwork U).IsMinimizer (Network.binaryWeights η)
        (negativeFace U i ∪ positiveFace U i) (coordinateData i)
        ((issuedNetwork U).binaryMinimizer (twoFaceBoundary U i) (coordinateData i) η) := by
      rw [← twoFaceBoundary_eq_union]
      exact hmin
    rw [twoFaceBoundary_eq_union] at hu
    have hg := (issuedNetwork U).gradient_choice_independent_on_two_arm hmin' hu hs
    rw [hg]
  · simp [hs]

/-- In particular the implemented b equals the paper's literal boundary-average
selector, rather than depending on arbitrary constants on free components. -/
theorem localB_eq_sourceMinimizer {d : ℕ} (U : Finset (Vertex d)) (i : Fin d)
    (η : IssuedBond U → Bool) :
    localB U i η = (U.card : ℝ)⁻¹ * ∑ e,
      (1 - Network.binaryWeights η e) *
        ((issuedNetwork U).gradient (sourceMinimizer U i η) e) ^ 2 *
          if localTwoArm U i η e then 1 else 0 :=
  localB_eq_for_minimizer U i η _ (sourceMinimizer_spec U i η)

/-- The literal source integrand in `eq.defbb`: original minimizer with the
boundary-average convention and the source circle events on all lattice bonds. -/
def sourceQuenchedB {d : ℕ} (U : Finset (Vertex d)) (i : Fin d) (ω : Configuration d) : ℝ :=
  (U.card : ℝ)⁻¹ * ∑ e,
    (1 - domainWeights ω e) *
      ((issuedNetwork U).gradient (sourceMinimizer U i ((issuedBondSet U).restrict ω)) e) ^ 2 *
        if sourceTwoArm U i ω e then 1 else 0

theorem quenchedB_eq_sourceQuenchedB {d : ℕ} (U : Finset (Vertex d)) (i : Fin d)
    (ω : Configuration d) : quenchedB U i ω = sourceQuenchedB U i ω := by
  classical
  rw [quenchedB, localB_eq_sourceMinimizer]
  unfold sourceQuenchedB
  congr 1
  apply Finset.sum_congr rfl
  intro e _
  rw [← propext (localTwoArm_iff_sourceTwoArm U i ω e)]
  rfl

/-- Complete identification of the implemented b with the source convention,
including the original infinite-product probability measure. -/
theorem annealedB_eq_sourceIntegral {d : ℕ} (U : Finset (Vertex d)) (i : Fin d)
    (p : unitInterval) :
    annealedB U i (p : ℝ) = ∫ ω, sourceQuenchedB U i ω ∂percolation d p := by
  rw [annealedB_eq_integral]
  simp_rw [quenchedB_eq_sourceQuenchedB]

end NearCritical
