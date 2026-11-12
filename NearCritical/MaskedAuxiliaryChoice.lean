module

public import NearCritical.LatticeCanonicalMinimizer

/-! The masked auxiliary uses exactly the source's original-configuration
boundary-average minimizer. On two-arm support its voltage agrees with every
same-data minimizer, even if the tested bond is closed. No Bulk import is needed. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Finset
open scoped Classical

/-- Termwise choice independence retains the OLD configuration's two-arm event;
no equality of voltages off that support, or tested-edge openness, is assumed. -/
theorem auxiliarySummand_eq_for_minimizer {d : ℕ} (U : Finset (Vertex d)) (i : Fin d)
    (η : IssuedBond U → Bool) (u : DomainVertex U → ℝ)
    (hu : (issuedNetwork U).IsMinimizer (Network.binaryWeights η) (twoFaceBoundary U i)
      (coordinateData i) u) (e : IssuedBond U) :
    (1 - Network.binaryWeights η e) *
        ((issuedNetwork U).gradient
          ((issuedNetwork U).binaryMinimizer (twoFaceBoundary U i) (coordinateData i) η) e)^2 *
        (if localTwoArm U i η e then 1 else 0) =
      (1 - Network.binaryWeights η e) * ((issuedNetwork U).gradient u e)^2 *
        (if localTwoArm U i η e then 1 else 0) := by
  by_cases hs : localTwoArm U i η e
  · have hmin := (issuedNetwork U).binaryMinimizer_spec (twoFaceBoundary U i) (coordinateData i) η
    have hmin' : (issuedNetwork U).IsMinimizer (Network.binaryWeights η)
        (negativeFace U i ∪ positiveFace U i) (coordinateData i)
        ((issuedNetwork U).binaryMinimizer (twoFaceBoundary U i) (coordinateData i) η) := by
      rw [← twoFaceBoundary_eq_union]
      exact hmin
    rw [twoFaceBoundary_eq_union] at hu
    rw [(issuedNetwork U).gradient_choice_independent_on_two_arm hmin' hu hs]
  · simp [hs]

/-- Restricting the edge SUM does not change the underlying full-domain
minimizer, its boundary data, or the original two-arm support. -/
theorem maskedAuxiliary_eq_for_minimizer {d : ℕ} (U : Finset (Vertex d)) (i : Fin d)
    (M : Finset (IssuedBond U)) (η : IssuedBond U → Bool) (u : DomainVertex U → ℝ)
    (hu : (issuedNetwork U).IsMinimizer (Network.binaryWeights η) (twoFaceBoundary U i)
      (coordinateData i) u) :
    (U.card : ℝ)⁻¹ * (∑ e ∈ M,
      (1 - Network.binaryWeights η e) *
        ((issuedNetwork U).gradient
          ((issuedNetwork U).binaryMinimizer (twoFaceBoundary U i) (coordinateData i) η) e)^2 *
        (if localTwoArm U i η e then 1 else 0)) =
      (U.card : ℝ)⁻¹ * ∑ e ∈ M,
        (1 - Network.binaryWeights η e) * ((issuedNetwork U).gradient u e)^2 *
          (if localTwoArm U i η e then 1 else 0) := by
  congr 1
  apply sum_congr rfl
  intro e _
  exact auxiliarySummand_eq_for_minimizer U i η u hu e

/-- Exact literal source selector in the arbitrary-mask auxiliary sum. -/
theorem maskedAuxiliary_eq_sourceMinimizer {d : ℕ} (U : Finset (Vertex d)) (i : Fin d)
    (M : Finset (IssuedBond U)) (η : IssuedBond U → Bool) :
    (U.card : ℝ)⁻¹ * (∑ e ∈ M,
      (1 - Network.binaryWeights η e) *
        ((issuedNetwork U).gradient
          ((issuedNetwork U).binaryMinimizer (twoFaceBoundary U i) (coordinateData i) η) e)^2 *
        (if localTwoArm U i η e then 1 else 0)) =
      (U.card : ℝ)⁻¹ * ∑ e ∈ M,
        (1 - Network.binaryWeights η e) *
          ((issuedNetwork U).gradient (sourceMinimizer U i η) e)^2 *
            (if localTwoArm U i η e then 1 else 0) :=
  maskedAuxiliary_eq_for_minimizer U i M η _ (sourceMinimizer_spec U i η)

/-- Literal source b-delta integrand for any selected issued-bond mask: OLD
configuration, actual source circle event, and boundary-average minimizer. -/
def sourceMaskedQuenchedB {d : ℕ} (U : Finset (Vertex d)) (i : Fin d)
    (M : Finset (IssuedBond U)) (ω : Configuration d) : ℝ :=
  (U.card : ℝ)⁻¹ * ∑ e ∈ M,
    (1 - domainWeights ω e) *
      ((issuedNetwork U).gradient (sourceMinimizer U i ((issuedBondSet U).restrict ω)) e)^2 *
        (if sourceTwoArm U i ω e then 1 else 0)

/-- Exact global source-event rewrite. Only the finite sum is masked; all bond
values, minimizers and two-arm events refer to the original configuration. -/
theorem maskedAuxiliary_restrict_eq_source {d : ℕ} (U : Finset (Vertex d)) (i : Fin d)
    (M : Finset (IssuedBond U)) (ω : Configuration d) :
    (U.card : ℝ)⁻¹ * (∑ e ∈ M,
      (1 - Network.binaryWeights ((issuedBondSet U).restrict ω) e) *
        ((issuedNetwork U).gradient
          ((issuedNetwork U).binaryMinimizer (twoFaceBoundary U i) (coordinateData i)
            ((issuedBondSet U).restrict ω)) e)^2 *
        (if localTwoArm U i ((issuedBondSet U).restrict ω) e then 1 else 0)) =
      sourceMaskedQuenchedB U i M ω := by
  rw [maskedAuxiliary_eq_sourceMinimizer]
  unfold sourceMaskedQuenchedB
  congr 1
  apply sum_congr rfl
  intro e _
  rw [← propext (localTwoArm_iff_sourceTwoArm U i ω e)]
  rfl

end NearCritical
