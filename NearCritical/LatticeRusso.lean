module

public import NearCritical.LatticeDomain
public import NearCritical.Russo

/-! Russo's formula for the paper's relaxed finite-volume conductivity.
The polynomial is an extension to real parameters. On [0,1] it is proved to
equal the expectation under the concrete infinite-lattice percolation law. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory ProbabilityTheory BernoulliCalculus

noncomputable def localRelaxedConductivity {d : ℕ} (U : Finset (Vertex d)) (i : Fin d)
    (η : IssuedBond U → Bool) : ℝ :=
  (issuedNetwork U).conductance (fun e ↦ if η e then 1 else 0)
    (twoFaceBoundary U i) (coordinateData i) / U.card

lemma relaxedConductivity_restrict {d : ℕ} (U : Finset (Vertex d)) (i : Fin d)
    (ω : Configuration d) :
    relaxedConductivity U i ω = localRelaxedConductivity U i ((issuedBondSet U).restrict ω) := rfl

/-- Polynomial extension of the annealed two-face conductivity. -/
noncomputable def annealedRelaxed {d : ℕ} (U : Finset (Vertex d)) (i : Fin d) (p : ℝ) : ℝ :=
  finiteExpectation p (localRelaxedConductivity U i)

/-- Polynomiality in `pr:expansion_init`, with the polynomial exhibited. -/
theorem annealedRelaxed_polynomial {d : ℕ} (U : Finset (Vertex d)) (i : Fin d) :
    ∃ P : Polynomial ℝ, ∀ p : ℝ, P.eval p = annealedRelaxed U i p := by
  refine ⟨annealedPolynomial (localRelaxedConductivity U i), ?_⟩
  exact fun p ↦ eval_annealedPolynomial p _

/-- Identification with the original infinite-product measure. -/
theorem annealedRelaxed_eq_integral {d : ℕ} (U : Finset (Vertex d)) (i : Fin d)
    (p : unitInterval) :
    annealedRelaxed U i (p : ℝ) = ∫ ω, relaxedConductivity U i ω ∂percolation d p := by
  classical
  simp_rw [relaxedConductivity_restrict]
  exact (percolation_cylinder_expectation d p (issuedBondSet U) (localRelaxedConductivity U i)).symm

lemma restrict_update_bond {d : ℕ} (s : Finset (Bond d)) (ω : Configuration d) (e : s) :
    s.restrict (Function.update ω e.val true) = forceOpen e (s.restrict ω) := by
  classical
  rw [forceOpen_eq_update]
  ext j
  by_cases hj : j = e
  · subst j
    simp
  · have hv : j.val ≠ e.val := fun h ↦ hj (Subtype.ext h)
    simp [Finset.restrict, Function.update_of_ne hj, Function.update_of_ne hv]

lemma relaxed_opening_expectation {d : ℕ} (U : Finset (Vertex d)) (i : Fin d)
    (p : unitInterval) (e : IssuedBond U) :
    finiteExpectation (p : ℝ)
      (fun η ↦ localRelaxedConductivity U i (forceOpen e η) - localRelaxedConductivity U i η) =
    ∫ ω, (relaxedConductivity U i (Function.update ω e.val true) - relaxedConductivity U i ω)
      ∂percolation d p := by
  classical
  simp_rw [relaxedConductivity_restrict, restrict_update_bond]
  exact (percolation_cylinder_expectation d p (issuedBondSet U)
    (fun η ↦ localRelaxedConductivity U i (forceOpen e η) - localRelaxedConductivity U i η)).symm

/-- `pr:expansion_init` for the paper's issued-edge domains and relaxed
boundary data. Both sides refer to the same infinite-product percolation model. -/
theorem annealedRelaxed_russo {d : ℕ} (U : Finset (Vertex d)) (i : Fin d)
    (p : unitInterval) (hp : (p : ℝ) ≠ 1) :
    HasDerivAt (annealedRelaxed U i)
      ((1 - (p : ℝ))⁻¹ * ∑ e : IssuedBond U,
        ∫ ω, (relaxedConductivity U i (Function.update ω e.val true) - relaxedConductivity U i ω)
          ∂percolation d p) (p : ℝ) := by
  classical
  have h := BernoulliCalculus.finiteExpectation_russo (p : ℝ) hp (localRelaxedConductivity U i)
  simp_rw [relaxed_opening_expectation U i p] at h
  exact h

end NearCritical
