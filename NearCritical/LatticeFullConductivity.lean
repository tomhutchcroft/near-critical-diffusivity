module

public import NearCritical.LatticeRusso
public import NearCritical.DifferentialInequality

/-! Full-Dirichlet finite-volume annealed conductivity under the actual lattice
law. This keeps the full boundary distinct from the relaxed two-face boundary. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory

/-- The full-boundary finite-coordinate observable, on precisely E+(U). -/
def localFullConductivity {d : ℕ} (U : Finset (Vertex d)) (i : Fin d)
    (η : IssuedBond U → Bool) : ℝ :=
  (issuedNetwork U).conductance (fun e ↦ if η e then 1 else 0)
    (fullBoundary U) (coordinateData i) / U.card

lemma fullConductivity_restrict {d : ℕ} (U : Finset (Vertex d)) (i : Fin d)
    (ω : Configuration d) :
    fullConductivity U i ω = localFullConductivity U i ((issuedBondSet U).restrict ω) := rfl

def annealedFull {d : ℕ} (U : Finset (Vertex d)) (i : Fin d) (p : ℝ) : ℝ :=
  finiteExpectation p (localFullConductivity U i)

theorem annealedFull_polynomial {d : ℕ} (U : Finset (Vertex d)) (i : Fin d) :
    ∃ P : Polynomial ℝ, ∀ p : ℝ, P.eval p = annealedFull U i p := by
  exact ⟨annealedPolynomial (localFullConductivity U i), fun p ↦ eval_annealedPolynomial p _⟩

theorem annealedFull_eq_integral {d : ℕ} (U : Finset (Vertex d)) (i : Fin d)
    (p : unitInterval) :
    annealedFull U i (p : ℝ) = ∫ ω, fullConductivity U i ω ∂percolation d p := by
  simp_rw [fullConductivity_restrict]
  exact (percolation_cylinder_expectation d p (issuedBondSet U) (localFullConductivity U i)).symm

lemma localRelaxedConductivity_le_full {d : ℕ} (U : Finset (Vertex d)) (i : Fin d)
    (η : IssuedBond U → Bool) :
    localRelaxedConductivity U i η ≤ localFullConductivity U i η := by
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact (issuedNetwork U).conductance_boundary_mono
    (fun e ↦ by split <;> norm_num) (twoFaceBoundary_subset U i) (coordinateData i)

/-- Annealed form of the source's boundary-relaxation comparison. -/
theorem annealedRelaxed_le_full {d : ℕ} (U : Finset (Vertex d)) (i : Fin d)
    {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    annealedRelaxed U i p ≤ annealedFull U i p :=
  finiteExpectation_mono hp hp1 (localRelaxedConductivity_le_full U i)

lemma localFullConductivity_nonneg {d : ℕ} (U : Finset (Vertex d)) (i : Fin d)
    (η : IssuedBond U → Bool) : 0 ≤ localFullConductivity U i η := by
  exact div_nonneg ((issuedNetwork U).conductance_nonneg
    (fun e ↦ by split <;> norm_num) _ _) (Nat.cast_nonneg _)

lemma annealedFull_nonneg {d : ℕ} (U : Finset (Vertex d)) (i : Fin d)
    {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) : 0 ≤ annealedFull U i p :=
  finiteExpectation_nonneg hp hp1 (localFullConductivity_nonneg U i)

/-- Every real finite-coordinate observable is integrable under percolation. -/
lemma percolation_cylinder_integrable (d : ℕ) (p : unitInterval) (s : Finset (Bond d))
    (f : ((e : s) → Bool) → ℝ) :
    Integrable (fun ω : Configuration d ↦ f (s.restrict ω)) (percolation d p) := by
  have hm : Measurable (s.restrict : Configuration d → ((e : s) → Bool)) :=
    Finset.measurable_restrict s
  have hf : Integrable f ((percolation d p).map
      (s.restrict : Configuration d → ((e : s) → Bool))) := Integrable.of_finite
  exact hf.comp_measurable hm

lemma integrable_fullConductivity {d : ℕ} (U : Finset (Vertex d)) (i : Fin d)
    (p : unitInterval) : Integrable (fullConductivity U i) (percolation d p) := by
  change Integrable (fun ω ↦ fullConductivity U i ω) (percolation d p)
  simp_rw [fullConductivity_restrict]
  exact percolation_cylinder_integrable d p (issuedBondSet U) (localFullConductivity U i)

end NearCritical
