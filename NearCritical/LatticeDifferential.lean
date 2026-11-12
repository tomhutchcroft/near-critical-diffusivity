module

public import NearCritical.DifferentialInequality
public import NearCritical.LatticeRusso
public import NearCritical.LatticeFaces
public import NearCritical.NetworkPivotal

/-! The finite-volume differential inequality `prop.inequality_diff` on the
actual issued-edge lattice domains. The two-arm event is deterministic disjoint
connection support in the OLD configuration. Both a and b are identified with
expectations under the concrete infinite product percolation law. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Finset Set MeasureTheory ProbabilityTheory BernoulliCalculus

/-- The opposite-face two-arm event of equation `eq.two_arm`, in the original
finite configuration, with disjoint open-edge certificates. -/
def localTwoArm {d : ℕ} (U : Finset (Vertex d)) (i : Fin d)
    (η : IssuedBond U → Bool) (e : IssuedBond U) : Prop :=
  (issuedNetwork U).binaryTwoArm (negativeFace U i) (positiveFace U i) η e

/-- The quenched quantity inside the expectation in equation `eq.defbb`.
The gradient is that of the ORIGINAL configuration's selected minimizer. -/
def localB {d : ℕ} (U : Finset (Vertex d)) (i : Fin d) (η : IssuedBond U → Bool) : ℝ := by
  classical
  exact (U.card : ℝ)⁻¹ * ∑ e,
    (1 - Network.binaryWeights η e) *
      ((issuedNetwork U).gradient
        ((issuedNetwork U).binaryMinimizer (twoFaceBoundary U i) (coordinateData i) η) e) ^ 2 *
      if localTwoArm U i η e then 1 else 0

def annealedB {d : ℕ} (U : Finset (Vertex d)) (i : Fin d) (p : ℝ) : ℝ :=
  finiteExpectation p (localB U i)

def quenchedB {d : ℕ} (U : Finset (Vertex d)) (i : Fin d) (ω : Configuration d) : ℝ :=
  localB U i ((issuedBondSet U).restrict ω)

lemma localB_nonneg {d : ℕ} (U : Finset (Vertex d)) (i : Fin d) (η : IssuedBond U → Bool) :
    0 ≤ localB U i η := by
  classical
  apply mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg U.card))
  apply Finset.sum_nonneg
  intro e _
  apply mul_nonneg
  · exact mul_nonneg (sub_nonneg.mpr (Network.binaryWeights_le_one η e)) (sq_nonneg _)
  · split <;> norm_num

lemma annealedB_nonneg {d : ℕ} (U : Finset (Vertex d)) (i : Fin d) {p : ℝ}
    (hp : 0 ≤ p) (hp1 : p ≤ 1) : 0 ≤ annealedB U i p :=
  finiteExpectation_nonneg hp hp1 (localB_nonneg U i)

/-- Identification of b(U,p) with the original percolation probability law. -/
theorem annealedB_eq_integral {d : ℕ} (U : Finset (Vertex d)) (i : Fin d) (p : unitInterval) :
    annealedB U i (p : ℝ) = ∫ ω, quenchedB U i ω ∂percolation d p := by
  classical
  exact (percolation_cylinder_expectation d p (issuedBondSet U) (localB U i)).symm

lemma annealedB_eq_binaryAuxiliary {d : ℕ} (U : Finset (Vertex d)) (i : Fin d) (p : ℝ) :
    annealedB U i p = (issuedNetwork U).binaryAuxiliary (twoFaceBoundary U i) (coordinateData i)
      (localTwoArm U i) (U.card : ℝ)⁻¹ p := rfl

lemma localRelaxedConductivity_eq_binary {d : ℕ} (U : Finset (Vertex d)) (i : Fin d) :
    localRelaxedConductivity U i = (fun η ↦
      (issuedNetwork U).binaryConductance (twoFaceBoundary U i) (coordinateData i) η / (U.card : ℝ)) := rfl

/-- Geometric support of conductivity-changing openings in the actual lattice
model. Face constancy and access are proved, not left as source hypotheses. -/
theorem localConductance_pivotal_support {d : ℕ} {U : Finset (Vertex d)} (hU : U.Nonempty)
    (i : Fin d) (η : IssuedBond U → Bool) (e : IssuedBond U)
    (hchange : (issuedNetwork U).binaryConductance (twoFaceBoundary U i) (coordinateData i)
      (forceOpen e η) ≠
      (issuedNetwork U).binaryConductance (twoFaceBoundary U i) (coordinateData i) η) :
    localTwoArm U i η e := by
  classical
  obtain ⟨x, hx⟩ := negativeFace_nonempty hU i
  obtain ⟨y, hy⟩ := positiveFace_nonempty hU i
  have hlohi : coordinateData i x ≤ coordinateData i y := (face_data_lt hU hx hy).le
  have hlow : ∀ v ∈ negativeFace U i, coordinateData i v = coordinateData i x := by
    intro v hv
    exact negativeFace_data_constant hv hx
  have hhigh : ∀ v ∈ positiveFace U i, coordinateData i v = coordinateData i y := by
    intro v hv
    exact positiveFace_data_constant hv hy
  rw [twoFaceBoundary_eq_union] at hchange
  exact ((issuedNetwork U).binaryConductance_pivotal_support hlohi hlow hhigh η e hchange).2

/-- Proposition `prop.inequality_diff`, including the source's normalization
and actual two-arm auxiliary term. It is proved for all finite nonempty lattice
domains, hence for the cubes and water cubes used in the paper. -/
theorem annealedRelaxed_differential_inequality {d : ℕ} {U : Finset (Vertex d)}
    (hU : U.Nonempty) (i : Fin d) {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    deriv (annealedRelaxed U i) p ≤
      Real.sqrt (annealedRelaxed U i p) * Real.sqrt (annealedB U i p) /
        (Real.sqrt p * (1 - p)) := by
  classical
  have hvol : 0 < (U.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hU
  have h := (issuedNetwork U).binaryConductance_volume_differential_inequality_of_support
    (twoFaceBoundary U i) (coordinateData i) (localTwoArm U i) hp hp1 hvol
    (localConductance_pivotal_support hU i)
  change deriv (fun q ↦ finiteExpectation q (localRelaxedConductivity U i)) p ≤
    Real.sqrt (finiteExpectation p (localRelaxedConductivity U i)) * Real.sqrt (annealedB U i p) /
      (Real.sqrt p * (1 - p))
  rw [localRelaxedConductivity_eq_binary, annealedB_eq_binaryAuxiliary]
  exact h

end NearCritical
