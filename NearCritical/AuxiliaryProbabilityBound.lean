module

public import NearCritical.LatticeCanonicalMinimizer
public import NearCritical.NetworkEnergyLocalization
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! Deterministic bounds reducing the auxiliary b term to exact two-arm
probabilities. No high-dimensional estimate or BK inequality is assumed here. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Finset Set MeasureTheory ProbabilityTheory
open scoped Classical

lemma weighted_square_indicator_le {w v M : ℝ} {P : Prop}
    (hw1 : w ≤ 1) (hv : |v| ≤ M) :
    w * v ^ 2 * (if P then 1 else 0) ≤ M ^ 2 * (if P then 1 else 0) := by
  have hM : 0 ≤ M := (abs_nonneg v).trans hv
  have hsq : v ^ 2 ≤ M ^ 2 := sq_le_sq.mpr (by simpa only [abs_of_nonneg hM] using hv)
  by_cases hP : P
  · simp only [ite_eq_left hP, mul_one]
    exact (mul_le_mul_of_nonneg_right hw1 (sq_nonneg v)).trans (by simpa using hsq)
  · simp [hP]

/-- Pointwise reduction of b to a count of two-arm events. The source-prescribed
boundary-average minimizer supplies the maximum-principle bound on all edges. -/
theorem localB_le_twoArm_count {d : ℕ} (U : Finset (Vertex d)) (i : Fin d)
    {l h : DomainVertex U} (hl : l ∈ negativeFace U i) (hh : h ∈ positiveFace U i)
    (η : IssuedBond U → Bool) :
    localB U i η ≤ ((coordinateData i h - coordinateData i l) ^ 2 / (U.card : ℝ)) *
      ∑ e : IssuedBond U, if localTwoArm U i η e then 1 else 0 := by
  classical
  rw [localB_eq_sourceMinimizer]
  calc
    _ ≤ (U.card : ℝ)⁻¹ * ∑ e : IssuedBond U,
        (coordinateData i h - coordinateData i l) ^ 2 *
          (if localTwoArm U i η e then 1 else 0) := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg U.card))
      apply Finset.sum_le_sum
      intro e _
      exact weighted_square_indicator_le
        (by linarith [Network.binaryWeights_nonneg η e])
        (sourceMinimizer_gradient_bound hl hh η e)
    _ = _ := by rw [← Finset.mul_sum]; ring

/-- Exact probabilistic precursor to the estimates for b in the paper:
only the sum of actual two-arm probabilities remains to be bounded. -/
theorem annealedB_le_twoArm_expectations {d : ℕ} (U : Finset (Vertex d)) (i : Fin d)
    {l h : DomainVertex U} (hl : l ∈ negativeFace U i) (hh : h ∈ positiveFace U i)
    {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    annealedB U i p ≤ ((coordinateData i h - coordinateData i l) ^ 2 / (U.card : ℝ)) *
      ∑ e : IssuedBond U, finiteExpectation p (fun η ↦ if localTwoArm U i η e then 1 else 0) := by
  calc
    _ ≤ finiteExpectation p (fun η ↦
        ((coordinateData i h - coordinateData i l) ^ 2 / (U.card : ℝ)) *
          ∑ e : IssuedBond U, if localTwoArm U i η e then 1 else 0) :=
      finiteExpectation_mono hp hp1 (localB_le_twoArm_count U i hl hh)
    _ = _ := by rw [finiteExpectation_const_mul, finiteExpectation_sum]

/-- The two-arm event lifted to the original infinite configuration space. -/
def twoArmCylinderEvent {d : ℕ} (U : Finset (Vertex d)) (i : Fin d) (e : IssuedBond U) :
    Set (Configuration d) := {ω | localTwoArm U i ((issuedBondSet U).restrict ω) e}

lemma measurableSet_twoArmCylinderEvent {d : ℕ} (U : Finset (Vertex d)) (i : Fin d)
    (e : IssuedBond U) : MeasurableSet (twoArmCylinderEvent U i e) := by
  classical
  have hs : MeasurableSet {η : IssuedBond U → Bool | localTwoArm U i η e} :=
    (Set.toFinite _).measurableSet
  exact hs.preimage (Finset.measurable_restrict (issuedBondSet U))

/-- The finite indicator expectation is exactly the probability under the
original infinite-lattice Bernoulli measure, not a replacement finite model. -/
theorem finiteExpectation_twoArm_indicator_eq_probability {d : ℕ} (U : Finset (Vertex d))
    (i : Fin d) (e : IssuedBond U) (p : unitInterval) :
    finiteExpectation (p : ℝ) (fun η ↦ if localTwoArm U i η e then 1 else 0) =
      (percolation d p).real (twoArmCylinderEvent U i e) := by
  classical
  calc
    _ = ∫ ω, (if localTwoArm U i ((issuedBondSet U).restrict ω) e then 1 else 0) ∂percolation d p :=
      (percolation_cylinder_expectation d p (issuedBondSet U)
        (fun η ↦ if localTwoArm U i η e then (1 : ℝ) else 0)).symm
    _ = _ := by
      have hi := integral_indicator_one (μ := percolation d p) (measurableSet_twoArmCylinderEvent U i e)
      simpa only [Set.indicator, Pi.one_apply, twoArmCylinderEvent, Set.mem_ofPred_eq] using! hi

/-- Reduction of the paper's actual b(U,p) to actual two-arm probabilities.
All geometry and minimizer bounds are proved; no stochastic decay assumption
is hidden in this inequality. -/
theorem annealedB_le_twoArm_probabilities {d : ℕ} (U : Finset (Vertex d)) (i : Fin d)
    {l h : DomainVertex U} (hl : l ∈ negativeFace U i) (hh : h ∈ positiveFace U i)
    (p : unitInterval) :
    annealedB U i (p : ℝ) ≤ ((coordinateData i h - coordinateData i l) ^ 2 / (U.card : ℝ)) *
      ∑ e : IssuedBond U, (percolation d p).real (twoArmCylinderEvent U i e) := by
  have h := annealedB_le_twoArm_expectations U i hl hh p.property.1 p.property.2
  simpa only [finiteExpectation_twoArm_indicator_eq_probability U i] using h

/-- The same probability precursor for conductivity itself, using exact
energy localization rather than the auxiliary closed-edge expression. -/
theorem localRelaxedConductivity_le_twoArm_count {d : ℕ} (U : Finset (Vertex d)) (i : Fin d)
    {l h : DomainVertex U} (hl : l ∈ negativeFace U i) (hh : h ∈ positiveFace U i)
    (η : IssuedBond U → Bool) :
    localRelaxedConductivity U i η ≤ ((coordinateData i h - coordinateData i l) ^ 2 / (U.card : ℝ)) *
      ∑ e : IssuedBond U, if localTwoArm U i η e then 1 else 0 := by
  classical
  have hu := sourceMinimizer_spec U i η
  rw [twoFaceBoundary_eq_union] at hu
  have hlohi := (face_data_range hl hh l).2
  have hlow : ∀ v ∈ negativeFace U i, coordinateData i v = coordinateData i l :=
    fun _ hv ↦ negativeFace_data_constant hv hl
  have hhigh : ∀ v ∈ positiveFace U i, coordinateData i v = coordinateData i h :=
    fun _ hv ↦ positiveFace_data_constant hv hh
  have hloc := hu.binaryConductance_eq_localized_energy (issuedNetwork U) η hlohi hlow hhigh
  rw [← twoFaceBoundary_eq_union] at hloc
  rw [localRelaxedConductivity_eq_binary]
  dsimp only
  rw [hloc]
  calc
    _ ≤ (∑ e : IssuedBond U, (coordinateData i h - coordinateData i l) ^ 2 *
          (if localTwoArm U i η e then 1 else 0)) / (U.card : ℝ) := by
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg U.card)
      apply Finset.sum_le_sum
      intro e _
      exact weighted_square_indicator_le (Network.binaryWeights_le_one η e)
        (sourceMinimizer_gradient_bound hl hh η e)
    _ = _ := by rw [← Finset.mul_sum]; ring

/-- Conductivity is bounded by the same explicit sum of exact two-arm
probabilities. Stochastic critical estimates enter only after this reduction. -/
theorem annealedRelaxed_le_twoArm_probabilities {d : ℕ} (U : Finset (Vertex d)) (i : Fin d)
    {l h : DomainVertex U} (hl : l ∈ negativeFace U i) (hh : h ∈ positiveFace U i)
    (p : unitInterval) :
    annealedRelaxed U i (p : ℝ) ≤ ((coordinateData i h - coordinateData i l) ^ 2 / (U.card : ℝ)) *
      ∑ e : IssuedBond U, (percolation d p).real (twoArmCylinderEvent U i e) := by
  have hp := p.property.1
  have hp1 := p.property.2
  calc
    _ ≤ finiteExpectation (p : ℝ) (fun η ↦
        ((coordinateData i h - coordinateData i l) ^ 2 / (U.card : ℝ)) *
          ∑ e : IssuedBond U, if localTwoArm U i η e then 1 else 0) :=
      finiteExpectation_mono hp hp1 (localRelaxedConductivity_le_twoArm_count U i hl hh)
    _ = _ := by
      rw [finiteExpectation_const_mul, finiteExpectation_sum]
      simp only [finiteExpectation_twoArm_indicator_eq_probability U i]

end NearCritical
