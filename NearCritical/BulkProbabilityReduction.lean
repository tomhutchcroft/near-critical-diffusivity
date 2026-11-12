module

public import NearCritical.BulkPercolation
public import NearCritical.SourceProbabilityReduction

/-! Exact two-arm probability reductions for the paper's new bulk argument.
The auxiliary edge sum is masked; the conductivity edge sum is not. All
probabilities use the actual inhomogeneous product law. No BK or decay input. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Finset Set MeasureTheory
open scoped Classical

/-- The old-configuration masked auxiliary is bounded using the canonical
source maximum principle, including its voltages on closed tested bonds. -/
theorem localMaskedB_le_twoArm_count {d : ℕ} (U : Finset (Vertex d)) (i : Fin d)
    (M : Finset (IssuedBond U)) {l h : DomainVertex U}
    (hl : l ∈ negativeFace U i) (hh : h ∈ positiveFace U i) (η : IssuedBond U → Bool) :
    localMaskedB U i M η ≤ ((coordinateData i h - coordinateData i l)^2 / (U.card : ℝ)) *
      ∑ e ∈ M, if localTwoArm U i η e then 1 else 0 := by
  unfold localMaskedB
  rw [maskedAuxiliary_eq_sourceMinimizer]
  calc
    _ ≤ (U.card : ℝ)⁻¹ * ∑ e ∈ M,
        (coordinateData i h - coordinateData i l)^2 *
          (if localTwoArm U i η e then 1 else 0) := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg U.card))
      apply sum_le_sum
      intro e _
      exact weighted_square_indicator_le
        (by linarith [Network.binaryWeights_nonneg η e])
        (sourceMinimizer_gradient_bound hl hh η e)
    _ = _ := by rw [← mul_sum]; ring

/-- Exact finite indicator expectation under the actual inhomogeneous law.
The event uses the original FULL issued-domain configuration and source circle. -/
theorem maskedExpectation_twoArm_indicator_eq_probability {d : ℕ}
    (U : Finset (Vertex d)) (i : Fin d) (M : Finset (IssuedBond U))
    (e : IssuedBond U) (p s : unitInterval) :
    finiteExpectationProfile (maskProfile M (p : ℝ) (s : ℝ))
      (fun η ↦ if localTwoArm U i η e then 1 else 0) =
      (maskedPercolation d (M.image Subtype.val) p s).real {ω | sourceTwoArm U i ω e} := by
  calc
    _ = ∫ ω, (if localTwoArm U i ((issuedBondSet U).restrict ω) e then (1 : ℝ) else 0)
        ∂maskedPercolation d (M.image Subtype.val) p s :=
      (maskedPercolation_expectation U M p s
        (fun η ↦ if localTwoArm U i η e then (1 : ℝ) else 0)).symm
    _ = ∫ ω, (if sourceTwoArm U i ω e then (1 : ℝ) else 0)
        ∂maskedPercolation d (M.image Subtype.val) p s := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun ω ↦ by
        change (if localTwoArm U i ((issuedBondSet U).restrict ω) e then (1 : ℝ) else 0) =
          (if sourceTwoArm U i ω e then (1 : ℝ) else 0)
        rw [localTwoArm_iff_sourceTwoArm U i ω e])
    _ = _ := by
      have hi := integral_indicator_one
        (μ := maskedPercolation d (M.image Subtype.val) p s) (measurableSet_sourceTwoArm U i e)
      simpa only [Set.indicator, Pi.one_apply, Set.mem_ofPred_eq] using! hi

private lemma maskProfile_unit_bounds {E : Type*} (M : Finset E) (p s : unitInterval) :
    ∀ e, 0 ≤ maskProfile M (p : ℝ) (s : ℝ) e ∧ maskProfile M (p : ℝ) (s : ℝ) e ≤ 1 := by
  intro e
  unfold maskProfile
  split
  · exact s.property
  · exact p.property

/-- Exact precursor for b-delta: only the edge sum in the perturbed mask appears.
Neither independence/BK between the arms nor any decay estimate is assumed. -/
theorem annealedMaskedB_le_sourceTwoArm_probabilities {d : ℕ}
    (U : Finset (Vertex d)) (i : Fin d) (M : Finset (IssuedBond U))
    {l h : DomainVertex U} (hl : l ∈ negativeFace U i) (hh : h ∈ positiveFace U i)
    (p s : unitInterval) :
    annealedMaskedB U i M (p : ℝ) (s : ℝ) ≤
      ((coordinateData i h - coordinateData i l)^2 / (U.card : ℝ)) *
        ∑ e ∈ M, (maskedPercolation d (M.image Subtype.val) p s).real
          {ω | sourceTwoArm U i ω e} := by
  calc
    _ ≤ finiteExpectationProfile (maskProfile M (p : ℝ) (s : ℝ)) (fun η ↦
        ((coordinateData i h - coordinateData i l)^2 / (U.card : ℝ)) *
          ∑ e ∈ M, if localTwoArm U i η e then 1 else 0) :=
      finiteExpectationProfile_mono (maskProfile_unit_bounds M p s)
        (localMaskedB_le_twoArm_count U i M hl hh)
    _ = _ := by
      rw [finiteExpectationProfile_const_mul, finiteExpectationProfile_finsetSum]
      simp only [maskedExpectation_twoArm_indicator_eq_probability U i M]

/-- In a-delta the law is perturbed on M, but the energy retains ALL issued
bonds of U. Replacing this sum by M would incorrectly change the source energy. -/
theorem annealedMaskedRelaxed_le_sourceTwoArm_probabilities {d : ℕ}
    (U : Finset (Vertex d)) (i : Fin d) (M : Finset (IssuedBond U))
    {l h : DomainVertex U} (hl : l ∈ negativeFace U i) (hh : h ∈ positiveFace U i)
    (p s : unitInterval) :
    annealedMaskedRelaxed U i M (p : ℝ) (s : ℝ) ≤
      ((coordinateData i h - coordinateData i l)^2 / (U.card : ℝ)) *
        ∑ e : IssuedBond U, (maskedPercolation d (M.image Subtype.val) p s).real
          {ω | sourceTwoArm U i ω e} := by
  calc
    _ ≤ finiteExpectationProfile (maskProfile M (p : ℝ) (s : ℝ)) (fun η ↦
        ((coordinateData i h - coordinateData i l)^2 / (U.card : ℝ)) *
          ∑ e : IssuedBond U, if localTwoArm U i η e then 1 else 0) :=
      finiteExpectationProfile_mono (maskProfile_unit_bounds M p s)
        (localRelaxedConductivity_le_twoArm_count U i hl hh)
    _ = _ := by
      rw [finiteExpectationProfile_const_mul, finiteExpectationProfile_finsetSum]
      simp only [maskedExpectation_twoArm_indicator_eq_probability U i M]

/-- The bulk mask is the source's BOTH-endpoint internal-bond set. -/
theorem annealedBulkB_le_sourceTwoArm_probabilities {d : ℕ}
    (U : Finset (Vertex d)) (i : Fin d) (height δ : ℝ)
    {l h : DomainVertex U} (hl : l ∈ negativeFace U i) (hh : h ∈ positiveFace U i)
    (p s : unitInterval) :
    annealedMaskedB U i (bulkBondMask U i height δ) (p : ℝ) (s : ℝ) ≤
      ((coordinateData i h - coordinateData i l)^2 / (U.card : ℝ)) *
        ∑ e ∈ bulkBondMask U i height δ, (bulkPercolation U i height δ p s).real
          {ω | sourceTwoArm U i ω e} := by
  rw [bulkPercolation_eq_masked]
  exact annealedMaskedB_le_sourceTwoArm_probabilities U i _ hl hh p s

theorem annealedBulkRelaxed_le_sourceTwoArm_probabilities {d : ℕ}
    (U : Finset (Vertex d)) (i : Fin d) (height δ : ℝ)
    {l h : DomainVertex U} (hl : l ∈ negativeFace U i) (hh : h ∈ positiveFace U i)
    (p s : unitInterval) :
    annealedMaskedRelaxed U i (bulkBondMask U i height δ) (p : ℝ) (s : ℝ) ≤
      ((coordinateData i h - coordinateData i l)^2 / (U.card : ℝ)) *
        ∑ e : IssuedBond U, (bulkPercolation U i height δ p s).real
          {ω | sourceTwoArm U i ω e} := by
  rw [bulkPercolation_eq_masked]
  exact annealedMaskedRelaxed_le_sourceTwoArm_probabilities U i _ hl hh p s

/-- Source water-cube height is 2r+1, while the b-delta sum stays bulk-only. -/
theorem waterCube_annealedBulkB_le_sourceTwoArm_probabilities
    (d : ℕ) (i : Fin d) (r R : ℕ) (δ : ℝ) (p s : unitInterval) :
    annealedMaskedB (waterCube d i r R) i
      (bulkBondMask (waterCube d i r R) i (2*(r:ℝ)+1) δ) (p : ℝ) (s : ℝ) ≤
      ((2*(r:ℝ)+1)^2 / ((2*(r:ℝ)+1)*(2*(R:ℝ)+1)^(d-1))) *
        ∑ e ∈ bulkBondMask (waterCube d i r R) i (2*(r:ℝ)+1) δ,
          (bulkPercolation (waterCube d i r R) i (2*(r:ℝ)+1) δ p s).real
            {ω | sourceTwoArm (waterCube d i r R) i ω e} := by
  obtain ⟨l, hl⟩ := negativeFace_nonempty (waterCube_nonempty d i r R) i
  obtain ⟨h, hh⟩ := positiveFace_nonempty (waterCube_nonempty d i r R) i
  have hb := annealedBulkB_le_sourceTwoArm_probabilities (waterCube d i r R) i (2*(r:ℝ)+1) δ hl hh p s
  rw [waterCube_face_height d i r R hl hh, card_waterCube] at hb
  simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, Nat.cast_pow] using hb

/-- Same height normalization, retaining the full energy edge sum for a-delta. -/
theorem waterCube_annealedBulkRelaxed_le_sourceTwoArm_probabilities
    (d : ℕ) (i : Fin d) (r R : ℕ) (δ : ℝ) (p s : unitInterval) :
    annealedMaskedRelaxed (waterCube d i r R) i
      (bulkBondMask (waterCube d i r R) i (2*(r:ℝ)+1) δ) (p : ℝ) (s : ℝ) ≤
      ((2*(r:ℝ)+1)^2 / ((2*(r:ℝ)+1)*(2*(R:ℝ)+1)^(d-1))) *
        ∑ e : IssuedBond (waterCube d i r R),
          (bulkPercolation (waterCube d i r R) i (2*(r:ℝ)+1) δ p s).real
            {ω | sourceTwoArm (waterCube d i r R) i ω e} := by
  obtain ⟨l, hl⟩ := negativeFace_nonempty (waterCube_nonempty d i r R) i
  obtain ⟨h, hh⟩ := positiveFace_nonempty (waterCube_nonempty d i r R) i
  have hb := annealedBulkRelaxed_le_sourceTwoArm_probabilities (waterCube d i r R) i (2*(r:ℝ)+1) δ hl hh p s
  rw [waterCube_face_height d i r R hl hh, card_waterCube] at hb
  simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, Nat.cast_pow] using hb

end NearCritical
