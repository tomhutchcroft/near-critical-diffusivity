module

public import NearCritical.AuxiliaryProbabilityBound
public import NearCritical.LatticePivotal
public import NearCritical.WaterCube

/-! Probability reductions expressed with the literal source circle events on
all lattice bonds. No high-dimensional probability estimate is asserted. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Set MeasureTheory

lemma twoArmCylinderEvent_eq_sourceTwoArm {d : ℕ} (U : Finset (Vertex d)) (i : Fin d)
    (e : IssuedBond U) : twoArmCylinderEvent U i e = {ω | sourceTwoArm U i ω e} := by
  ext ω
  exact localTwoArm_iff_sourceTwoArm U i ω e

lemma measurableSet_sourceTwoArm {d : ℕ} (U : Finset (Vertex d)) (i : Fin d) (e : IssuedBond U) :
    MeasurableSet {ω | sourceTwoArm U i ω e} := by
  rw [← twoArmCylinderEvent_eq_sourceTwoArm]
  exact measurableSet_twoArmCylinderEvent U i e

theorem annealedB_le_sourceTwoArm_probabilities {d : ℕ} (U : Finset (Vertex d)) (i : Fin d)
    {l h : DomainVertex U} (hl : l ∈ negativeFace U i) (hh : h ∈ positiveFace U i)
    (p : unitInterval) :
    annealedB U i (p : ℝ) ≤ ((coordinateData i h - coordinateData i l) ^ 2 / (U.card : ℝ)) *
      ∑ e : IssuedBond U, (percolation d p).real {ω | sourceTwoArm U i ω e} := by
  simpa only [twoArmCylinderEvent_eq_sourceTwoArm] using annealedB_le_twoArm_probabilities U i hl hh p

theorem annealedRelaxed_le_sourceTwoArm_probabilities {d : ℕ} (U : Finset (Vertex d)) (i : Fin d)
    {l h : DomainVertex U} (hl : l ∈ negativeFace U i) (hh : h ∈ positiveFace U i)
    (p : unitInterval) :
    annealedRelaxed U i (p : ℝ) ≤ ((coordinateData i h - coordinateData i l) ^ 2 / (U.card : ℝ)) *
      ∑ e : IssuedBond U, (percolation d p).real {ω | sourceTwoArm U i ω e} := by
  simpa only [twoArmCylinderEvent_eq_sourceTwoArm] using
    annealedRelaxed_le_twoArm_probabilities U i hl hh p

/-- The water-cube normalization h²/(h L^(d-1)), with h=2r+1,L=2R+1. -/
theorem waterCube_annealedB_le_sourceTwoArm_probabilities (d : ℕ) (i : Fin d) (r R : ℕ)
    (p : unitInterval) :
    annealedB (waterCube d i r R) i (p : ℝ) ≤
      ((2 * (r : ℝ) + 1) ^ 2 / ((2 * (r : ℝ) + 1) * (2 * (R : ℝ) + 1) ^ (d - 1))) *
        ∑ e : IssuedBond (waterCube d i r R), (percolation d p).real
          {ω | sourceTwoArm (waterCube d i r R) i ω e} := by
  obtain ⟨l, hl⟩ := negativeFace_nonempty (waterCube_nonempty d i r R) i
  obtain ⟨h, hh⟩ := positiveFace_nonempty (waterCube_nonempty d i r R) i
  have hb := annealedB_le_sourceTwoArm_probabilities (waterCube d i r R) i hl hh p
  rw [waterCube_face_height d i r R hl hh, card_waterCube] at hb
  simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, Nat.cast_pow] using hb

end NearCritical
