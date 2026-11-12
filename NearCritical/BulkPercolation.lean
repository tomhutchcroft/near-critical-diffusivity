module

public import NearCritical.BulkDifferential
public import NearCritical.MaskedAuxiliaryChoice

/-! Exact original-law interpretation of the paper's bulk perturbation.
The law varies only the internal bonds of the bulk; the energy is unchanged. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Finset MeasureTheory
open scoped Classical

def maskedPercolation (d : ℕ) (B : Finset (Bond d)) (p s : unitInterval) :
    Measure (Configuration d) :=
  percolationProfile d (fun e ↦ if e ∈ B then s else p)

lemma maskedPercolation_self (d : ℕ) (B : Finset (Bond d)) (p : unitInterval) :
    maskedPercolation d B p p = percolation d p := by
  simp only [maskedPercolation, ite_self, percolationProfile_const]

lemma issued_mask_image_mem {d : ℕ} {U : Finset (Vertex d)}
    (M : Finset (IssuedBond U)) (e : IssuedBond U) :
    e.val ∈ M.image Subtype.val ↔ e ∈ M := by
  constructor
  · rintro he
    obtain ⟨j, hj, hje⟩ := Finset.mem_image.mp he
    exact (Subtype.ext hje : j = e) ▸ hj
  · exact fun he ↦ Finset.mem_image.mpr ⟨e, he, rfl⟩

/-- Exact expectation identity for every finite energy-coordinate observable. -/
theorem maskedPercolation_expectation {d : ℕ} (U : Finset (Vertex d))
    (M : Finset (IssuedBond U)) (p s : unitInterval) (f : (IssuedBond U → Bool) → ℝ) :
    (∫ ω, f ((issuedBondSet U).restrict ω)
      ∂maskedPercolation d (M.image Subtype.val) p s) =
      finiteExpectationProfile (maskProfile M (p : ℝ) (s : ℝ)) f := by
  unfold maskedPercolation
  rw [percolationProfile_cylinder_expectation]
  congr 1
  funext e
  by_cases he : e ∈ M
  · simp only [issued_mask_image_mem, he, ite_true, maskProfile]
  · simp only [issued_mask_image_mem, he, ite_false, maskProfile]

/-- Original infinite-product integral, with the source full-domain energy. -/
theorem annealedMaskedRelaxed_eq_integral {d : ℕ} (U : Finset (Vertex d)) (i : Fin d)
    (M : Finset (IssuedBond U)) (p s : unitInterval) :
    annealedMaskedRelaxed U i M (p : ℝ) (s : ℝ) =
      ∫ ω, relaxedConductivity U i ω ∂maskedPercolation d (M.image Subtype.val) p s := by
  simp_rw [relaxedConductivity_restrict]
  exact (maskedPercolation_expectation U M p s (localRelaxedConductivity U i)).symm

theorem annealedMaskedB_eq_integral {d : ℕ} (U : Finset (Vertex d)) (i : Fin d)
    (M : Finset (IssuedBond U)) (p s : unitInterval) :
    annealedMaskedB U i M (p : ℝ) (s : ℝ) =
      ∫ ω, localMaskedB U i M ((issuedBondSet U).restrict ω)
        ∂maskedPercolation d (M.image Subtype.val) p s :=
  (maskedPercolation_expectation U M p s (localMaskedB U i M)).symm

/-- The literal law in eq.def.Pdelta, with E(bulk) rather than E+(bulk). -/
def bulkPercolation {d : ℕ} (U : Finset (Vertex d)) (i : Fin d) (h δ : ℝ)
    (p s : unitInterval) : Measure (Configuration d) :=
  maskedPercolation d (internalBondSet (bulkVertices U i h δ)) p s

lemma bulkPercolation_eq_masked {d : ℕ} (U : Finset (Vertex d)) (i : Fin d) (h δ : ℝ)
    (p s : unitInterval) : bulkPercolation U i h δ p s =
      maskedPercolation d ((bulkBondMask U i h δ).image Subtype.val) p s := by
  rw [bulkBondMask_image]
  rfl

/-- Source eq.proba.identity. -/
lemma bulkPercolation_self {d : ℕ} (U : Finset (Vertex d)) (i : Fin d) (h δ : ℝ)
    (p : unitInterval) : bulkPercolation U i h δ p p = percolation d p :=
  maskedPercolation_self _ _ _

/-- Source a-delta has the literal inhomogeneous infinite-law expectation. -/
theorem annealedBulkRelaxed_eq_integral {d : ℕ} (U : Finset (Vertex d)) (i : Fin d)
    (h δ : ℝ) (p s : unitInterval) :
    annealedMaskedRelaxed U i (bulkBondMask U i h δ) (p : ℝ) (s : ℝ) =
      ∫ ω, relaxedConductivity U i ω ∂bulkPercolation U i h δ p s := by
  rw [bulkPercolation_eq_masked]
  exact annealedMaskedRelaxed_eq_integral U i _ p s

/-- The new source differential inequality with its literal bulk edge mask. -/
theorem annealedBulkRelaxed_differential_inequality {d : ℕ} {U : Finset (Vertex d)}
    (hU : U.Nonempty) (i : Fin d) (h δ : ℝ) {p s : ℝ}
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (hs : 0 < s) (hs1 : s < 1) :
    deriv (annealedMaskedRelaxed U i (bulkBondMask U i h δ) p) s ≤
      Real.sqrt (annealedMaskedRelaxed U i (bulkBondMask U i h δ) p s) *
        Real.sqrt (annealedMaskedB U i (bulkBondMask U i h δ) p s) /
          (Real.sqrt s * (1-s)) :=
  annealedMaskedRelaxed_differential_inequality hU i _ hp hp1 hs hs1

/-- The masked auxiliary is exactly the literal source minimizer/circle integral,
including old-configuration voltages on closed tested edges. -/
theorem annealedMaskedB_eq_sourceIntegral {d : ℕ} (U : Finset (Vertex d)) (i : Fin d)
    (M : Finset (IssuedBond U)) (p s : unitInterval) :
    annealedMaskedB U i M (p : ℝ) (s : ℝ) =
      ∫ ω, sourceMaskedQuenchedB U i M ω
        ∂maskedPercolation d (M.image Subtype.val) p s := by
  rw [annealedMaskedB_eq_integral]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun ω ↦ maskedAuxiliary_restrict_eq_source U i M ω)

theorem annealedBulkB_eq_sourceIntegral {d : ℕ} (U : Finset (Vertex d)) (i : Fin d)
    (h δ : ℝ) (p s : unitInterval) :
    annealedMaskedB U i (bulkBondMask U i h δ) (p : ℝ) (s : ℝ) =
      ∫ ω, sourceMaskedQuenchedB U i (bulkBondMask U i h δ) ω
        ∂bulkPercolation U i h δ p s := by
  rw [bulkPercolation_eq_masked]
  exact annealedMaskedB_eq_sourceIntegral U i _ p s

/-- Literal original-law statement of source prop.inequality_diff_delta.
The only varied parameters are the bonds with BOTH endpoints in the bulk. -/
theorem bulk_source_differential_inequality {d : ℕ} {U : Finset (Vertex d)}
    (hU : U.Nonempty) (i : Fin d) (h δ : ℝ) (p s : unitInterval)
    (hs : 0 < (s : ℝ)) (hs1 : (s : ℝ) < 1) :
    deriv (annealedMaskedRelaxed U i (bulkBondMask U i h δ) (p : ℝ)) (s : ℝ) ≤
      Real.sqrt (∫ ω, relaxedConductivity U i ω ∂bulkPercolation U i h δ p s) *
        Real.sqrt (∫ ω, sourceMaskedQuenchedB U i (bulkBondMask U i h δ) ω
          ∂bulkPercolation U i h δ p s) / (Real.sqrt (s : ℝ) * (1-(s : ℝ))) := by
  rw [← annealedBulkRelaxed_eq_integral, ← annealedBulkB_eq_sourceIntegral]
  exact annealedBulkRelaxed_differential_inequality hU i h δ p.property.1 p.property.2 hs hs1

/-- In the source water cube the height is exactly 2r+1, not its radius. -/
theorem waterCube_bulk_source_differential_inequality (d : ℕ) (i : Fin d) (r R : ℕ)
    (δ : ℝ) (p s : unitInterval) (hs : 0 < (s : ℝ)) (hs1 : (s : ℝ) < 1) :
    deriv (annealedMaskedRelaxed (waterCube d i r R) i
      (bulkBondMask (waterCube d i r R) i (2*(r:ℝ)+1) δ) (p : ℝ)) (s : ℝ) ≤
      Real.sqrt (∫ ω, relaxedConductivity (waterCube d i r R) i ω
        ∂bulkPercolation (waterCube d i r R) i (2*(r:ℝ)+1) δ p s) *
        Real.sqrt (∫ ω, sourceMaskedQuenchedB (waterCube d i r R) i
          (bulkBondMask (waterCube d i r R) i (2*(r:ℝ)+1) δ) ω
          ∂bulkPercolation (waterCube d i r R) i (2*(r:ℝ)+1) δ p s) /
            (Real.sqrt (s : ℝ) * (1-(s : ℝ))) :=
  bulk_source_differential_inequality (waterCube_nonempty d i r R) i _ δ p s hs hs1

end NearCritical
