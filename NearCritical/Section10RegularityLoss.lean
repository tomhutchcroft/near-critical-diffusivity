module

public import NearCritical.Section10PreGoodLower
public import NearCritical.PreGoodEnergyLoss

/-! `hloss` of `hpre_of_candidate_counts` for the origin typical cube, reduced to
the regularity energy moments.

`typMark t z` is the union of the split faces. `hloss_of_energy_moments`
instantiates `literal_regularity_loss_from_energy_moments` with `Q` the typical
cube, the typical heart, `excluded` the inner cube, the full cube boundary, the
candidate predicate, `n = 2t`, `c = 2 boundaryLower`. The structural hypotheses
(`hmeet`, `hpatch`, the three inclusions) are discharged from `CandidateCluster`.

Left as hypotheses: the two conditional means, the centred second moments, the
boundary hitting probability and the cardinality of the marked boundary
(source ERE1/ERE2 moment estimates; NOT derived here).
-/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open MeasureTheory
open scoped Classical

/-- Union of the split faces of the typical cube. -/
def typMark {d : ℕ} (t : ℕ) (z : Vertex d) : Finset (Vertex d) :=
  Finset.univ.biUnion (typPatch t z)

theorem typMark_subset_boundary {d : ℕ} (t : ℕ) (z : Vertex d) :
    typMark t z ⊆ typicalBoundary t z := by
  intro x hx
  obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hx
  exact Finset.mem_biUnion.mpr ⟨i.1, Finset.mem_univ _, Finset.filter_subset _ _ hi⟩

theorem typMark_subset_cube {d : ℕ} (t : ℕ) (z : Vertex d) :
    typMark t z ⊆ typicalCube t z := by
  intro x hx
  obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp (typMark_subset_boundary t z hx)
  exact Finset.filter_subset _ _ hi

theorem hloss_of_energy_moments {d : ℕ} (hd : 7 ≤ d) (typ : TypicalParameters) (t : ℕ)
    (ht : 1 ≤ t) (hr : 1 ≤ typ.regularRadius) (hδ : 0 < typ.regularTolerance)
    (hbL : 0 < typ.boundaryLower) {Cv Cp Cb c1 : ℝ} (hCv : 0 ≤ Cv) (hCp : 0 ≤ Cp)
    (hc1 : 0 < c1)
    (hm1 : ∀ x ∈ typMark t (0 : Vertex d),
      heartConditionalMean (criticalPoint d) (typicalCube t 0)
        (typicalHeart t 0 typ.heartRatio)
        (fun F => regularityEnergyOne F (typicalInnerCube t 0) typ.regularRadius x) x ≤
          typ.regularTolerance / 2)
    (hm2 : ∀ x ∈ typMark t (0 : Vertex d),
      heartConditionalMean (criticalPoint d) (typicalCube t 0)
        (typicalHeart t 0 typ.heartRatio)
        (fun F => regularityEnergyTwo F (typicalBoundary t 0) typ.regularRadius x) x ≤
          typ.regularTolerance / 2)
    (hvar : ∀ x ∈ typMark t (0 : Vertex d),
      heartCenteredMoment (criticalPoint d) (typicalCube t 0)
        (typicalHeart t 0 typ.heartRatio)
        (fun F => regularityEnergyOne F (typicalInnerCube t 0) typ.regularRadius x) x +
      heartCenteredMoment (criticalPoint d) (typicalCube t 0)
        (typicalHeart t 0 typ.heartRatio)
        (fun F => regularityEnergyTwo F (typicalBoundary t 0) typ.regularRadius x) x ≤
      (Cv / (typ.regularRadius : ℝ) ^ (d - 6)) * (percolation d (criticalPoint d)).real
        {ω | x ∈ heartClusterUnion ω (typicalCube t 0) (typicalHeart t 0 typ.heartRatio)})
    (hhit : ∀ x ∈ typMark t (0 : Vertex d), (percolation d (criticalPoint d)).real
        {ω | x ∈ heartClusterUnion ω (typicalCube t 0) (typicalHeart t 0 typ.heartRatio)} ≤
      Cp / (2 * (t : ℝ)) ^ 3)
    (hcard : ((typMark t (0 : Vertex d)).card : ℝ) ≤ Cb * (2 * (t : ℝ)) ^ (d - 1)) :
    (percolation d (criticalPoint d)).real {ω | c1 * (2 * (t : ℝ)) ^ (d - 6) / 2 ≤
      ((filteredClusterFamily ω (typicalCube t (0 : Vertex d))
        (regularityBadCluster (CandidateCluster typ t 0 ω) (typPatch t 0)
          (typRegular typ t 0 ω) (typ.boundaryLower * (2 * (t : ℝ)) ^ 2))).card : ℝ)} ≤
    16 * Cv * Cp * Cb / (typ.regularTolerance ^ 2 * (2 * typ.boundaryLower) * c1 *
      (typ.regularRadius : ℝ) ^ (d - 6)) := by
  have e : ((2 * t : ℕ) : ℝ) = 2 * (t : ℝ) := by push_cast; ring
  have h := literal_regularity_loss_from_energy_moments (criticalPoint d)
    (typicalCube t (0 : Vertex d)) (typicalHeart t 0 typ.heartRatio) (typicalInnerCube t 0)
    (typicalBoundary t 0) (typMark t 0) (typMark_subset_cube t 0) (typMark_subset_boundary t 0)
    (CandidateCluster typ t 0) (typPatch t 0)
    (fun i => Finset.subset_biUnion_of_mem _ (Finset.mem_univ i))
    (fun ω C hC => by
      unfold filteredClusterFamily at hC
      exact (Finset.mem_filter.mp hC).2.1)
    typ.regularRadius (2 * t) hr (by omega) hd hδ hCv hCp
    (show (0:ℝ) < 2 * typ.boundaryLower by linarith) hc1 hm1 hm2 hvar
    (fun x hx => by rw [e]; exact hhit x hx) (by rw [e]; exact hcard)
    (fun ω C hC i => by
      unfold filteredClusterFamily at hC
      have h6 := (Finset.mem_filter.mp hC).2.2.2.2.2.2.1 i
      rw [e]
      linarith)
  rw [e] at h
  have e2 : 2 * typ.boundaryLower / 2 = typ.boundaryLower := by ring
  have e3 : c1 / 2 * (2 * (t : ℝ)) ^ (d - 6) = c1 * (2 * (t : ℝ)) ^ (d - 6) / 2 := by ring
  rw [e2, e3] at h
  exact h

end NearCritical.Section10
