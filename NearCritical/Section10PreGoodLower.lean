module

public import NearCritical.Section10PreGoodCombine
public import NearCritical.PreGoodRegularBoundary

/-! Steps 1-2 of `prop.proba.pregood`, deterministic part, for the ACTUAL
typical family.

`CandidateCluster` collects the cluster-only conditions of Step 1 (heart
touching, spanning, volume window, face diameter, at least `2 c_b l0^2` points
on every split face, at most `C_b l0^2` on every face). A candidate that keeps
`c_b l0^2` REGULAR points on every split face (`regularityGoodCluster`) is a
typical cluster (`isTypical_of_candidate_good`). Hence
`typical_lower_count_failure`: the lower count fails only if there are fewer
than `L` candidates or at least `L/2` candidates lose regularity; these are the
conclusion shapes of `critical_spanningWindow_distinct_failure_rate` and
`literal_regularity_loss_from_energy_moments`. `hpre_of_candidate_counts`
feeds this into `hpre`.
-/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open scoped Classical
open MeasureTheory

/-- Regularity predicate of def.spanning.z at cube `z`. -/
def typRegular {d : ℕ} (typ : TypicalParameters) (t : ℕ) (z : Vertex d)
    (ω : Configuration d) : Vertex d → Prop :=
  sourceRegularPoint (heartClusterUnion ω (typicalCube t z)
    (typicalHeart t z typ.heartRatio)) (typicalInnerCube t z)
      (typicalBoundary t z) typ.regularRadius typ.regularTolerance

/-- The split faces as one family of patches. -/
def typPatch {d : ℕ} (t : ℕ) (z : Vertex d) (i : (Fin d × Bool) × Bool) : Finset (Vertex d) :=
  typicalSplitFace t z i.1 i.2

/-- Cluster-only conditions of Step 1 of the proof of prop.proba.pregood. -/
def CandidateCluster {d : ℕ} (typ : TypicalParameters) (t : ℕ) (z : Vertex d)
    (ω : Configuration d) (C : Finset (Vertex d)) : Prop :=
  (C ∩ typicalHeart t z typ.heartRatio).Nonempty ∧
  (∀ face : Fin d × Bool, (C ∩ typicalFace t z face).Nonempty) ∧
  typ.volumeLower * (2 * (t : ℝ))^4 < (C.card : ℝ) ∧
  (C.card : ℝ) < typ.volumeUpper * (2 * (t : ℝ))^4 ∧
  (spanningFaceDiameter (restrictedGraph ω (typicalCube t z : Set (Vertex d)))
    C (typicalFace t z) : ℝ) ≤ typ.diameterUpper * (2 * (t : ℝ))^2 ∧
  (∀ i : (Fin d × Bool) × Bool,
    2 * (typ.boundaryLower * (2 * (t : ℝ))^2) ≤ ((C ∩ typPatch t z i).card : ℝ)) ∧
  (∀ face : Fin d × Bool,
    ((C ∩ typicalFace t z face).card : ℝ) ≤ typ.boundaryUpper * (2 * (t : ℝ))^2)

theorem isTypical_of_candidate_good {d : ℕ} (typ : TypicalParameters) (t : ℕ) (z : Vertex d)
    (ω : Configuration d) (C : Finset (Vertex d))
    (hC : C ∈ finiteClusterFamily ω (typicalCube t z))
    (hgood : regularityGoodCluster (CandidateCluster typ t z ω) (typPatch t z)
      (typRegular typ t z ω) (typ.boundaryLower * (2 * (t : ℝ))^2) C) :
    IsTypicalCluster typ t z ω C := by
  obtain ⟨⟨hheart, hspan, hvl, hvu, hdiam, _, hface⟩, hreg⟩ :=
    (regularityGoodCluster_iff _ _ _ _ C).mp hgood
  refine ⟨component_subset_heartUnion_of_meets ω _ _ C hC hheart, hspan, hvl, hvu, hdiam,
    ?_, hface⟩
  intro face plus
  have hpatch : typicalRegularPatch typ t z ω C face plus =
      (C ∩ typPatch t z (face, plus)).filter (typRegular typ t z ω) := rfl
  rw [hpatch]
  refine ⟨hreg (face, plus), ?_⟩
  have hsub : (C ∩ typPatch t z (face, plus)).filter (typRegular typ t z ω) ⊆
      C ∩ typicalFace t z face := by
    intro x hx
    obtain ⟨hxC, hxp⟩ := Finset.mem_inter.mp (Finset.mem_filter.mp hx).1
    exact Finset.mem_inter.mpr ⟨hxC, (Finset.mem_filter.mp hxp).1⟩
  have hcard : (((C ∩ typPatch t z (face, plus)).filter (typRegular typ t z ω)).card : ℝ) ≤
      ((C ∩ typicalFace t z face).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  exact hcard.trans (hface face)

theorem candidate_good_card_le_typical {d : ℕ} (typ : TypicalParameters) (t : ℕ)
    (z : Vertex d) (ω : Configuration d) :
    (filteredClusterFamily ω (typicalCube t z)
      (regularityGoodCluster (CandidateCluster typ t z ω) (typPatch t z)
        (typRegular typ t z ω) (typ.boundaryLower * (2 * (t : ℝ))^2))).card ≤
      (typicalClusterFamily typ t z ω).card := by
  refine Finset.card_le_card (fun C hC => ?_)
  have hC' : C ∈ finiteClusterFamily ω (typicalCube t z) ∧
      regularityGoodCluster (CandidateCluster typ t z ω) (typPatch t z)
        (typRegular typ t z ω) (typ.boundaryLower * (2 * (t : ℝ))^2) C := by
    unfold filteredClusterFamily at hC
    exact Finset.mem_filter.mp hC
  exact (mem_typicalClusterFamily typ t z ω C).mpr
    ⟨hC'.1, isTypical_of_candidate_good typ t z ω C hC'.1 hC'.2⟩

/-- **Lower count of prop.proba.pregood from the two source loss events.** -/
theorem typical_lower_count_failure {d : ℕ} (p : unitInterval) (typ : TypicalParameters)
    (t : ℕ) (z : Vertex d) {L η₁ η₂ : ℝ}
    (hL : typ.countLower * (2 * (t : ℝ)) ^ (d - 6) ≤ L / 2)
    (hcand : (percolation d p).real {ω | ¬ L ≤
      ((filteredClusterFamily ω (typicalCube t z) (CandidateCluster typ t z ω)).card : ℝ)} ≤ η₁)
    (hloss : (percolation d p).real {ω | L / 2 ≤
      ((filteredClusterFamily ω (typicalCube t z)
        (regularityBadCluster (CandidateCluster typ t z ω) (typPatch t z)
          (typRegular typ t z ω) (typ.boundaryLower * (2 * (t : ℝ))^2))).card : ℝ)} ≤ η₂) :
    (percolation d p).real
      {ω | ¬ typ.countLower * (2 * (t : ℝ)) ^ (d - 6) ≤
        ((typicalClusterFamily typ t z ω).card : ℝ)} ≤ η₁ + η₂ := by
  have hsub : {ω : Configuration d | ¬ typ.countLower * (2 * (t : ℝ)) ^ (d - 6) ≤
        ((typicalClusterFamily typ t z ω).card : ℝ)} ⊆
      {ω | ¬ L ≤
        ((filteredClusterFamily ω (typicalCube t z) (CandidateCluster typ t z ω)).card : ℝ)} ∪
      {ω | L / 2 ≤
        ((filteredClusterFamily ω (typicalCube t z)
          (regularityBadCluster (CandidateCluster typ t z ω) (typPatch t z)
            (typRegular typ t z ω) (typ.boundaryLower * (2 * (t : ℝ))^2))).card : ℝ)} := by
    intro ω hω
    by_contra hne
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_le] at hne
    apply hω
    have hgood := regularity_good_count_lower ω (typicalCube t z) (CandidateCluster typ t z ω)
      (typPatch t z) (typRegular typ t z ω) (typ.boundaryLower * (2 * (t : ℝ))^2) L (not_lt.mp hne.1) hne.2
    have hle : ((filteredClusterFamily ω (typicalCube t z)
        (regularityGoodCluster (CandidateCluster typ t z ω) (typPatch t z)
          (typRegular typ t z ω) (typ.boundaryLower * (2 * (t : ℝ))^2))).card : ℝ) ≤
        ((typicalClusterFamily typ t z ω).card : ℝ) := by
      exact_mod_cast candidate_good_card_le_typical typ t z ω
    linarith
  have h1 := (measureReal_mono (μ := percolation d p) hsub
    (measure_ne_top (percolation d p) _)).trans (measureReal_union_le _ _)
  linarith

/-- **`hpre` from the candidate count and the regularity loss at the origin cube.** -/
theorem hpre_of_candidate_counts {d : ℕ} (i : Fin d) (hd : 6 ≤ d) (typ : TypicalParameters)
    (t : ℕ) (ht : 3 ≤ t) {C ε L η₁ η₂ : ℝ} (hC : 0 < C)
    (ordinary : OrdinaryArmWindowInput d C)
    (hv : 0 < typ.volumeLower) (hε : 0 < ε)
    (hup : 27 * C / (typ.volumeLower * ε) ≤ typ.countUpper)
    (hL : typ.countLower * (2 * (t : ℝ)) ^ (d - 6) ≤ L / 2)
    (hcand : (percolation d (criticalPoint d)).real {ω | ¬ L ≤
      ((filteredClusterFamily ω (typicalCube t (0 : Vertex d))
        (CandidateCluster typ t 0 ω)).card : ℝ)} ≤ η₁)
    (hloss : (percolation d (criticalPoint d)).real {ω | L / 2 ≤
      ((filteredClusterFamily ω (typicalCube t (0 : Vertex d))
        (regularityBadCluster (CandidateCluster typ t 0 ω) (typPatch t 0)
          (typRegular typ t 0 ω) (typ.boundaryLower * (2 * (t : ℝ))^2))).card : ℝ)} ≤ η₂)
    (a : Vertex d) :
    1 - (η₁ + η₂) - ε / 3 ≤ ∫ ω, (if IsPreGoodCube typ t a ω then (1:ℝ) else 0)
      ∂(percolation d (criticalPoint d)) :=
  hpre_of_lower_count i hd typ t ht hC ordinary hv hε hup
    (typical_lower_count_failure _ typ t 0 hL hcand hloss) a

end NearCritical.Section10
