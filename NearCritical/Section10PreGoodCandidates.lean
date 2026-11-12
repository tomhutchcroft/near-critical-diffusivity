module

public import NearCritical.Section10PreGoodLower
public import NearCritical.ClusterSpanningCountRate
public import NearCritical.FiniteClusterMetric

/-! Step 1 of `prop.proba.pregood`: the candidate count from the spanning-window
second-moment rate, for the ACTUAL origin cube.

`StepOneProperty` is the graph property (face diameter, split-face lower
counts, face upper counts). Components selected by the window property with a
root in the heart are candidates (`selected_card_le_candidates`), so
`hcand_of_raw` turns `critical_spanningWindow_distinct_failure_rate` into the
hypothesis `hcand` of `hpre_of_candidate_counts`. The raw probabilistic inputs
(spanning probability two-sided, property probability, small-volume control)
remain hypotheses.
-/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open scoped Classical
open MeasureTheory

lemma spanningFaceDiameter_congr {ι : Type*} [Fintype ι] [DecidableEq ι] {d : ℕ}
    (G G' : SimpleGraph (Vertex d)) (C : Finset (Vertex d)) (faces : ι → Finset (Vertex d))
    (h : ∀ x ∈ C, ∀ y ∈ C, G.dist x y = G'.dist x y) :
    spanningFaceDiameter G C faces = spanningFaceDiameter G' C faces := by
  unfold spanningFaceDiameter
  refine Finset.sup_congr rfl (fun p _ => Finset.sup_congr rfl (fun xy hxy => ?_))
  obtain ⟨h1, h2⟩ := Finset.mem_product.mp hxy
  exact h xy.1 (Finset.mem_inter.mp h1).1 xy.2 (Finset.mem_inter.mp h2).1

/-- Graph property of Step 1 (diameter and boundary counts) at cube `z`. -/
def StepOneProperty {d : ℕ} (typ : TypicalParameters) (t : ℕ) (z : Vertex d)
    (G : SimpleGraph (Vertex d)) (C : Finset (Vertex d)) : Prop :=
  (spanningFaceDiameter G C (typicalFace t z) : ℝ) ≤ typ.diameterUpper * (2 * (t : ℝ))^2 ∧
  (∀ i : (Fin d × Bool) × Bool,
    2 * (typ.boundaryLower * (2 * (t : ℝ))^2) ≤ ((C ∩ typPatch t z i).card : ℝ)) ∧
  (∀ face : Fin d × Bool,
    ((C ∩ typicalFace t z face).card : ℝ) ≤ typ.boundaryUpper * (2 * (t : ℝ))^2)

theorem candidate_of_selected {d : ℕ} (typ : TypicalParameters) (t : ℕ) (z : Vertex d)
    (ω : Configuration d) {B : ℝ} (hB : B ≤ typ.volumeUpper * (2 * (t : ℝ))^4)
    (C : Finset (Vertex d)) (hC : C ∈ finiteClusterFamily ω (typicalCube t z))
    (hW : spanningWindowProperty (typicalFace t z) (StepOneProperty typ t z)
      (typ.volumeLower * (2 * (t : ℝ))^4) B (restrictedGraph ω (C : Set (Vertex d))) C)
    (hmeet : (C ∩ typicalHeart t z typ.heartRatio).Nonempty) :
    CandidateCluster typ t z ω C := by
  obtain ⟨⟨hdiam, hpatch, hface⟩, hspan, hlo, hhi⟩ := hW
  refine ⟨hmeet, hspan, hlo, hhi.trans_le hB, ?_, hpatch, hface⟩
  have heq : spanningFaceDiameter (restrictedGraph ω (typicalCube t z : Set (Vertex d))) C
      (typicalFace t z) =
      spanningFaceDiameter (restrictedGraph ω (C : Set (Vertex d))) C (typicalFace t z) := by
    refine spanningFaceDiameter_congr _ _ C _ (fun x hx y hy => ?_)
    have hrec := finiteClusterFamily_recover ω (typicalCube t z) hC hx
    have h := finiteBoxCluster_dist_eq ω (typicalCube t z) x (x := x) (y := y)
      (by rw [hrec]; exact hx) (by rw [hrec]; exact hy)
    rw [hrec] at h
    exact h.symm
  rw [heq]
  exact hdiam

theorem selected_card_le_candidates {d : ℕ} (typ : TypicalParameters) (t : ℕ) (z : Vertex d)
    (ω : Configuration d) {B : ℝ} (hB : B ≤ typ.volumeUpper * (2 * (t : ℝ))^4) :
    (selectedPropertyComponents (typicalCube t z) (typicalHeart t z typ.heartRatio)
      (spanningWindowProperty (typicalFace t z) (StepOneProperty typ t z)
        (typ.volumeLower * (2 * (t : ℝ))^4) B) ω).card ≤
      (filteredClusterFamily ω (typicalCube t z) (CandidateCluster typ t z ω)).card := by
  have hH : typicalHeart t z typ.heartRatio ⊆ typicalCube t z :=
    fun x hx => (Finset.mem_filter.mp hx).1
  refine Finset.card_le_card (fun C hC => ?_)
  obtain ⟨r, hrR, rfl⟩ := Finset.mem_image.mp hC
  obtain ⟨hrZ, hrP⟩ := Finset.mem_filter.mp hrR
  have hCF : finiteBoxCluster ω (typicalCube t z) r ∈ finiteClusterFamily ω (typicalCube t z) :=
    (mem_finiteClusterFamily ω _ _).mpr ⟨r, hH hrZ, rfl⟩
  unfold filteredClusterFamily
  exact Finset.mem_filter.mpr ⟨hCF, candidate_of_selected typ t z ω hB _ hCF hrP
    ⟨r, Finset.mem_inter.mpr ⟨root_mem_finiteBoxCluster ω _ (hH hrZ), hrZ⟩⟩⟩

/-- `hcand` from a lower-tail bound for the selected window components. -/
theorem hcand_of_selected_rate {d : ℕ} (p : unitInterval) (typ : TypicalParameters) (t : ℕ)
    (z : Vertex d) {B K L η : ℝ} (hB : B ≤ typ.volumeUpper * (2 * (t : ℝ))^4) (hL : L ≤ K)
    (hrate : (percolation d p).real {ω |
      ((selectedPropertyComponents (typicalCube t z) (typicalHeart t z typ.heartRatio)
        (spanningWindowProperty (typicalFace t z) (StepOneProperty typ t z)
          (typ.volumeLower * (2 * (t : ℝ))^4) B) ω).card : ℝ) ≤ K} ≤ η) :
    (percolation d p).real {ω | ¬ L ≤
      ((filteredClusterFamily ω (typicalCube t z) (CandidateCluster typ t z ω)).card : ℝ)} ≤ η := by
  refine (measureReal_mono (μ := percolation d p) ?_ (measure_ne_top (percolation d p) _)).trans
    hrate
  intro ω hω
  have h1 : ((filteredClusterFamily ω (typicalCube t z) (CandidateCluster typ t z ω)).card : ℝ)
      < L := not_le.mp hω
  have h2 : ((selectedPropertyComponents (typicalCube t z) (typicalHeart t z typ.heartRatio)
        (spanningWindowProperty (typicalFace t z) (StepOneProperty typ t z)
          (typ.volumeLower * (2 * (t : ℝ))^4) B) ω).card : ℝ) ≤
      ((filteredClusterFamily ω (typicalCube t z) (CandidateCluster typ t z ω)).card : ℝ) := by
    exact_mod_cast selected_card_le_candidates typ t z ω hB
  show _ ≤ K
  linarith

/-- **Candidate count of Step 1 from the raw spanning inputs** (origin cube,
`N = (t-1)/2`, roots in the heart). -/
theorem hcand_of_raw {d : ℕ} (hd : 9 ≤ d) (hA : TwoPointAsymptotics d) (δ c Cs cz Cz : ℝ)
    (hδ : 0 < δ) (hc : 0 < c) (hCs : 0 ≤ Cs) (hcz : 0 < cz) (hCz : 0 ≤ Cz) :
    ∃ C D : ℝ, 0 < C ∧ 0 < D ∧
      ∀ (typ : TypicalParameters) (t N : ℕ), 1 ≤ t → (t - 1) / 2 = N →
      C * (N + 1 : ℝ)^4 ≤ typ.volumeUpper * (2 * (t : ℝ))^4 →
      cz * (N + 1 : ℝ)^d ≤ ((typicalHeart t (0 : Vertex d) typ.heartRatio).card : ℝ) →
      ((typicalHeart t (0 : Vertex d) typ.heartRatio).card : ℝ) ≤ Cz * (N + 1 : ℝ)^d →
      (∀ x ∈ typicalHeart t (0 : Vertex d) typ.heartRatio,
        c / (N + 1 : ℝ)^2 ≤ (percolation d (criticalPoint d)).real
          (finiteRootSpanningEvent (centeredBox d N) (typicalFace t (0 : Vertex d)) x)) →
      (∀ x ∈ typicalHeart t (0 : Vertex d) typ.heartRatio,
        (percolation d (criticalPoint d)).real
          (finiteRootSpanningEvent (centeredBox d N) (typicalFace t (0 : Vertex d)) x) ≤
            Cs / (N + 1 : ℝ)^2) →
      (∀ x ∈ typicalHeart t (0 : Vertex d) typ.heartRatio,
        δ * (percolation d (criticalPoint d)).real
          (finiteRootSpanningEvent (centeredBox d N) (typicalFace t (0 : Vertex d)) x) ≤
        (percolation d (criticalPoint d)).real
          ({ω | rootedClusterProperty (centeredBox d N) x (StepOneProperty typ t 0) ω} ∩
            finiteRootSpanningEvent (centeredBox d N) (typicalFace t (0 : Vertex d)) x)) →
      (∀ x ∈ typicalHeart t (0 : Vertex d) typ.heartRatio,
        (percolation d (criticalPoint d)).real
          ({ω | ((finiteBoxCluster ω (centeredBox d N) x).card : ℝ) ≤
              typ.volumeLower * (2 * (t : ℝ))^4} ∩
            finiteRootSpanningEvent (centeredBox d N) (typicalFace t (0 : Vertex d)) x) ≤
        (δ / 4) * (percolation d (criticalPoint d)).real
          (finiteRootSpanningEvent (centeredBox d N) (typicalFace t (0 : Vertex d)) x)) →
      ∀ L : ℝ, L ≤ ((δ * c * cz / 4) / C) * (N + 1 : ℝ)^(d - 6) →
      (percolation d (criticalPoint d)).real {ω | ¬ L ≤
        ((filteredClusterFamily ω (typicalCube t (0 : Vertex d))
          (CandidateCluster typ t 0 ω)).card : ℝ)} ≤ D / (N + 1 : ℝ)^(d - 8) := by
  obtain ⟨C, D, hC, hD, hrate⟩ :=
    critical_spanningWindow_distinct_failure_rate hd hA δ c Cs cz Cz hδ hc hCs hcz hCz
  refine ⟨C, D, hC, hD, ?_⟩
  intro typ t N ht hN hB hzlo hzhi hspanlo hspanhi hprop hlow L hL
  have hcube : typicalCube t (0 : Vertex d) = centeredBox d N := by
    rw [typicalCube_zero t ht, hN]
  have hZ : typicalHeart t (0 : Vertex d) typ.heartRatio ⊆ centeredBox d N := by
    intro x hx
    rw [← hcube]
    exact (Finset.mem_filter.mp hx).1
  have h := hrate N (typicalHeart t (0 : Vertex d) typ.heartRatio) hZ hzlo hzhi
    (Fin d × Bool) (typicalFace t (0 : Vertex d)) (StepOneProperty typ t 0)
    (typ.volumeLower * (2 * (t : ℝ))^4) hspanlo hspanhi hprop hlow
  refine hcand_of_selected_rate _ typ t 0 hB hL ?_
  rw [hcube]
  exact h

end NearCritical.Section10
