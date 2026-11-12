module

public import NearCritical.ClusterDistinctCount

/-! Transfer lower-count conclusions from components hitting an interior root
region to the source whole filtered component family. Actual component labels
are retained; no representative or multiplicity hypothesis is introduced. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory Set
open scoped Classical

/-- Removing the requirement of hitting Z only enlarges the actual selected
component family. The graph property is evaluated on the same induced graph. -/
theorem selectedPropertyComponents_subset_whole {d : ℕ}
    (U Z : Finset (Vertex d)) (hZ : Z ⊆ U)
    (P : SimpleGraph (Vertex d) → Finset (Vertex d) → Prop) (ω : Configuration d) :
    selectedPropertyComponents U Z P ω ⊆
      filteredClusterFamily ω U (fun C => P (restrictedGraph ω (C : Set (Vertex d))) C) := by
  rw [selectedPropertyComponents_eq_filtered_family U Z hZ P ω]
  intro C hC
  simp only [filteredClusterFamily,Finset.mem_filter] at hC ⊢
  exact ⟨hC.1,hC.2.1⟩

/-- Actual full-family lower-count failure is contained in the failure for
components meeting the chosen root region. Valid for outer probabilities too. -/
theorem wholePropertyFamily_failure_le_selected {d : ℕ} (p : unitInterval)
    (U Z : Finset (Vertex d)) (hZ : Z ⊆ U)
    (P : SimpleGraph (Vertex d) → Finset (Vertex d) → Prop) (t : ℝ) :
    (percolation d p).real {ω |
      ((filteredClusterFamily ω U
        (fun C => P (restrictedGraph ω (C : Set (Vertex d))) C)).card:ℝ) ≤ t} ≤
      (percolation d p).real {ω | ((selectedPropertyComponents U Z P ω).card:ℝ) ≤ t} := by
  refine measureReal_mono (μ := percolation d p) ?_ (by finiteness)
  intro ω hω
  have hc : (selectedPropertyComponents U Z P ω).card ≤
      (filteredClusterFamily ω U (fun C => P (restrictedGraph ω (C : Set (Vertex d))) C)).card :=
    Finset.card_le_card (selectedPropertyComponents_subset_whole U Z hZ P ω)
  have hr : ((selectedPropertyComponents U Z P ω).card:ℝ) ≤
      ((filteredClusterFamily ω U (fun C => P (restrictedGraph ω (C : Set (Vertex d))) C)).card:ℝ) := by
    exact_mod_cast hc
  exact hr.trans hω

/-- Source whole-family success is at least one minus the actual selected-root
failure. This uses a union cover and needs no unstated complement-measurability
argument for an arbitrary component graph predicate. -/
theorem wholePropertyFamily_success_ge_one_sub_failure {d : ℕ} (p : unitInterval)
    (U Z : Finset (Vertex d)) (hZ : Z ⊆ U)
    (P : SimpleGraph (Vertex d) → Finset (Vertex d) → Prop) (t : ℝ) :
    1-(percolation d p).real {ω | ((selectedPropertyComponents U Z P ω).card:ℝ) ≤ t} ≤
      (percolation d p).real {ω | t ≤
        ((filteredClusterFamily ω U
          (fun C => P (restrictedGraph ω (C : Set (Vertex d))) C)).card:ℝ)} := by
  have hcover : (Set.univ : Set (Configuration d)) ⊆
      {ω | ((filteredClusterFamily ω U
        (fun C => P (restrictedGraph ω (C : Set (Vertex d))) C)).card:ℝ) ≤ t} ∪
      {ω | t ≤ ((filteredClusterFamily ω U
        (fun C => P (restrictedGraph ω (C : Set (Vertex d))) C)).card:ℝ)} := by
    intro ω _hω
    change ((filteredClusterFamily ω U
      (fun C => P (restrictedGraph ω (C : Set (Vertex d))) C)).card:ℝ) ≤ t ∨
      t ≤ ((filteredClusterFamily ω U
        (fun C => P (restrictedGraph ω (C : Set (Vertex d))) C)).card:ℝ)
    exact le_total _ _
  have h := (measureReal_mono (μ := percolation d p) hcover).trans (measureReal_union_le _ _)
  have hfail := wholePropertyFamily_failure_le_selected p U Z hZ P t
  have hu : (percolation d p).real Set.univ = 1 := by simp
  rw [hu] at h
  linarith

end NearCritical
