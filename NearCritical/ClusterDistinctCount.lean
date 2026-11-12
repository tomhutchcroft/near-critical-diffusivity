module

public import NearCritical.ClusterCountConcentration

/-! Source prop.num_spanning_new Step3: actual rooted multiplicity count is
converted to a distinct-component count using the actual volume cap. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory ProbabilityTheory
open scoped Classical

def selectedPropertyRoots {d : ℕ} (U Z : Finset (Vertex d))
    (P : SimpleGraph (Vertex d) → Finset (Vertex d) → Prop) (ω : Configuration d) :
    Finset (Vertex d) := Z.filter (fun r => rootedClusterProperty U r P ω)

/-- Finite image deduplicates repeated selected roots in the same actual component. -/
def selectedPropertyComponents {d : ℕ} (U Z : Finset (Vertex d))
    (P : SimpleGraph (Vertex d) → Finset (Vertex d) → Prop) (ω : Configuration d) :
    Finset (Finset (Vertex d)) :=
  (selectedPropertyRoots U Z P ω).image (finiteBoxCluster ω U)

/-- The image definition is exactly the existing actual component family,
filtered by graph-property and intersection with the selected root region. -/
theorem selectedPropertyComponents_eq_filtered_family {d : ℕ}
    (U Z : Finset (Vertex d)) (hZU : Z ⊆ U)
    (P : SimpleGraph (Vertex d) → Finset (Vertex d) → Prop) (ω : Configuration d) :
    selectedPropertyComponents U Z P ω = filteredClusterFamily ω U
      (fun C => P (restrictedGraph ω (C : Set (Vertex d))) C ∧ (C ∩ Z).Nonempty) := by
  ext C
  constructor
  · intro hC
    obtain ⟨r, hrR, rfl⟩ := Finset.mem_image.mp hC
    obtain ⟨hrZ, hrP⟩ := Finset.mem_filter.mp hrR
    simp only [filteredClusterFamily,Finset.mem_filter]
    refine ⟨(mem_finiteClusterFamily ω U _).mpr ⟨r, hZU hrZ, rfl⟩, hrP, ?_⟩
    exact ⟨r, Finset.mem_inter.mpr ⟨root_mem_finiteBoxCluster ω U (hZU hrZ), hrZ⟩⟩
  · intro hC
    simp only [filteredClusterFamily,Finset.mem_filter] at hC
    obtain ⟨hCF, hPC, hmeet⟩ := hC
    obtain ⟨r, hr⟩ := hmeet
    obtain ⟨hrC, hrZ⟩ := Finset.mem_inter.mp hr
    have hc := finiteClusterFamily_recover ω U hCF hrC
    apply Finset.mem_image.mpr
    refine ⟨r, Finset.mem_filter.mpr ⟨hrZ, ?_⟩, hc⟩
    simpa only [rootedClusterProperty, hc] using hPC

lemma rootedPropertyCount_eq_selected_card {d : ℕ} (U Z : Finset (Vertex d))
    (P : SimpleGraph (Vertex d) → Finset (Vertex d) → Prop) (ω : Configuration d) :
    rootedPropertyCount U Z P ω = ((selectedPropertyRoots U Z P ω).card:ℝ) := by
  simp only [rootedPropertyCount, rootedPropertyIndicator, selectedPropertyRoots]
  rw [Finset.sum_boole]

/-- Every selected root in the fiber labelled C belongs to C itself. This is
actual component membership, not a supplied multiplicity bound. -/
lemma selectedProperty_fiber_subset {d : ℕ} (U Z : Finset (Vertex d)) (hZU : Z ⊆ U)
    (P : SimpleGraph (Vertex d) → Finset (Vertex d) → Prop) (ω : Configuration d)
    (C : Finset (Vertex d)) :
    (selectedPropertyRoots U Z P ω).filter (fun r => finiteBoxCluster ω U r = C) ⊆ C := by
  intro r hr
  obtain ⟨hrR, hC⟩ := Finset.mem_filter.mp hr
  have hrZ : r ∈ Z := (Finset.mem_filter.mp hrR).1
  have hroot := root_mem_finiteBoxCluster ω U (hZU hrZ)
  simpa only [hC] using hroot

/-- Literal source N<=V*number-of-distinct-components. The fiber cardinal
bound is derived from actual root membership and the raw selected volume cap. -/
theorem rootedPropertyCount_le_volume_mul_distinct {d : ℕ}
    (U Z : Finset (Vertex d)) (hZU : Z ⊆ U)
    (P : SimpleGraph (Vertex d) → Finset (Vertex d) → Prop) (ω : Configuration d)
    {V : ℝ} (hcap : ∀ r ∈ Z, rootedClusterProperty U r P ω →
      ((finiteBoxCluster ω U r).card:ℝ) ≤ V) :
    rootedPropertyCount U Z P ω ≤ V*((selectedPropertyComponents U Z P ω).card:ℝ) := by
  let R := selectedPropertyRoots U Z P ω
  let F := selectedPropertyComponents U Z P ω
  have hc : R.card = ∑ C ∈ F, (R.filter (fun r => finiteBoxCluster ω U r = C)).card :=
    Finset.card_eq_sum_card_image (finiteBoxCluster ω U) R
  have hreal : (R.card:ℝ) =
      ∑ C ∈ F, ((R.filter (fun r => finiteBoxCluster ω U r = C)).card:ℝ) := by
    exact_mod_cast hc
  have hf (C : Finset (Vertex d)) (hC : C ∈ F) :
      ((R.filter (fun r => finiteBoxCluster ω U r = C)).card:ℝ) ≤ V := by
    obtain ⟨r, hrR, he⟩ := Finset.mem_image.mp hC
    obtain ⟨hrZ, hrP⟩ := Finset.mem_filter.mp hrR
    have hV : (C.card:ℝ) ≤ V := by simpa only [he] using hcap r hrZ hrP
    have hs : ((R.filter (fun r => finiteBoxCluster ω U r = C)).card:ℝ) ≤ (C.card:ℝ) := by
      exact_mod_cast Finset.card_le_card (selectedProperty_fiber_subset U Z hZU P ω C)
    exact hs.trans hV
  calc
    _ = (R.card:ℝ) := rootedPropertyCount_eq_selected_card U Z P ω
    _ = ∑ C ∈ F, ((R.filter (fun r => finiteBoxCluster ω U r = C)).card:ℝ) := hreal
    _ ≤ ∑ _C ∈ F, V := Finset.sum_le_sum hf
    _ = _ := by simp [F, mul_comm]

/-- The source distinct-count failure is contained in the actual rooted-count
failure. No distinct-count measurability or failure estimate is assumed. -/
theorem selectedPropertyComponents_lower_tail_subset {d : ℕ}
    (U Z : Finset (Vertex d)) (hZU : Z ⊆ U)
    (P : SimpleGraph (Vertex d) → Finset (Vertex d) → Prop) {V : ℝ} (hV : 0 < V)
    (hcap : ∀ ω r, r ∈ Z → rootedClusterProperty U r P ω →
      ((finiteBoxCluster ω U r).card:ℝ) ≤ V) (a : ℝ) :
    {ω | ((selectedPropertyComponents U Z P ω).card:ℝ) ≤ a/V} ⊆
      {ω | rootedPropertyCount U Z P ω ≤ a} := by
  intro ω hω
  have hprod := (le_div_iff₀ hV).mp hω
  have hcount := rootedPropertyCount_le_volume_mul_distinct U Z hZU P ω (hcap ω)
  exact hcount.trans (by simpa only [mul_comm] using hprod)

/-- Actual distinct-component lower-tail bound from the derived count moments.
The volume cap is raw component data, not a supplied root-to-distinct bound. -/
theorem selectedPropertyComponents_relative_lower_tail {d : ℕ} (p : unitInterval)
    (U Z : Finset (Vertex d)) (hZU : Z ⊆ U)
    (P : SimpleGraph (Vertex d) → Finset (Vertex d) → Prop) {V : ℝ} (hV : 0 < V)
    (hcap : ∀ ω r, r ∈ Z → rootedClusterProperty U r P ω →
      ((finiteBoxCluster ω U r).card:ℝ) ≤ V)
    (hm : 0 < rootedPropertyCountMean p U Z P) {«λ» : ℝ} («hλ» : «λ» < 1) :
    (percolation d p).real {ω | ((selectedPropertyComponents U Z P ω).card:ℝ) ≤
      «λ»*rootedPropertyCountMean p U Z P/V} ≤
      rootedPropertyCountError p U Z P/((1-«λ»)*rootedPropertyCountMean p U Z P)^2 := by
  have hs := selectedPropertyComponents_lower_tail_subset U Z hZU P hV hcap
    («λ»*rootedPropertyCountMean p U Z P)
  exact (measureReal_mono hs).trans
    (rootedPropertyCount_relative_lower_tail p U Z hZU P hm «hλ»)

end NearCritical
