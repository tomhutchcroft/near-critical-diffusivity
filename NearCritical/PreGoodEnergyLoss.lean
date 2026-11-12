module

public import NearCritical.RegularityEnergyTails

/-! Source pre-good Step2 from actual ERE moments, not an assumed irregular
marked first moment. NEW analytic moment estimates remain explicit. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Finset Set MeasureTheory
open scoped Classical

/-- Concrete source cluster-loss rate from computed ERE moments and raw
candidate data. This discharges the marked first-moment input of the earlier
loss theorem, retaining the genuinely NEW analytic diagram obligations. -/
theorem literal_regularity_loss_from_energy_moments {d : ℕ} {φ : Type*}
    (p : unitInterval) (Q heart excluded cubeBoundary markBoundary : Finset (Vertex d))
    (hmarkQ : markBoundary ⊆ Q) (hmark : markBoundary ⊆ cubeBoundary)
    (P : Configuration d → Finset (Vertex d) → Prop) (patch : φ → Finset (Vertex d))
    (hpatch_mark : ∀ i, patch i ⊆ markBoundary)
    (hmeet : ∀ ω C, C ∈ filteredClusterFamily ω Q (P ω) → (C ∩ heart).Nonempty)
    (r n : ℕ) (hr : 1 ≤ r) (hn : 1 ≤ n) (hd : 7 ≤ d)
    {δ Cv Cp Cb c c1 : ℝ} (hδ : 0 < δ) (hCv : 0 ≤ Cv) (hCp : 0 ≤ Cp)
    (hc : 0 < c) (hc1 : 0 < c1)
    (hm1 : ∀ x ∈ markBoundary,
      heartConditionalMean p Q heart (fun F => regularityEnergyOne F excluded r x) x ≤ δ/2)
    (hm2 : ∀ x ∈ markBoundary,
      heartConditionalMean p Q heart (fun F => regularityEnergyTwo F cubeBoundary r x) x ≤ δ/2)
    (hvar : ∀ x ∈ markBoundary,
      heartCenteredMoment p Q heart (fun F => regularityEnergyOne F excluded r x) x +
        heartCenteredMoment p Q heart (fun F => regularityEnergyTwo F cubeBoundary r x) x ≤
      (Cv/(r:ℝ)^(d-6))*(percolation d p).real {ω | x ∈ heartClusterUnion ω Q heart})
    (hhit : ∀ x ∈ markBoundary,
      (percolation d p).real {ω | x ∈ heartClusterUnion ω Q heart} ≤ Cp/(n:ℝ)^3)
    (hcard : (markBoundary.card:ℝ) ≤ Cb*(n:ℝ)^(d-1))
    (hpatch : ∀ ω C, C ∈ filteredClusterFamily ω Q (P ω) → ∀ i,
      c*(n:ℝ)^2 ≤ ((C ∩ patch i).card:ℝ)) :
    (percolation d p).real {ω | (c1/2)*(n:ℝ)^(d-6) ≤
      ((filteredClusterFamily ω Q (regularityBadCluster (P ω) patch
        (sourceRegularPoint (heartClusterUnion ω Q heart) excluded cubeBoundary r δ)
        ((c/2)*(n:ℝ)^2))).card:ℝ)} ≤
      16*Cv*Cp*Cb/(δ^2*c*c1*(r:ℝ)^(d-6)) := by
  have hdR : (0:ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hrR : (0:ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  let ε' : ℝ := (2*Cv*Cp*Cb)/((d:ℝ)*δ^2*(r:ℝ)^(d-6))
  have hfirst := irregularBoundary_first_moment_source_scale p Q heart excluded cubeBoundary
    markBoundary hmarkQ hmark r n hr hn hd hδ hCv hCp hm1 hm2 hvar hhit hcard
  have hefirst : (4*Cv*Cp*Cb/δ^2)/(r:ℝ)^(d-6)*(n:ℝ)^(d-4) =
      2*(d:ℝ)*ε'*(n:ℝ)^(d-4) := by
    dsimp [ε']
    field_simp [ne_of_gt hdR,ne_of_gt hrR,ne_of_gt hδ]
    ring
  have hmoment : (∑ x ∈ Q, (percolation d p).real
      {ω | x ∈ irregularBoundaryVertices ω Q heart excluded cubeBoundary markBoundary r δ}) ≤
      2*(d:ℝ)*ε'*(n:ℝ)^(d-4) := by
    rw [← integral_irregularBoundary_count p Q heart excluded cubeBoundary markBoundary r δ,
      ← hefirst]
    exact hfirst
  have h := literal_regularity_loss_source_bound p Q heart excluded cubeBoundary markBoundary r δ
    P patch hpatch_mark hmeet n hn (by omega) hc hc1 hpatch hmoment
  have he : 8*(d:ℝ)*ε'/(c*c1) = 16*Cv*Cp*Cb/(δ^2*c*c1*(r:ℝ)^(d-6)) := by
    dsimp [ε']
    field_simp [ne_of_gt hdR,ne_of_gt hrR,ne_of_gt hδ,ne_of_gt hc,ne_of_gt hc1]
    ring
  simpa only [he] using h

end NearCritical
