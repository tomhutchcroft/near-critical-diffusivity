module

public import NearCritical.HeartInnerArm
public import NearCritical.LatticeShells

/-! Surface-order entry counting for NEW PxinfC. Integer radii are explicit;
source real-radius rounding and the new outer box estimate remain separate. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Finset Set MeasureTheory
open scoped Classical

lemma centered_boundary_subset_sup_shell {d R : ℕ} (hR : 1 ≤ R) :
    boundarySites (centeredBox d R) ⊆
      latticeSupCube d R \ latticeSupCube d (R-1) := by
  intro v hv
  have hvC := (Finset.mem_filter.mp hv).1
  obtain ⟨i,hi | hi⟩ := centeredBox_boundary_coordinate hv
  · apply Finset.mem_sdiff.mpr
    refine ⟨mem_latticeSupCube.mpr (fun j => abs_le.mpr (mem_centeredBox.mp hvC j)), ?_⟩
    intro hin
    have hh := abs_le.mp (mem_latticeSupCube.mp hin i)
    omega
  · apply Finset.mem_sdiff.mpr
    refine ⟨mem_latticeSupCube.mpr (fun j => abs_le.mpr (mem_centeredBox.mp hvC j)), ?_⟩
    intro hin
    have hh := abs_le.mp (mem_latticeSupCube.mp hin i)
    omega

/-- No supplied surface-count premise: actual entry vertices lie in the
existing lattice shell, whose surface-order estimate has already been proved. -/
theorem innerEntryBoundary_card_le {d R : ℕ} (Q : Finset (Vertex d)) (hR : 1 ≤ R) :
    (innerEntryBoundary Q (centeredBox d R)).card ≤ 2*d*(2*R+1)^(d-1) := by
  have hs := Finset.card_le_card
    ((innerEntryBoundary_subset_boundarySites Q (centeredBox d R)).trans
      (centered_boundary_subset_sup_shell hR))
  have he : R-1+1 = R := by omega
  have hb := card_latticeSupShell_le d (R-1)
  rw [he] at hb
  have hn : 2*(R-1)+3 = 2*R+1 := by omega
  rw [hn] at hb
  exact hs.trans hb

/-- Actual critical membership upper bound after deriving BOTH the inner
arm factor and the entry-cardinality estimate. The outer factor stays explicit. -/
theorem heartClusterUnion_probability_le_counted_inner_arm {d R H : ℕ}
    (Q heart : Finset (Vertex d)) (hCQ : centeredBox d R ⊆ Q)
    (hheart : heart ⊆ centeredBox d H) (hHR : H < R) (x : Vertex d)
    (hx : x ∉ centeredBox d R) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (criticalArm : ∀ i : Fin d, HalfSpaceCriticalArmInput i B)
    (hprefix : ∀ v ∈ innerEntryBoundary Q (centeredBox d R),
      (percolation d (criticalPoint d)).real
        (connectionToSetEvent (Q : Set (Vertex d)) x {v}) ≤ A) :
    (percolation d (criticalPoint d)).real {ω | x ∈ heartClusterUnion ω Q heart} ≤
      (A*(B/((R-H:ℕ):ℝ)^3))*((2*d*(2*R+1)^(d-1):ℕ):ℝ) := by
  have hc : ((innerEntryBoundary Q (centeredBox d R)).card:ℝ) ≤
      ((2*d*(2*R+1)^(d-1):ℕ):ℝ) := by
    exact_mod_cast innerEntryBoundary_card_le Q (show 1 ≤ R by omega)
  exact (heartClusterUnion_probability_le_critical_inner_arm Q heart hCQ hheart hHR x hx
    hA hB criticalArm hprefix).trans (mul_le_mul_of_nonneg_left hc (by positivity))

end NearCritical
