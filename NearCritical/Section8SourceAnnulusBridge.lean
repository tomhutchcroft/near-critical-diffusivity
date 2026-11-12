module
public import NearCritical.AppendixSourceRD
public import NearCritical.Section8LocalHalfSpaceGeometry

/-! Exact integer-radius domain identification for the source RD geometry. -/
@[expose] public section
noncomputable section
namespace NearCritical.Section8
open scoped Classical
open AppendixVariance

/-- The Appendix cube and the probability-side cube have identical vertices. -/
theorem appendix_cube_eq_centeredBox (d c : ℕ) :
    (cube c : Finset (Vertex d)) = centeredBox d c := by
  ext w
  simp only [mem_cube,mem_centeredBox,abs_le]

private theorem cube_norm_iff {d c : ℕ} (w : Vertex d) :
    w ∈ cube c ↔ linfDist 0 w ≤ c := by
  simpa [cube] using
    (mem_linfBall_iff_dist (0 : Vertex d) w (Int.natCast_nonneg c))

/-- In positive dimension the retained inner boundary is the exact norm shell. -/
theorem centeredBox_boundary_norm_iff {k c : ℕ} (w : Vertex (k+1)) :
    w ∈ boundarySites (centeredBox (k+1) c) ↔ linfDist 0 w = c := by
  rw [mem_centeredBox_boundary_iff]
  constructor
  · rintro ⟨hw,i,hi⟩
    have hupper : linfDist 0 w ≤ c := (cube_norm_iff w).mp
      (by simpa only [appendix_cube_eq_centeredBox] using hw)
    have hlower : (w i).natAbs ≤ linfDist 0 w := by
      rw [linfDist_zero]
      exact Finset.le_sup (f := fun j => (w j).natAbs) (Finset.mem_univ i)
    rcases hi with hi | hi <;> rw [hi] at hlower <;> simpa using le_antisymm hupper (by simpa using hlower)
  · intro hm
    refine ⟨?_,?_⟩
    · rw [← appendix_cube_eq_centeredBox]
      exact (cube_norm_iff w).mpr hm.le
    · obtain ⟨i,_,hi⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (Fin (k+1)))
        Finset.univ_nonempty (fun j => (w j).natAbs)
      have hni : (w i).natAbs = c := by
        simpa only [linfDist_zero,hi] using hm
      have hai : |w i| = (c : ℤ) := by
        rw [← Int.natCast_natAbs,hni]
      refine ⟨i,?_⟩
      rcases le_total 0 (w i) with hs | hs
      · left
        simpa only [abs_of_nonneg hs] using hai
      · right
        rw [abs_of_nonpos hs] at hai
        omega

/-- Exact equality of the literal Appendix annulus and the retained-boundary domain.
Positive dimension is essential to the radius-zero boundary convention. -/
theorem sourceAnnulus_eq_heartAnnulus (k n c : ℕ) :
    (sourceAnnulus n c : Finset (Vertex (k+1))) =
      heartAnnulus (centeredBox (k+1) n) (centeredBox (k+1) c) := by
  ext w
  simp only [sourceAnnulus,Finset.mem_filter,heartAnnulus,Finset.mem_sdiff,
    centeredBox_boundary_norm_iff]
  rw [← appendix_cube_eq_centeredBox (k+1) n,
    ← appendix_cube_eq_centeredBox (k+1) c]
  simp only [cube_norm_iff]
  omega

end NearCritical.Section8
