module
public import NearCritical.Section8FinitePlaneSplit
public import NearCritical.Section8ShiftedSlabMass

/-! The actual finite-face decomposition with its upper slab wall retained.
This is the corrected second-factor step of source eq.cube_step1. -/
@[expose] public section
noncomputable section
namespace NearCritical.Section8
open Set MeasureTheory
open scoped Classical

/-- A finite top-face mass is controlled by the actual midpoint prefix mass.
The suffix stays inside Q and between the midpoint and top planes. -/
theorem finite_top_face_mass_le_midplane {d : ℕ} (i : Fin d) (A B : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (arm : HalfSpaceCriticalArmInput i A)
    (second : SlabBoundarySecondMomentUpper i B)
    (n : ℕ) (hn : 1 ≤ n) (Q : Finset (Vertex d)) (x : Vertex d) (l : ℤ)
    (hx : x i ≤ l) (hQ : ∀ y ∈ Q, y i ≤ l + (n : ℤ)) :
    (∑ y ∈ Q.filter (fun y => y i = l + (n : ℤ)),
      (percolation d (criticalPoint d)).real
        (connectionToSetEvent (Q : Set (Vertex d)) x {y})) ≤
    (∑ u ∈ Q.filter (fun u => u i = l),
      (percolation d (criticalPoint d)).real
        (connectionToSetEvent (Q : Set (Vertex d)) x {u})) * ((A+B)/(n : ℝ)) := by
  let p := criticalPoint d
  let F := Q.filter (fun y => y i = l + (n : ℤ))
  let M := Q.filter (fun u => u i = l)
  let S := Q.filter (fun z => l ≤ z i)
  let f := fun u => (percolation d p).real
    (connectionToSetEvent (Q : Set (Vertex d)) x {u})
  let g := fun u y => (percolation d p).real
    (connectionToSetEvent (S : Set (Vertex d)) u {y})
  have hdom : (S : Set (Vertex d)) = (Q : Set (Vertex d)) ∩ {z | l ≤ z i} := by
    ext z
    simp [S]
  have hsuffix (u : Vertex d) (hu : u ∈ M) :
      ∑ y ∈ F, g u y ≤ (A+B)/(n : ℝ) := by
    obtain ⟨huQ, hul⟩ := Finset.mem_filter.mp hu
    have huS : u ∈ S := Finset.mem_filter.mpr ⟨huQ, hul.ge⟩
    have hS : ∀ y ∈ S, u i ≤ y i ∧ y i ≤ u i + (n : ℤ) := by
      intro y hy
      obtain ⟨hyQ, hyl⟩ := Finset.mem_filter.mp hy
      rw [hul]
      exact ⟨hyl, hQ y hyQ⟩
    have hF : S.filter (fun y => y i = u i + (n : ℤ)) = F := by
      ext y
      simp only [S, F, Finset.mem_filter, hul]
      constructor
      · rintro ⟨⟨hy, _⟩, he⟩
        exact ⟨hy, he⟩
      · rintro ⟨hy, he⟩
        exact ⟨⟨hy, by omega⟩, he⟩
    have h := shifted_slab_plane_mass_le i A B hA hB arm second n hn S u huS hS
    rw [hF] at h
    exact h
  change (∑ y ∈ F, (percolation d p).real
    (connectionToSetEvent (Q : Set (Vertex d)) x {y})) ≤ _
  calc
    _ ≤ ∑ y ∈ F, ∑ u ∈ M, f u * g u y := by
      apply Finset.sum_le_sum
      intro y hy
      have hyl : l ≤ y i := by
        have he := (Finset.mem_filter.mp hy).2
        omega
      simpa only [M, f, g, hdom] using
        finite_connection_last_plane_bk p Q x y i l hx hyl
    _ = ∑ u ∈ M, f u * (∑ y ∈ F, g u y) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro u _
      exact (Finset.mul_sum _ _ _).symm
    _ ≤ ∑ u ∈ M, f u * ((A+B)/(n : ℝ)) := by
      apply Finset.sum_le_sum
      intro u hu
      exact mul_le_mul_of_nonneg_left (hsuffix u hu) (by dsimp [f]; positivity)
    _ = _ := (Finset.sum_mul _ _ _).symm

end NearCritical.Section8
