module
public import NearCritical.Section8SlabBoundaryMass
public import NearCritical.HalfSpaceTranslation
public import NearCritical.LatticeInversion

/-! The slab plane bound at an arbitrary boundary starting vertex, under the
actual translated percolation law. No fixed-cutoff stationarity is assumed. -/
@[expose] public section
noncomputable section
namespace NearCritical.Section8
open Set MeasureTheory
open scoped Classical

/-- Translate the entire finite slab domain and top-plane target together.
The amplitude is uniform in the cutoff, boundary position and scale. -/
theorem shifted_slab_plane_mass_le {d : ℕ} (i : Fin d) (A B : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (arm : HalfSpaceCriticalArmInput i A)
    (second : SlabBoundarySecondMomentUpper i B)
    (n : ℕ) (hn : 1 ≤ n) (Q : Finset (Vertex d)) (x : Vertex d) (hx : x ∈ Q)
    (hQ : ∀ y ∈ Q, x i ≤ y i ∧ y i ≤ x i+(n : ℤ)) :
    ∑ y ∈ Q.filter (fun y => y i = x i+(n : ℤ)),
      (percolation d (criticalPoint d)).real
        (connectionToSetEvent (Q : Set (Vertex d)) x {y}) ≤ (A+B)/(n : ℝ) := by
  let Q' := Q.image (fun y => -x+y)
  have h0 : (0 : Vertex d) ∈ Q' := Finset.mem_image.mpr ⟨x,hx,by simp⟩
  have hQ' : ∀ y ∈ Q', 0 ≤ y i ∧ y i ≤ (n : ℤ) := by
    intro y hy
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hy
    have hh := hQ z hz
    change 0 ≤ -x i+z i ∧ -x i+z i ≤ (n : ℤ)
    constructor <;> omega
  have hdom : (fun z : Vertex d => x+z) '' (Q' : Set (Vertex d)) = (Q : Set (Vertex d)) := by
    dsimp only [Q']
    rw [Finset.coe_image, Set.image_image]
    have he : (fun y : Vertex d => x + (-x+y)) = id := by
      funext y
      simp
    rw [he, Set.image_id]
  have hprob (y : Vertex d) :
      (percolation d (criticalPoint d)).real
        (connectionToSetEvent (Q' : Set (Vertex d)) 0 {-x+y}) =
      (percolation d (criticalPoint d)).real
        (connectionToSetEvent (Q : Set (Vertex d)) x {y}) := by
    have he := connectionToSet_probability_translation (criticalPoint d) x 0
      (Q' : Set (Vertex d)) {-x+y}
    simpa [measureReal_def, hdom] using congrArg ENNReal.toReal he.symm
  have he :
      (∑ y ∈ slabTopTargets Q' i n, (percolation d (criticalPoint d)).real
        (connectionToSetEvent (Q' : Set (Vertex d)) 0 {y})) =
      ∑ y ∈ Q.filter (fun y => y i = x i+(n : ℤ)),
        (percolation d (criticalPoint d)).real
          (connectionToSetEvent (Q : Set (Vertex d)) x {y}) := by
    unfold slabTopTargets
    rw [Finset.sum_filter,Finset.sum_filter]
    dsimp only [Q']
    rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro y _hy
      have hc : (-x+y) i = (n : ℤ) ↔ y i = x i+(n : ℤ) := by
        change -x i+y i = (n : ℤ) ↔ y i = x i+(n : ℤ)
        omega
      simp only [hc]
      split_ifs
      · exact hprob y
      · rfl
    · intro y _hy z _hz heq
      have hh := congrArg (fun v : Vertex d => x+v) heq
      simpa using hh
  rw [← he]
  exact finite_slab_plane_mass_le i A B hA hB arm second n hn Q' h0 hQ'

/-- The opposite face uses the actual inverted domain and law. -/
theorem shifted_lower_slab_plane_mass_le {d : ℕ} (i : Fin d) (A B : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (arm : HalfSpaceCriticalArmInput i A)
    (second : SlabBoundarySecondMomentUpper i B)
    (n : ℕ) (hn : 1 ≤ n) (Q : Finset (Vertex d)) (x : Vertex d) (hx : x ∈ Q)
    (hQ : ∀ y ∈ Q, x i-(n : ℤ) ≤ y i ∧ y i ≤ x i) :
    ∑ y ∈ Q.filter (fun y => y i = x i-(n : ℤ)),
      (percolation d (criticalPoint d)).real
        (connectionToSetEvent (Q : Set (Vertex d)) x {y}) ≤ (A+B)/(n : ℝ) := by
  let Q' := Q.image Neg.neg
  have hx' : -x ∈ Q' := Finset.mem_image.mpr ⟨x,hx,rfl⟩
  have hQ' : ∀ y ∈ Q', (-x) i ≤ y i ∧ y i ≤ (-x) i+(n : ℤ) := by
    intro y hy
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hy
    have hh := hQ z hz
    change -x i ≤ -z i ∧ -z i ≤ -x i+(n : ℤ)
    constructor <;> omega
  have hprob (y : Vertex d) :
      (percolation d (criticalPoint d)).real
        (connectionToSetEvent (Q' : Set (Vertex d)) (-x) {-y}) =
      (percolation d (criticalPoint d)).real
        (connectionToSetEvent (Q : Set (Vertex d)) x {y}) := by
    have he := connectionToSet_probability_inversion (criticalPoint d) x
      (Q : Set (Vertex d)) {y}
    simpa only [measureReal_def,Q',Finset.coe_image,Set.image_singleton] using congrArg ENNReal.toReal he
  have he :
      (∑ y ∈ Q'.filter (fun y => y i = (-x) i+(n : ℤ)),
        (percolation d (criticalPoint d)).real
          (connectionToSetEvent (Q' : Set (Vertex d)) (-x) {y})) =
      ∑ y ∈ Q.filter (fun y => y i = x i-(n : ℤ)),
        (percolation d (criticalPoint d)).real
          (connectionToSetEvent (Q : Set (Vertex d)) x {y}) := by
    rw [Finset.sum_filter,Finset.sum_filter]
    dsimp only [Q']
    rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro y _hy
      have hc : (-y) i = (-x) i+(n : ℤ) ↔ y i = x i-(n : ℤ) := by
        change -y i = -x i+(n : ℤ) ↔ y i = x i-(n : ℤ)
        omega
      simp only [hc]
      split_ifs
      · exact hprob y
      · rfl
    · intro y _hy z _hz heq
      exact neg_injective heq
  rw [← he]
  exact shifted_slab_plane_mass_le i A B hA hB arm second n hn Q' (-x) hx' hQ'

end NearCritical.Section8
