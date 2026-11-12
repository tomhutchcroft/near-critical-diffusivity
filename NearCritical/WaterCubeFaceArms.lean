module
public import NearCritical.LatticeInversion
public import NearCritical.WaterCube
public import NearCritical.HalfSpaceEntropicTransfer

/-! Actual finite-face to full-half-space comparisons for lem.aa_bound.
Both faces are handled under the genuine product law. No decay estimate is
assumed in these geometric/probability comparisons. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Set MeasureTheory

lemma invert_lowerHalfSpace {d : ℕ} (i : Fin d) (b : ℤ) :
    Neg.neg '' {z : Vertex d | z i ≤ b} = {z | -b ≤ z i} := by
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    change -b ≤ -y i
    change y i ≤ b at hy
    omega
  · intro hz
    refine ⟨-z, ?_, by simp⟩
    change -z i ≤ b
    change -b ≤ z i at hz
    omega

/-- Normalize any horizontal starting point, including its transverse offset. -/
theorem upperHalfSpace_probability_normalize {d : ℕ} (p : unitInterval)
    (i : Fin d) (b : ℤ) (k n : ℕ) (x : Vertex d) (hx : x i = b + k) :
    percolation d p (connectionToSetEvent {z | b ≤ z i} x {z | b + n ≤ z i}) =
      percolation d p (halfSpaceArmEvent i k n) := by
  let a := halfSpaceArmBase i k - x
  have hai : a i = -b := by simp [a, halfSpaceArmBase, hx]
  have hax : a + x = halfSpaceArmBase i k := by simp [a]
  have h := halfSpace_arm_probability_translation p a i b (b + n) x
  rw [hai, hax] at h
  simpa [halfSpaceArmEvent, halfSpaceArmDomain, halfSpaceArmTarget] using h.symm

/-- The negative-facing version uses actual inversion of environments. -/
theorem lowerHalfSpace_probability_normalize {d : ℕ} (p : unitInterval)
    (i : Fin d) (b : ℤ) (k n : ℕ) (x : Vertex d) (hx : x i = b - k) :
    percolation d p (connectionToSetEvent {z | z i ≤ b} x {z | z i ≤ b - n}) =
      percolation d p (halfSpaceArmEvent i k n) := by
  have h := connectionToSet_probability_inversion p x {z | z i ≤ b} {z | z i ≤ b - n}
  rw [invert_lowerHalfSpace, invert_lowerHalfSpace] at h
  rw [← h]
  have hn : -(b - (n : ℤ)) = -b + n := by omega
  rw [hn]
  exact upperHalfSpace_probability_normalize p i (-b) k n (-x) (by
    change -x i = -b + k
    omega)

lemma waterCube_sitesPlus_coordinate {d : ℕ} (i : Fin d) (r R : ℕ)
    (x : DomainVertex (waterCube d i r R)) :
    -(r : ℤ) ≤ x.val i ∧ x.val i ≤ (r : ℤ) + 1 := by
  have h := rectangularBox_sitesPlus_range (fun j => if j = i then r else R) i x
  simp only [ite_true, coordinateData, mem_Icc] at h
  exact_mod_cast h

/-- A positive-face path is confined above the negative cube face and reaches
the positive face's exact integer level. -/
theorem waterCube_positiveFace_subset_halfSpace {d : ℕ} (i : Fin d) (r R : ℕ)
    (x : DomainVertex (waterCube d i r R)) :
    latticeBoundaryConnectionEvent (waterCube d i r R) x (positiveFace _ i) ⊆
      connectionToSetEvent {z | -(r : ℤ) ≤ z i} x.val {z | (r : ℤ) + 1 ≤ z i} := by
  apply (latticeBoundaryConnectionEvent_subset _ x _).trans
  apply connectionToSetEvent_mono
  · intro z hz
    exact (waterCube_sitesPlus_coordinate i r R ⟨z, hz⟩).1
  · rintro z ⟨y, hy, rfl⟩
    have h := rectangularBox_positiveFace_coordinate (fun j => if j = i then r else R) i hy
    simpa using le_of_eq h.symm

/-- The negative-face comparison retains the actual upper enlarged-support
level r+1; no symmetric-support convention is silently substituted. -/
theorem waterCube_negativeFace_subset_halfSpace {d : ℕ} (i : Fin d) (r R : ℕ)
    (x : DomainVertex (waterCube d i r R)) :
    latticeBoundaryConnectionEvent (waterCube d i r R) x (negativeFace _ i) ⊆
      connectionToSetEvent {z | z i ≤ (r : ℤ) + 1} x.val {z | z i ≤ -(r : ℤ)} := by
  apply (latticeBoundaryConnectionEvent_subset _ x _).trans
  apply connectionToSetEvent_mono
  · intro z hz
    exact (waterCube_sitesPlus_coordinate i r R ⟨z, hz⟩).2
  · rintro z ⟨y, hy, rfl⟩
    have h := rectangularBox_negativeFace_coordinate (fun j => if j = i then r else R) i hy
    simpa using le_of_eq h

/-- Actual-law finite positive-face probability bounded by the normalized
half-space arm at the vertex's exact height above the lower face. -/
theorem waterCube_positiveFace_probability_le_halfSpace {d : ℕ} (p : unitInterval)
    (i : Fin d) (r R : ℕ) (x : DomainVertex (waterCube d i r R)) :
    percolation d p (latticeBoundaryConnectionEvent (waterCube d i r R) x (positiveFace _ i)) ≤
      percolation d p (halfSpaceArmEvent i (x.val i + (r : ℤ)).toNat (2 * r + 1)) := by
  have hx := waterCube_sitesPlus_coordinate i r R x
  have hn : (r : ℤ) + 1 = -(r : ℤ) + (2 * r + 1 : ℕ) := by omega
  have he := upperHalfSpace_probability_normalize p i (-(r : ℤ))
    (x.val i + (r : ℤ)).toNat (2 * r + 1) x.val (by omega)
  rw [← he, ← hn]
  exact measure_mono (waterCube_positiveFace_subset_halfSpace i r R x)

/-- Inverted actual-law finite negative-face comparison. -/
theorem waterCube_negativeFace_probability_le_halfSpace {d : ℕ} (p : unitInterval)
    (i : Fin d) (r R : ℕ) (x : DomainVertex (waterCube d i r R)) :
    percolation d p (latticeBoundaryConnectionEvent (waterCube d i r R) x (negativeFace _ i)) ≤
      percolation d p (halfSpaceArmEvent i ((r : ℤ) + 1 - x.val i).toNat (2 * r + 1)) := by
  have hx := waterCube_sitesPlus_coordinate i r R x
  have hn : -(r : ℤ) = (r : ℤ) + 1 - (2 * r + 1 : ℕ) := by omega
  have he := lowerHalfSpace_probability_normalize p i ((r : ℤ) + 1)
    ((r : ℤ) + 1 - x.val i).toNat (2 * r + 1) x.val (by omega)
  rw [← he, ← hn]
  exact measure_mono (waterCube_negativeFace_subset_halfSpace i r R x)

end NearCritical
