module
public import NearCritical.LatticePermutation
public import NearCritical.Section8SlabBoundaryMass
public import NearCritical.HeartConnectionCount

/-! Step R1 of the repaired route to eq.boundary_0_mean_segment. The source's rotation step
(main.tex ~6303) claims Q' ⊆ Q_z, which fails in the transverse coordinates for
d ≥ 3. Here the face mass from a point `z` of the separating plane is bounded instead
by translating `z` to the origin and swapping coordinates `i₀ ↔ j`, which maps the
region into the slab `{0 ≤ v i₀ ≤ h}`. The verified finite slab mean bound
`finite_slab_count_mean_le` (lem.Nn_mean_upper in finite form, conditional on the
cited arm and second-moment inputs) then applies. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory
open scoped Classical
open NearCritical.Section8

lemma permVertex_zero {d : ℕ} (σ : Equiv.Perm (Fin d)) : permVertex σ (0 : Vertex d) = 0 := by
  funext j
  simp [permVertex]

/-- Translate `z` to the origin, then swap coordinates `i₀ ↔ j`. -/
def sideSlabMap {d : ℕ} (i₀ j : Fin d) (z w : Vertex d) : Vertex d :=
  permVertex (Equiv.swap i₀ j) (-z+w)

lemma sideSlabMap_apply_i₀ {d : ℕ} (i₀ j : Fin d) (z w : Vertex d) :
    sideSlabMap i₀ j z w i₀ = w j - z j := by
  simp only [sideSlabMap,permVertex,Equiv.symm_swap,Equiv.swap_apply_left,Pi.add_apply,
    Pi.neg_apply]
  ring

lemma sideSlabMap_injective {d : ℕ} (i₀ j : Fin d) (z : Vertex d) :
    Function.Injective (sideSlabMap i₀ j z) := by
  intro a b h
  have h' := permVertex_injective (Equiv.swap i₀ j) h
  simpa using h'

/-- Exact transport of a restricted connection probability under `sideSlabMap`. -/
lemma sideSlabMap_connection {d : ℕ} (p : unitInterval) (i₀ j : Fin d)
    (Rz : Finset (Vertex d)) (z y : Vertex d) :
    (percolation d p).real (connectionToSetEvent (Rz : Set (Vertex d)) z {y}) =
      (percolation d p).real (connectionToSetEvent
        ((Rz.image (sideSlabMap i₀ j z) : Finset (Vertex d)) : Set (Vertex d)) 0
        {sideSlabMap i₀ j z y}) := by
  have h1 := connectionToSet_probability_translation p (-z) z (Rz : Set (Vertex d)) {y}
  have h2 := connectionToSet_probability_perm (Equiv.swap i₀ j) p (-z+z)
    ((fun w ↦ -z+w) '' (Rz : Set (Vertex d))) ((fun w ↦ -z+w) '' ({y} : Set (Vertex d)))
  simp only [Set.image_image,Set.image_singleton] at h1 h2
  rw [neg_add_cancel] at h1 h2
  rw [permVertex_zero] at h2
  rw [Finset.coe_image]
  show (percolation d p (connectionToSetEvent (Rz : Set (Vertex d)) z {y})).toReal =
    (percolation d p (connectionToSetEvent
      ((fun x ↦ permVertex (Equiv.swap i₀ j) (-z+x)) '' (Rz : Set (Vertex d))) 0
      {permVertex (Equiv.swap i₀ j) (-z+y)})).toReal
  rw [h2,h1]

/-- Face mass from a separating-plane point `z` into the far layer `{w j = z j + h}`
of a region lying in `{z j ≤ w j ≤ z j + h}`, bounded by the cited slab mean. -/
theorem side_face_mass_le_slab_mean {d : ℕ} (i₀ j : Fin d) (A B : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (arm : HalfSpaceCriticalArmInput i₀ A)
    (second : SlabBoundarySecondMomentUpper i₀ B) (h : ℕ) (hh : 1 ≤ h)
    (Rz : Finset (Vertex d)) (z : Vertex d) (hz : z ∈ Rz)
    (hR : ∀ w ∈ Rz, z j ≤ w j ∧ w j ≤ z j+h) :
    ∑ y ∈ Rz.filter (fun y => y j = z j+h), (percolation d (criticalPoint d)).real
      (connectionToSetEvent (Rz : Set (Vertex d)) z {y}) ≤ (A+B)/(h : ℝ) := by
  have h0 : (0 : Vertex d) ∈ Rz.image (sideSlabMap i₀ j z) := by
    refine Finset.mem_image.mpr ⟨z,hz,?_⟩
    simp [sideSlabMap,permVertex_zero]
  have hQ : ∀ v ∈ Rz.image (sideSlabMap i₀ j z), 0 ≤ v i₀ ∧ v i₀ ≤ (h : ℤ) := by
    intro v hv
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hv
    rw [sideSlabMap_apply_i₀]
    have := hR w hw
    constructor <;> omega
  have hmean := finite_slab_count_mean_le i₀ A B hA hB arm second h hh (Rz.image (sideSlabMap i₀ j z)) h0 hQ
  rw [integral_heartConnectionCount _ (Rz.image (sideSlabMap i₀ j z)) _ 0 h0] at hmean
  have htop : slabTopTargets (Rz.image (sideSlabMap i₀ j z)) i₀ h =
      (Rz.filter (fun y => y j = z j+h)).image (sideSlabMap i₀ j z) := by
    unfold slabTopTargets
    rw [Finset.filter_image]
    congr 1
    apply Finset.filter_congr
    intro w _
    change sideSlabMap i₀ j z w i₀ = (h : ℤ) ↔ w j = z j+h
    rw [sideSlabMap_apply_i₀]
    constructor <;> intro hw <;> omega
  rw [htop,Finset.sum_image (fun a _ b _ hab => sideSlabMap_injective i₀ j z hab)] at hmean
  calc _ = ∑ y ∈ Rz.filter (fun y => y j = z j+h), (percolation d (criticalPoint d)).real
          (connectionToSetEvent ((Rz.image (sideSlabMap i₀ j z) : Finset (Vertex d)) :
            Set (Vertex d)) 0 {sideSlabMap i₀ j z y}) :=
        Finset.sum_congr rfl (fun y _ => sideSlabMap_connection _ i₀ j Rz z y)
    _ ≤ _ := hmean

end NearCritical
