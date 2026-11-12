module
public import NearCritical.Section8CubeFaceMass

/-! All coordinate faces, including a face that coincides with an ambient wall. -/
@[expose] public section
noncomputable section
namespace NearCritical.Section8
open Set MeasureTheory
open scoped Classical

/-- Actual full cube-face mass, with no excluded-face containment requirement. -/
theorem cube_all_face_mass_le {d n : ℕ} (hd : 1 ≤ d) (hn : 1 ≤ n)
    (C A B : ℝ) (hC : 0 ≤ C) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (panis : PanisHalfSpaceTwoPointUpper d C)
    (Q : Finset (Vertex d)) (x : Vertex d) (hx : x ∈ Q)
    (j : Fin d) (wall : ℤ) (positive : Bool)
    (arm : ∀ i : Fin d, HalfSpaceCriticalArmInput i A)
    (second : ∀ i : Fin d, SlabBoundarySecondMomentUpper i B)
    (hQ : ∀ y ∈ Q, ∀ k, x k-(n : ℤ) ≤ y k ∧ y k ≤ x k+(n : ℤ))
    (hD : (Q : Set (Vertex d)) ⊆ coordinateHalfSpace j wall positive) :
    (∑ y ∈ Q.filter (fun y => ∃ i : Fin d,
        y i = x i+(n : ℤ) ∨ y i = x i-(n : ℤ)),
      (percolation d (criticalPoint d)).real
        (connectionToSetEvent (Q : Set (Vertex d)) x {y})) ≤
      (2*(d : ℝ))*
        ((4*C*(A+B)*(9 : ℝ)^(d-1))*(1+coordinateDepth j wall positive x)/(n : ℝ)) := by
  let F := Q.filter (fun y => ∃ i : Fin d,
    y i = x i+(n : ℤ) ∨ y i = x i-(n : ℤ))
  let U := cubeNonbottomFaces Q x n j
  let V := Q.filter (fun y => y j = x j-(n : ℤ))
  let f := fun y : Vertex d => (percolation d (criticalPoint d)).real
    (connectionToSetEvent (Q : Set (Vertex d)) x {y})
  let K := (4*C*(A+B)*(9 : ℝ)^(d-1))*(1+coordinateDepth j wall positive x)/(n : ℝ)
  have hcover : F ⊆ U ∪ V := by
    intro y hy
    obtain ⟨hyQ,i,hi⟩ := Finset.mem_filter.mp hy
    rcases hi with hi | hi
    · apply Finset.mem_union.mpr
      left
      apply Finset.mem_filter.mpr
      refine ⟨hyQ,(i,true),?_,?_⟩
      · simp
      · simpa using hi
    · by_cases hij : i = j
      · apply Finset.mem_union.mpr
        right
        exact Finset.mem_filter.mpr ⟨hyQ,by simpa [hij] using hi⟩
      · apply Finset.mem_union.mpr
        left
        apply Finset.mem_filter.mpr
        refine ⟨hyQ,(i,false),?_,?_⟩
        · simp [hij]
        · simpa [sub_eq_add_neg] using hi
  have hU : (∑ y ∈ U, f y) ≤ (((2*d-1 : ℕ) : ℝ))*K :=
    cube_nonbottom_mass_le hd hn C A B hC hA hB panis Q x hx j wall positive arm second hQ hD
  have hV : (∑ y ∈ V, f y) ≤ K :=
    cube_negative_face_mass_le hd hn C A B hC hA hB panis Q x hx
      j j wall positive (arm j) (second j) hQ hD
  have hcount : (((2*d-1 : ℕ) : ℝ)+1) = 2*(d : ℝ) := by
    exact_mod_cast (show 2*d-1+1 = 2*d by omega)
  calc
    _ ≤ ∑ y ∈ U ∪ V, f y :=
      Finset.sum_le_sum_of_subset_of_nonneg hcover (fun y _ _ => measureReal_nonneg)
    _ ≤ (∑ y ∈ U, f y)+(∑ y ∈ V, f y) := by
      have he := Finset.sum_union_inter (s₁ := U) (s₂ := V) (f := f)
      have hi : 0 ≤ ∑ y ∈ U ∩ V, f y := Finset.sum_nonneg (fun y _ => measureReal_nonneg)
      linarith
    _ ≤ (((2*d-1 : ℕ) : ℝ))*K+K := add_le_add hU hV
    _ = (2*(d : ℝ))*K := by rw [← add_one_mul,hcount]

end NearCritical.Section8
