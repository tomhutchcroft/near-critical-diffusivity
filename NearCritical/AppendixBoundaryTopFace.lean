module
public import NearCritical.AppendixBoundaryBoxFaces
public import NearCritical.AppendixBoundaryPlaneMass
public import NearCritical.LatticeReflection

/-! Step R3b of the repaired route to eq.boundary_0_mean_segment (lem.boundary_regularity,
main.tex ~6281-6330). For the CLOSED box `B = {0 ≤ w i₀ ≤ h} ∩ Λ_R` (the source's
`Q_{n,rn}` with integer faces), the top-face mass satisfies
`Σ_{∂₁B} P[0 ↔_B y] ≥ (first-moment mass of ∂̂B) − 2(d-1)·N·C(1+h)/(R-h)^d·(A+B)/h`,
with `N = (h+1)(2R+1)^(d-2)`. The pieces are:
* R3a for each positive side face `{w k = R}`;
* `LatticeReflection` for each negative face `{w k = -R}`, by the box's symmetry;
* R2 (Panis) for the plane mass, with an exact count of the plane.
The source's false containment Q' ⊆ Q_z is not used. `top_face_mass_lower_of_wide` gives
`≥ c/(2h)` whenever the explicit width condition holds; R/h large enough suffices. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory
open scoped Classical
open NearCritical.Section8

/-- The closed box `{0 ≤ w i₀ ≤ h} ∩ Λ_R`. -/
def boundaryBox {d : ℕ} (i₀ : Fin d) (h R : ℕ) : Finset (Vertex d) :=
  (centeredBox d R).filter (fun w => 0 ≤ w i₀ ∧ w i₀ ≤ (h : ℤ))

/-- `∂̂B`: every face except the bottom `{w i₀ = 0}`. -/
def boundaryHat {d : ℕ} (i₀ : Fin d) (h R : ℕ) : Finset (Vertex d) :=
  (boundaryBox i₀ h R).filter
    (fun y => y i₀ = (h : ℤ) ∨ ∃ k, k ≠ i₀ ∧ (y k = (R : ℤ) ∨ y k = -(R : ℤ)))

/-- The top face `∂₁B = {w i₀ = h}`. -/
def boundaryTop {d : ℕ} (i₀ : Fin d) (h R : ℕ) : Finset (Vertex d) :=
  (boundaryBox i₀ h R).filter (fun y => y i₀ = (h : ℤ))

lemma sum_union_le_of_nonneg {α : Type*} [DecidableEq α] (f : α → ℝ) (hf : ∀ a, 0 ≤ f a) (s t : Finset α) :
    ∑ a ∈ s ∪ t, f a ≤ ∑ a ∈ s, f a+∑ a ∈ t, f a := by
  have h : ∑ a ∈ s ∪ t, f a+∑ a ∈ s ∩ t, f a = ∑ a ∈ s, f a+∑ a ∈ t, f a :=
    Finset.sum_union_inter
  have h0 : 0 ≤ ∑ a ∈ s ∩ t, f a := Finset.sum_nonneg (fun a _ => hf a)
  linarith

lemma sum_biUnion_le_of_nonneg {α ι : Type*} [DecidableEq α] [DecidableEq ι] (f : α → ℝ) (hf : ∀ a, 0 ≤ f a)
    (K : Finset ι) (G : ι → Finset α) :
    ∑ a ∈ K.biUnion G, f a ≤ ∑ k ∈ K, ∑ a ∈ G k, f a := by
  refine Finset.induction_on K (by simp) ?_
  intro a K ha ih
  rw [Finset.biUnion_insert,Finset.sum_insert ha]
  exact (sum_union_le_of_nonneg f hf _ _).trans (add_le_add le_rfl ih)

lemma reflVertex_zero {d : ℕ} (k : Fin d) : reflVertex k (0 : Vertex d) = 0 := by
  funext j
  simp [reflVertex,Function.update_apply]

lemma reflVertex_mem_boundaryBox {d : ℕ} {i₀ k : Fin d} (hk : k ≠ i₀) (h R : ℕ)
    (w : Vertex d) : reflVertex k w ∈ boundaryBox i₀ h R ↔ w ∈ boundaryBox i₀ h R := by
  have key : ∀ v : Vertex d, v ∈ boundaryBox i₀ h R → reflVertex k v ∈ boundaryBox i₀ h R := by
    intro v hv
    obtain ⟨hvbox,hv1,hv2⟩ := Finset.mem_filter.mp hv
    have hvc := mem_centeredBox.mp hvbox
    have hi : reflVertex k v i₀ = v i₀ := by
      simp only [reflVertex]
      exact Function.update_of_ne (Ne.symm hk) _ _
    refine Finset.mem_filter.mpr ⟨?_,?_,?_⟩
    · rw [mem_centeredBox]
      intro j
      have := hvc j
      by_cases hj : j = k
      · rw [hj]
        simp only [reflVertex,Function.update_self]
        rw [hj] at this
        constructor <;> omega
      · simp only [reflVertex]
        rw [Function.update_of_ne hj]
        exact this
    · rw [hi]
      exact hv1
    · rw [hi]
      exact hv2
  constructor
  · intro hw
    have := key _ hw
    rwa [reflVertex_reflVertex] at this
  · exact key w

/-- The negative side face carries the same mass as the positive one. -/
lemma neg_side_face_eq {d : ℕ} (p : unitInterval) {i₀ k : Fin d} (hk : k ≠ i₀) (h R : ℕ) :
    ∑ y ∈ (boundaryBox i₀ h R).filter (fun y => y k = -(R : ℤ)), (percolation d p).real
        (connectionToSetEvent ((boundaryBox i₀ h R : Finset (Vertex d)) : Set (Vertex d)) 0 {y}) =
      ∑ y ∈ (boundaryBox i₀ h R).filter (fun y => y k = (R : ℤ)), (percolation d p).real
        (connectionToSetEvent ((boundaryBox i₀ h R : Finset (Vertex d)) : Set (Vertex d)) 0 {y}) := by
  have hBimg : reflVertex k '' ((boundaryBox i₀ h R : Finset (Vertex d)) : Set (Vertex d)) =
      ((boundaryBox i₀ h R : Finset (Vertex d)) : Set (Vertex d)) := by
    ext z
    constructor
    · rintro ⟨w,hw,rfl⟩
      exact (reflVertex_mem_boundaryBox hk h R w).mpr hw
    · intro hz
      refine ⟨reflVertex k z,(reflVertex_mem_boundaryBox hk h R _).mpr ?_,reflVertex_reflVertex k z⟩
      exact hz
  have hk_coord : ∀ y : Vertex d, reflVertex k y k = -y k := by
    intro y
    simp [reflVertex]
  refine Finset.sum_nbij' (reflVertex k) (reflVertex k) ?_ ?_ ?_ ?_ ?_
  · intro y hy
    obtain ⟨hyB,hyk⟩ := Finset.mem_filter.mp hy
    exact Finset.mem_filter.mpr ⟨(reflVertex_mem_boundaryBox hk h R y).mpr hyB,
      by rw [hk_coord,hyk,neg_neg]⟩
  · intro y hy
    obtain ⟨hyB,hyk⟩ := Finset.mem_filter.mp hy
    exact Finset.mem_filter.mpr ⟨(reflVertex_mem_boundaryBox hk h R y).mpr hyB,
      by rw [hk_coord,hyk]⟩
  · intro y _
    exact reflVertex_reflVertex k y
  · intro y _
    exact reflVertex_reflVertex k y
  · intro y _
    have he := connectionToSet_probability_refl k p 0
      ((boundaryBox i₀ h R : Finset (Vertex d)) : Set (Vertex d)) {y}
    rw [hBimg,Set.image_singleton,reflVertex_zero] at he
    exact (congrArg ENNReal.toReal he).symm

/-- Exact count of a separating plane of the box. -/
lemma boundaryPlane_card_le {d : ℕ} {i₀ k : Fin d} (hk : k ≠ i₀) (h R : ℕ) (l : ℤ) :
    ((boundaryBox i₀ h R).filter (fun u => u k = l)).card ≤ (h+1)*(2*R+1)^(d-2) := by
  let t : Fin d → Finset ℤ := fun j =>
    if j = i₀ then Finset.Icc 0 (h : ℤ) else if j = k then {l} else Finset.Icc (-(R : ℤ)) R
  have hsub : (boundaryBox i₀ h R).filter (fun u => u k = l) ⊆ Fintype.piFinset t := by
    intro u hu
    obtain ⟨hub,huk⟩ := Finset.mem_filter.mp hu
    obtain ⟨hubox,hu1,hu2⟩ := Finset.mem_filter.mp hub
    have huc := mem_centeredBox.mp hubox
    rw [Fintype.mem_piFinset]
    intro j
    by_cases hj : j = i₀
    · rw [hj]
      simp only [t,if_pos rfl,Finset.mem_Icc]
      exact ⟨hu1,hu2⟩
    · by_cases hjk : j = k
      · rw [hjk]
        simp [t,hk,huk]
      · simp only [t,if_neg hj,if_neg hjk,Finset.mem_Icc]
        exact huc j
  have hcard := Finset.card_le_card hsub
  rw [Fintype.card_piFinset] at hcard
  have hki : k ∈ (Finset.univ : Finset (Fin d)).erase i₀ :=
    Finset.mem_erase.mpr ⟨hk,Finset.mem_univ k⟩
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i₀),
    ← Finset.mul_prod_erase _ _ hki] at hcard
  have hti : (t i₀).card = h+1 := by
    simp only [t,if_pos rfl,Int.card_Icc]
    omega
  have htk : (t k).card = 1 := by
    simp [t,hk]
  have hrest : ∏ j ∈ ((Finset.univ : Finset (Fin d)).erase i₀).erase k, (t j).card =
      (2*R+1)^(d-2) := by
    rw [Finset.prod_congr rfl (g := fun _ => 2*R+1)]
    · rw [Finset.prod_const,Finset.card_erase_of_mem hki,
        Finset.card_erase_of_mem (Finset.mem_univ i₀),Finset.card_univ,Fintype.card_fin,
        show d-1-1 = d-2 by omega]
    · intro j hj
      have hjk : j ≠ k := (Finset.mem_erase.mp hj).1
      have hji : j ≠ i₀ := (Finset.mem_erase.mp (Finset.mem_erase.mp hj).2).1
      simp only [t,if_neg hji,if_neg hjk,Int.card_Icc]
      omega
  rw [hti,htk,hrest,one_mul] at hcard
  exact hcard

set_option maxHeartbeats 800000 in
/-- R3b: top-face mass from the first-moment mass of `∂̂B` minus the side faces. -/
theorem top_face_mass_lower {d : ℕ} (i₀ : Fin d) {A B C : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hC : 0 ≤ C) (arm : HalfSpaceCriticalArmInput i₀ A)
    (second : SlabBoundarySecondMomentUpper i₀ B) (panis : PanisHalfSpaceTwoPointUpper d C)
    (h R : ℕ) (hh : 1 ≤ h) (hhR : h < R) :
    ∑ y ∈ boundaryHat i₀ h R, (percolation d (criticalPoint d)).real
        (connectionToSetEvent ((boundaryBox i₀ h R : Finset (Vertex d)) : Set (Vertex d)) 0 {y}) ≤
      ∑ y ∈ boundaryTop i₀ h R, (percolation d (criticalPoint d)).real
        (connectionToSetEvent ((boundaryBox i₀ h R : Finset (Vertex d)) : Set (Vertex d)) 0 {y}) +
      ((d-1 : ℕ) : ℝ)*(2*((((h+1)*(2*R+1)^(d-2) : ℕ) : ℝ)*(C*(1+(h : ℝ))/(((R : ℝ)-h)^d)))*
        ((A+B)/(h : ℝ))) := by
  set Bx := boundaryBox i₀ h R with hBxdef
  let f : Vertex d → ℝ := fun y => (percolation d (criticalPoint d)).real
    (connectionToSetEvent ((Bx : Finset (Vertex d)) : Set (Vertex d)) 0 {y})
  have hf : ∀ y, 0 ≤ f y := fun y => measureReal_nonneg
  let K := (Finset.univ : Finset (Fin d)).erase i₀
  let G : Fin d → Finset (Vertex d) := fun k =>
    Bx.filter (fun y => y k = (R : ℤ)) ∪ Bx.filter (fun y => y k = -(R : ℤ))
  let N : ℝ := (((h+1)*(2*R+1)^(d-2) : ℕ) : ℝ)
  let Ct : ℝ := C*(1+(h : ℝ))/(((R : ℝ)-h)^d)
  let M : ℝ := (A+B)/(h : ℝ)
  have hRh : (0 : ℝ) < (R : ℝ)-h := by
    have : (h : ℝ) < R := by exact_mod_cast hhR
    linarith
  have hCt : 0 ≤ Ct := div_nonneg (mul_nonneg hC (by positivity)) (pow_nonneg hRh.le d)
  have hM : 0 ≤ M := div_nonneg (by linarith) (Nat.cast_nonneg h)
  -- cover ∂̂B by the top face and the side faces
  have hcover : boundaryHat i₀ h R ⊆ boundaryTop i₀ h R ∪ K.biUnion G := by
    intro y hy
    obtain ⟨hyB,hcase⟩ := Finset.mem_filter.mp hy
    rcases hcase with htop | ⟨k,hk,hkR⟩
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hyB,htop⟩)
    · refine Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨k,Finset.mem_erase.mpr
        ⟨hk,Finset.mem_univ k⟩,?_⟩)
      rcases hkR with h1 | h2
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hyB,h1⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hyB,h2⟩)
  -- each side pair is bounded through R3a, R2 and reflection
  have hside : ∀ k ∈ K, ∑ y ∈ G k, f y ≤ 2*(N*Ct*M) := by
    intro k hkK
    have hk : k ≠ i₀ := (Finset.mem_erase.mp hkK).1
    have hpos := side_face_mass_le i₀ k A B hA hB arm second h hh R hhR.le Bx
      (fun w hw => ((mem_centeredBox.mp (Finset.mem_filter.mp hw).1) k).2)
    have hplane := plane_mass_le_panis hC panis i₀ k h R hhR Bx
      (fun w hw => (Finset.mem_filter.mp hw).2.1)
      (Bx.filter (fun u => u k = (R : ℤ)-h))
      (by
        intro z hz
        obtain ⟨hzB,hzk⟩ := Finset.mem_filter.mp hz
        obtain ⟨_,hz1,hz2⟩ := Finset.mem_filter.mp hzB
        refine ⟨hz1,hz2,?_⟩
        rw [hzk,abs_of_nonneg (by omega)])
    have hcardR : (((Bx.filter (fun u => u k = (R : ℤ)-h)).card : ℕ) : ℝ) ≤
        (((h+1)*(2*R+1)^(d-2) : ℕ) : ℝ) := by
      exact_mod_cast boundaryPlane_card_le hk h R ((R : ℤ)-h)
    have hplane' : ∑ u ∈ Bx.filter (fun u => u k = (R : ℤ)-h), f u ≤ N*Ct :=
      hplane.trans (mul_le_mul_of_nonneg_right hcardR hCt)
    have hpos' : ∑ y ∈ Bx.filter (fun y => y k = (R : ℤ)), f y ≤ N*Ct*M :=
      hpos.trans (mul_le_mul_of_nonneg_right hplane' hM)
    have hneg := neg_side_face_eq (criticalPoint d) hk h R
    rw [← hBxdef] at hneg
    simp only [G]
    calc ∑ y ∈ Bx.filter (fun y => y k = (R : ℤ)) ∪ Bx.filter (fun y => y k = -(R : ℤ)), f y
        ≤ ∑ y ∈ Bx.filter (fun y => y k = (R : ℤ)), f y +
            ∑ y ∈ Bx.filter (fun y => y k = -(R : ℤ)), f y :=
          sum_union_le_of_nonneg f hf (Bx.filter (fun y => y k = (R : ℤ)))
            (Bx.filter (fun y => y k = -(R : ℤ)))
      _ = 2*∑ y ∈ Bx.filter (fun y => y k = (R : ℤ)), f y := by
          rw [show ∑ y ∈ Bx.filter (fun y => y k = -(R : ℤ)), f y =
              ∑ y ∈ Bx.filter (fun y => y k = (R : ℤ)), f y from hneg]
          ring
      _ ≤ 2*(N*Ct*M) := by linarith
  have hKcard : (K.card : ℝ) = ((d-1 : ℕ) : ℝ) := by
    show (((Finset.univ : Finset (Fin d)).erase i₀).card : ℝ) = _
    rw [Finset.card_erase_of_mem (Finset.mem_univ i₀),Finset.card_univ,Fintype.card_fin]
  calc ∑ y ∈ boundaryHat i₀ h R, f y
      ≤ ∑ y ∈ boundaryTop i₀ h R ∪ K.biUnion G, f y :=
        Finset.sum_le_sum_of_subset_of_nonneg hcover (fun y _ _ => hf y)
    _ ≤ ∑ y ∈ boundaryTop i₀ h R, f y+∑ y ∈ K.biUnion G, f y := sum_union_le_of_nonneg f hf _ _
    _ ≤ ∑ y ∈ boundaryTop i₀ h R, f y+∑ k ∈ K, ∑ y ∈ G k, f y :=
        add_le_add le_rfl (sum_biUnion_le_of_nonneg f hf K G)
    _ ≤ ∑ y ∈ boundaryTop i₀ h R, f y+∑ _k ∈ K, 2*(N*Ct*M) :=
        add_le_add le_rfl (Finset.sum_le_sum hside)
    _ = ∑ y ∈ boundaryTop i₀ h R, f y+((d-1 : ℕ) : ℝ)*(2*(N*Ct)*M) := by
        rw [Finset.sum_const,nsmul_eq_mul,hKcard]
        ring

/-- eq.boundary_0_mean_segment for wide boxes, from the first-moment input and an explicit
width condition (satisfied once R/h is large, since N·Ct ≲ (h/R)² h). -/
theorem top_face_mass_lower_of_wide {d : ℕ} (i₀ : Fin d) {A B C c : ℝ} (hA : 0 ≤ A)
    (hB : 0 ≤ B) (hC : 0 ≤ C) (arm : HalfSpaceCriticalArmInput i₀ A)
    (second : SlabBoundarySecondMomentUpper i₀ B) (panis : PanisHalfSpaceTwoPointUpper d C)
    (h R : ℕ) (hh : 1 ≤ h) (hhR : h < R)
    (hFM : c/(h : ℝ) ≤ ∑ y ∈ boundaryHat i₀ h R, (percolation d (criticalPoint d)).real
        (connectionToSetEvent ((boundaryBox i₀ h R : Finset (Vertex d)) : Set (Vertex d)) 0 {y}))
    (hwide : ((d-1 : ℕ) : ℝ)*(2*((((h+1)*(2*R+1)^(d-2) : ℕ) : ℝ)*
        (C*(1+(h : ℝ))/(((R : ℝ)-h)^d)))*((A+B)/(h : ℝ))) ≤ c/(2*(h : ℝ))) :
    c/(2*(h : ℝ)) ≤ ∑ y ∈ boundaryTop i₀ h R, (percolation d (criticalPoint d)).real
        (connectionToSetEvent ((boundaryBox i₀ h R : Finset (Vertex d)) : Set (Vertex d)) 0 {y}) := by
  have hmain := top_face_mass_lower i₀ hA hB hC arm second panis h R hh hhR
  have hhalf : c/(h : ℝ) = c/(2*(h : ℝ))+c/(2*(h : ℝ)) := by ring
  linarith

end NearCritical
