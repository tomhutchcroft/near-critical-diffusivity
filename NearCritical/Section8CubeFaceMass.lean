module
public import NearCritical.Section8CubeMidpointMass
public import NearCritical.Section8FiniteFaceMass

/-! Actual cube-face masses from the retained-slab decomposition. -/
@[expose] public section
noncomputable section
namespace NearCritical.Section8
open Set MeasureTheory
open scoped Classical

/-- Positive coordinate face, with the original finite domain retained in
all connection probabilities. Constants are uniform in the cube radius. -/
theorem cube_positive_face_mass_le {d n : ℕ} (hd : 1 ≤ d) (hn : 1 ≤ n)
    (C A B : ℝ) (hC : 0 ≤ C) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (panis : PanisHalfSpaceTwoPointUpper d C)
    (Q : Finset (Vertex d)) (x : Vertex d) (hx : x ∈ Q)
    (i j : Fin d) (wall : ℤ) (positive : Bool)
    (arm : HalfSpaceCriticalArmInput i A) (second : SlabBoundarySecondMomentUpper i B)
    (hQ : ∀ y ∈ Q, ∀ k, x k-(n : ℤ) ≤ y k ∧ y k ≤ x k+(n : ℤ))
    (hD : (Q : Set (Vertex d)) ⊆ coordinateHalfSpace j wall positive) :
    (∑ y ∈ Q.filter (fun y => y i = x i+(n : ℤ)),
      (percolation d (criticalPoint d)).real
        (connectionToSetEvent (Q : Set (Vertex d)) x {y})) ≤
      (4*C*(A+B)*(9 : ℝ)^(d-1))*(1+coordinateDepth j wall positive x)/(n : ℝ) := by
  let m := n/2
  let h := n-m
  have hm : m ≤ n := by dsimp [m]; omega
  have hh : 1 ≤ h := by dsimp [h,m]; omega
  have htwice : n ≤ 2*h := by dsimp [h,m]; omega
  have htop : x i+(m : ℤ)+(h : ℤ) = x i+(n : ℤ) := by
    dsimp [h]
    omega
  have hupper : ∀ y ∈ Q, y i ≤ x i+(m : ℤ)+(h : ℤ) := by
    intro y hy
    rw [htop]
    exact (hQ y hy i).2
  have hsplit := finite_top_face_mass_le_midplane i A B hA hB arm second h hh Q x
    (x i+(m : ℤ)) (by omega) hupper
  rw [htop] at hsplit
  have hcut : |(x i : ℝ)-((x i+(m : ℤ) : ℤ) : ℝ)| = ((n/2 : ℕ) : ℝ) := by
    have he : (x i : ℝ)-((x i+(m : ℤ) : ℤ) : ℝ) = -(m : ℝ) := by
      push_cast
      ring
    rw [he, abs_neg, abs_of_nonneg (Nat.cast_nonneg m)]
  have hmid := cube_midpoint_connection_mass_le hd hn C hC panis Q x hx i j
    (x i+(m : ℤ)) wall positive hQ hD hcut
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hhpos : (0 : ℝ) < h := by exact_mod_cast (show 0 < h by omega)
  have htwiceR : (n : ℝ) ≤ 2*(h : ℝ) := by exact_mod_cast htwice
  have hdepth : 0 ≤ coordinateDepth j wall positive x := hD hx
  have hratio : (A+B)/(h : ℝ) ≤ (2*(A+B))/(n : ℝ) := by
    apply (div_le_div_iff₀ hhpos hnpos).mpr
    nlinarith [mul_nonneg (add_nonneg hA hB) (sub_nonneg.mpr htwiceR)]
  calc
    _ ≤ _ := hsplit
    _ ≤ ((2*C*(9 : ℝ)^(d-1))*(1+coordinateDepth j wall positive x))*
        ((A+B)/(h : ℝ)) := mul_le_mul_of_nonneg_right hmid (by positivity)
    _ ≤ ((2*C*(9 : ℝ)^(d-1))*(1+coordinateDepth j wall positive x))*
        ((2*(A+B))/(n : ℝ)) := mul_le_mul_of_nonneg_left hratio (by positivity)
    _ = _ := by ring

private theorem inverted_coordinateDepth {d : ℕ} (j : Fin d) (wall : ℤ)
    (positive : Bool) (x : Vertex d) :
    coordinateDepth j (-wall) (!positive) (-x) = coordinateDepth j wall positive x := by
  cases positive <;> simp [coordinateDepth] <;> ring

/-- Negative coordinate face, obtained by inverting the entire domain and event. -/
theorem cube_negative_face_mass_le {d n : ℕ} (hd : 1 ≤ d) (hn : 1 ≤ n)
    (C A B : ℝ) (hC : 0 ≤ C) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (panis : PanisHalfSpaceTwoPointUpper d C)
    (Q : Finset (Vertex d)) (x : Vertex d) (hx : x ∈ Q)
    (i j : Fin d) (wall : ℤ) (positive : Bool)
    (arm : HalfSpaceCriticalArmInput i A) (second : SlabBoundarySecondMomentUpper i B)
    (hQ : ∀ y ∈ Q, ∀ k, x k-(n : ℤ) ≤ y k ∧ y k ≤ x k+(n : ℤ))
    (hD : (Q : Set (Vertex d)) ⊆ coordinateHalfSpace j wall positive) :
    (∑ y ∈ Q.filter (fun y => y i = x i-(n : ℤ)),
      (percolation d (criticalPoint d)).real
        (connectionToSetEvent (Q : Set (Vertex d)) x {y})) ≤
      (4*C*(A+B)*(9 : ℝ)^(d-1))*(1+coordinateDepth j wall positive x)/(n : ℝ) := by
  let Q' := Q.image Neg.neg
  have hx' : -x ∈ Q' := Finset.mem_image.mpr ⟨x,hx,rfl⟩
  have hQ' : ∀ y ∈ Q', ∀ k,
      (-x) k-(n : ℤ) ≤ y k ∧ y k ≤ (-x) k+(n : ℤ) := by
    intro y hy k
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hy
    have hh := hQ z hz k
    change -x k-(n : ℤ) ≤ -z k ∧ -z k ≤ -x k+(n : ℤ)
    constructor <;> omega
  have hD' : (Q' : Set (Vertex d)) ⊆ coordinateHalfSpace j (-wall) (!positive) := by
    intro y hy
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hy
    change 0 ≤ coordinateDepth j (-wall) (!positive) (-z)
    rw [inverted_coordinateDepth]
    exact hD hz
  have hprob (y : Vertex d) :
      (percolation d (criticalPoint d)).real
        (connectionToSetEvent (Q' : Set (Vertex d)) (-x) {-y}) =
      (percolation d (criticalPoint d)).real
        (connectionToSetEvent (Q : Set (Vertex d)) x {y}) := by
    have he := connectionToSet_probability_inversion (criticalPoint d) x
      (Q : Set (Vertex d)) {y}
    simpa only [measureReal_def,Q',Finset.coe_image,Set.image_singleton]
      using congrArg ENNReal.toReal he
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
  have hp := cube_positive_face_mass_le hd hn C A B hC hA hB panis Q' (-x) hx'
    i j (-wall) (!positive) arm second hQ' hD'
  rw [he, inverted_coordinateDepth] at hp
  exact hp

/-- Union of all coordinate faces except the negative face in coordinate j.
The finite domain already imposes the ambient half-space restriction. -/
def cubeNonbottomFaces {d : ℕ} (Q : Finset (Vertex d)) (x : Vertex d)
    (n : ℕ) (j : Fin d) : Finset (Vertex d) :=
  Q.filter fun y => ∃ a ∈ (Finset.univ : Finset (Fin d × Bool)).erase (j,false),
    y a.1 = x a.1 + (if a.2 then (n : ℤ) else -(n : ℤ))

/-- Actual nonbottom boundary mass. Face overlaps only improve the upper bound. -/
theorem cube_nonbottom_mass_le {d n : ℕ} (hd : 1 ≤ d) (hn : 1 ≤ n)
    (C A B : ℝ) (hC : 0 ≤ C) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (panis : PanisHalfSpaceTwoPointUpper d C)
    (Q : Finset (Vertex d)) (x : Vertex d) (hx : x ∈ Q)
    (j : Fin d) (wall : ℤ) (positive : Bool)
    (arm : ∀ i : Fin d, HalfSpaceCriticalArmInput i A)
    (second : ∀ i : Fin d, SlabBoundarySecondMomentUpper i B)
    (hQ : ∀ y ∈ Q, ∀ k, x k-(n : ℤ) ≤ y k ∧ y k ≤ x k+(n : ℤ))
    (hD : (Q : Set (Vertex d)) ⊆ coordinateHalfSpace j wall positive) :
    (∑ y ∈ cubeNonbottomFaces Q x n j,
      (percolation d (criticalPoint d)).real
        (connectionToSetEvent (Q : Set (Vertex d)) x {y})) ≤
      ((2*d-1 : ℕ) : ℝ)*
        ((4*C*(A+B)*(9 : ℝ)^(d-1))*(1+coordinateDepth j wall positive x)/(n : ℝ)) := by
  let S := (Finset.univ : Finset (Fin d × Bool)).erase (j,false)
  let face := fun a : Fin d × Bool => Q.filter fun y =>
    y a.1 = x a.1 + (if a.2 then (n : ℤ) else -(n : ℤ))
  let f := fun y : Vertex d => (percolation d (criticalPoint d)).real
    (connectionToSetEvent (Q : Set (Vertex d)) x {y})
  let K := (4*C*(A+B)*(9 : ℝ)^(d-1))*(1+coordinateDepth j wall positive x)/(n : ℝ)
  have hface (a : Fin d × Bool) : (∑ y ∈ face a, f y) ≤ K := by
    obtain ⟨i,b⟩ := a
    cases b
    · simpa [face,f,K,sub_eq_add_neg] using
        cube_negative_face_mass_le hd hn C A B hC hA hB panis Q x hx
          i j wall positive (arm i) (second i) hQ hD
    · simpa [face,f,K] using
        cube_positive_face_mass_le hd hn C A B hC hA hB panis Q x hx
          i j wall positive (arm i) (second i) hQ hD
  have hcover (y : Vertex d) (hy : y ∈ cubeNonbottomFaces Q x n j) :
      f y ≤ ∑ a ∈ S, if y ∈ face a then f y else 0 := by
    obtain ⟨hyQ,a,ha,he⟩ := Finset.mem_filter.mp hy
    have hmem : y ∈ face a := Finset.mem_filter.mpr ⟨hyQ,he⟩
    calc
      f y = (if y ∈ face a then f y else 0) := by rw [if_pos hmem]
      _ ≤ ∑ a ∈ S, if y ∈ face a then f y else 0 :=
        Finset.single_le_sum (s := S)
          (f := fun a => if y ∈ face a then f y else 0)
          (fun a _ => by split_ifs <;> positivity) ha
  have hcard : S.card = 2*d-1 := by
    simp [S,Finset.card_erase_of_mem,Finset.mem_univ,Fintype.card_prod,
      Fintype.card_fin,Fintype.card_bool,Nat.mul_comm]
  calc
    _ ≤ ∑ y ∈ cubeNonbottomFaces Q x n j,
        ∑ a ∈ S, if y ∈ face a then f y else 0 := Finset.sum_le_sum hcover
    _ ≤ ∑ y ∈ Q, ∑ a ∈ S, if y ∈ face a then f y else 0 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro y _ _
      exact Finset.sum_nonneg (fun a _ => by split_ifs <;> positivity)
    _ = ∑ a ∈ S, ∑ y ∈ face a, f y := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      simp only [face,Finset.sum_filter,Finset.mem_filter]
      apply Finset.sum_congr rfl
      intro y hy
      simp only [hy,true_and]
    _ ≤ ∑ _a ∈ S, K := Finset.sum_le_sum (fun a _ => hface a)
    _ = _ := by rw [Finset.sum_const,nsmul_eq_mul,hcard]

end NearCritical.Section8
