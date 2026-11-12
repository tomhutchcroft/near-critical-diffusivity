module
public import NearCritical.Section8CubeFaceMass
public import NearCritical.LatticeShells

/-! Literal source cube/half-space specialization of the actual face estimate. -/
@[expose] public section
noncomputable section
namespace NearCritical.Section8
open Set MeasureTheory
open scoped Classical

/-- The source domain (x + Lambda_n) intersected with the coordinate half-space. -/
def sourceHalfCube {d : ℕ} (x : Vertex d) (n : ℕ) (j : Fin d) : Finset (Vertex d) :=
  ((latticeSupCube d n).image (fun z => x+z)).filter (fun y => 0 ≤ y j)

theorem mem_sourceHalfCube {d n : ℕ} (x y : Vertex d) (j : Fin d) :
    y ∈ sourceHalfCube x n j ↔
      (∀ k, x k-(n : ℤ) ≤ y k ∧ y k ≤ x k+(n : ℤ)) ∧ 0 ≤ y j := by
  constructor
  · intro hy
    obtain ⟨hy,hpos⟩ := Finset.mem_filter.mp hy
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hy
    refine ⟨?_,hpos⟩
    intro k
    have hk := abs_le.mp (mem_latticeSupCube.mp hz k)
    change x k-(n : ℤ) ≤ x k+z k ∧ x k+z k ≤ x k+(n : ℤ)
    constructor <;> omega
  · rintro ⟨hbox,hpos⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_image.mpr ⟨y-x,?_,?_⟩,hpos⟩
    · apply mem_latticeSupCube.mpr
      intro k
      apply abs_le.mpr
      have hk := hbox k
      change -(n : ℤ) ≤ y k-x k ∧ y k-x k ≤ (n : ℤ)
      constructor <;> omega
    · ext k
      change x k+(y k-x k) = y k
      omega

/-- The paper's cube-face sum, with all standard literature inputs explicit.
The source condition x_j <= n is not needed for this upper estimate. -/
theorem source_cube_face_mass_le {d n : ℕ} (hd : 1 ≤ d) (hn : 1 ≤ n)
    (C A B : ℝ) (hC : 0 ≤ C) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (panis : PanisHalfSpaceTwoPointUpper d C)
    (arm : ∀ i : Fin d, HalfSpaceCriticalArmInput i A)
    (second : ∀ i : Fin d, SlabBoundarySecondMomentUpper i B)
    (x : Vertex d) (j : Fin d) (hx : 0 ≤ x j) :
    (∑ y ∈ cubeNonbottomFaces (sourceHalfCube x n j) x n j,
      (percolation d (criticalPoint d)).real
        (connectionToSetEvent (sourceHalfCube x n j : Set (Vertex d)) x {y})) ≤
      (((2*d-1 : ℕ) : ℝ)*(4*C*(A+B)*(9 : ℝ)^(d-1)))*(1+(x j : ℝ))/(n : ℝ) := by
  have hxQ : x ∈ sourceHalfCube x n j := by
    apply (mem_sourceHalfCube x x j).mpr
    refine ⟨?_,hx⟩
    intro k
    constructor <;> omega
  have hQ : ∀ y ∈ sourceHalfCube x n j, ∀ k,
      x k-(n : ℤ) ≤ y k ∧ y k ≤ x k+(n : ℤ) := by
    intro y hy
    exact ((mem_sourceHalfCube x y j).mp hy).1
  have hD : (sourceHalfCube x n j : Set (Vertex d)) ⊆ coordinateHalfSpace j 0 true := by
    intro y hy
    have hpos := ((mem_sourceHalfCube x y j).mp hy).2
    change 0 ≤ coordinateDepth j 0 true y
    have hreal : (0 : ℝ) ≤ (y j : ℝ) := by exact_mod_cast hpos
    simpa [coordinateDepth] using hreal
  have h := cube_nonbottom_mass_le hd hn C A B hC hA hB panis
    (sourceHalfCube x n j) x hxQ j 0 true arm second hQ hD
  simp only [coordinateDepth, if_true, Int.cast_zero, sub_zero] at h
  convert h using 1 <;> ring

/-- One strictly positive constant works for all source cubes and scales. -/
theorem exists_source_cube_face_upper {d : ℕ} (hd : 1 ≤ d)
    (C A B : ℝ) (hC : 0 ≤ C) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (panis : PanisHalfSpaceTwoPointUpper d C)
    (arm : ∀ i : Fin d, HalfSpaceCriticalArmInput i A)
    (second : ∀ i : Fin d, SlabBoundarySecondMomentUpper i B) :
    ∃ K : ℝ, 0 < K ∧ ∀ (n : ℕ), 1 ≤ n → ∀ (x : Vertex d) (j : Fin d),
      0 ≤ x j →
      (∑ y ∈ cubeNonbottomFaces (sourceHalfCube x n j) x n j,
        (percolation d (criticalPoint d)).real
          (connectionToSetEvent (sourceHalfCube x n j : Set (Vertex d)) x {y})) ≤
        K*(1+(x j : ℝ))/(n : ℝ) := by
  let K := (((2*d-1 : ℕ) : ℝ)*(4*C*(A+B)*(9 : ℝ)^(d-1)))
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨K+1,by positivity,?_⟩
  intro n hn x j hx
  have hxR : (0 : ℝ) ≤ (x j : ℝ) := by exact_mod_cast hx
  calc
    _ ≤ K*(1+(x j : ℝ))/(n : ℝ) :=
      source_cube_face_mass_le hd hn C A B hC hA hB panis arm second x j hx
    _ ≤ (K+1)*(1+(x j : ℝ))/(n : ℝ) := by
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
      exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)

end NearCritical.Section8
