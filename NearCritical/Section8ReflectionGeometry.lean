module
public import NearCritical.AffineReflectionDeleted
public import NearCritical.Section8ExtensionSourceGeometry
public import NearCritical.RectangleBoundary

/-! Exact affine reflection of the OPEN source cube/tube and face geometry. -/
@[expose] public section
noncomputable section
namespace NearCritical
open scoped Classical

/-- Actual negative axial face core of Q3, using its predecessor-outside
condition rather than an incorrectly rounded coordinate equality. -/
def section8ExtensionNegativeFaceCore {d : ℕ} (i : Fin d) (n : ℕ) : Finset (Vertex d) :=
  (section9FiniteEndCube i n (2*(n : ℝ))).filter fun x =>
    bondPredecessor x i ∉ section9FiniteEndCube i n (2*(n : ℝ)) ∧
      ∀ j, j ≠ i → -(n : ℝ)/4 < (x j : ℝ) ∧ (x j : ℝ) < (n : ℝ)/4

private theorem source_reflect_coord_self {d : ℕ} (i : Fin d) (n : ℕ) (v : Vertex d) :
    (affineReflection (Pi.single i (2*(n : ℤ))) v i : ℝ) = 2*(n : ℝ)-(v i : ℝ) := by
  simp [affineReflection,Pi.sub_apply,Int.cast_sub,Int.cast_mul]

private theorem source_reflect_coord_ne {d : ℕ} (i : Fin d) (n : ℕ)
    (v : Vertex d) (j : Fin d) (hji : j ≠ i) :
    (affineReflection (Pi.single i (2*(n : ℤ))) v j : ℝ) = -(v j : ℝ) := by
  simp [affineReflection,Pi.sub_apply,Pi.single_apply,hji,Ne.symm hji]

private theorem source_reflect_mem_image {d : ℕ} (i : Fin d) (n : ℕ)
    (S : Finset (Vertex d)) (v : Vertex d) :
    v ∈ S.image (affineReflection (Pi.single i (2*(n : ℤ)))) ↔
      affineReflection (Pi.single i (2*(n : ℤ))) v ∈ S := by
  let f := affineReflection (Pi.single i (2*(n : ℤ)))
  have hinv (x : Vertex d) : f (f x) = x := by simp [f,affineReflection]
  constructor
  · intro hv
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hv
    change f (f x) ∈ S
    rw [hinv]
    exact hx
  · intro hv
    exact Finset.mem_image.mpr ⟨f v,hv,hinv v⟩

private theorem source_reflect_end_shape {d : ℕ} (i : Fin d) (n : ℕ)
    (v : Vertex d) (width center : ℝ) :
    affineReflection (Pi.single i (2*(n : ℤ))) v ∈ sprinklingEndCube i width center ↔
      v ∈ sprinklingEndCube i width (2*(n : ℝ)-center) := by
  constructor <;> intro h j <;> have hj := h j <;> by_cases hji : j = i
  · subst j
    simp only [ite_true,source_reflect_coord_self] at hj ⊢
    constructor <;> linarith [hj.1,hj.2]
  · simp only [hji,ite_false,sub_zero,source_reflect_coord_ne i n v j hji] at hj ⊢
    constructor <;> linarith [hj.1,hj.2]
  · subst j
    simp only [ite_true,source_reflect_coord_self] at hj ⊢
    constructor <;> linarith [hj.1,hj.2]
  · simp only [hji,ite_false,sub_zero,source_reflect_coord_ne i n v j hji] at hj ⊢
    constructor <;> linarith [hj.1,hj.2]

private theorem source_reflect_cube_iff {d : ℕ} (i : Fin d) (n : ℕ) (v : Vertex d) :
    (affineReflection (Pi.single i (2*(n : ℤ))) v ∈ section9FiniteEndCube i n 0 ↔
      v ∈ section9FiniteEndCube i n (2*(n : ℝ))) ∧
    (affineReflection (Pi.single i (2*(n : ℤ))) v ∈ section9FiniteEndCube i n (2*(n : ℝ)) ↔
      v ∈ section9FiniteEndCube i n 0) := by
  have h0 : -2*(n : ℝ) ≤ 0 ∧ (0 : ℝ) ≤ 2*(n : ℝ) := by
    constructor <;> nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have h2 : -2*(n : ℝ) ≤ 2*(n : ℝ) ∧ 2*(n : ℝ) ≤ 2*(n : ℝ) := by
    constructor
    · nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    · rfl
  constructor
  · rw [mem_section9FiniteEndCube i n 0 h0,
      mem_section9FiniteEndCube i n (2*(n : ℝ)) h2]
    simpa only [sub_zero] using source_reflect_end_shape i n v (n : ℝ) 0
  · rw [mem_section9FiniteEndCube i n (2*(n : ℝ)) h2,mem_section9FiniteEndCube i n 0 h0]
    simpa only [sub_self] using source_reflect_end_shape i n v (n : ℝ) (2*(n : ℝ))

/-- The exact finite open first and third source cubes are exchanged. The
containing enumeration box need not itself be reflection invariant. -/
theorem section8_reflection_source_cubes {d : ℕ} (i : Fin d) (n : ℕ) :
    (section9FiniteEndCube i n 0).image (affineReflection (Pi.single i (2*(n : ℤ)))) =
      section9FiniteEndCube i n (2*(n : ℝ)) ∧
    (section9FiniteEndCube i n (2*(n : ℝ))).image (affineReflection (Pi.single i (2*(n : ℤ)))) =
      section9FiniteEndCube i n 0 := by
  constructor <;> ext v <;> rw [source_reflect_mem_image]
  · exact (source_reflect_cube_iff i n v).1
  · exact (source_reflect_cube_iff i n v).2

private theorem source_reflect_tube_shape {d : ℕ} (i : Fin d) (n : ℕ)
    (v : Vertex d) (lo hi : ℝ) :
    affineReflection (Pi.single i (2*(n : ℤ))) v ∈ sprinklingTube i n lo hi ↔
      v ∈ sprinklingTube i n (-hi) (-lo) := by
  constructor
  · intro h
    have hl := h.1
    have hu := h.2.1
    rw [source_reflect_coord_self] at hl hu
    refine ⟨by nlinarith only [hu],by nlinarith only [hl],?_⟩
    intro j hji
    have ht := h.2.2 j hji
    rw [source_reflect_coord_ne i n v j hji] at ht
    constructor <;> linarith [ht.1,ht.2]
  · intro h
    refine ⟨?_,?_,?_⟩
    · rw [source_reflect_coord_self]
      nlinarith only [h.2.1]
    · rw [source_reflect_coord_self]
      nlinarith only [h.1]
    · intro j hji
      rw [source_reflect_coord_ne i n v j hji]
      have ht := h.2.2 j hji
      constructor <;> linarith [ht.1,ht.2]

private theorem source_reflect_tube_iff {d : ℕ} (i : Fin d) (n : ℕ) (v : Vertex d) :
    (affineReflection (Pi.single i (2*(n : ℤ))) v ∈
        section9FiniteTube i n (-(5 : ℝ)/8) (3/8) ↔
      v ∈ section9FiniteTube i n (-(3 : ℝ)/8) (5/8)) ∧
    (affineReflection (Pi.single i (2*(n : ℤ))) v ∈
        section9FiniteTube i n (-(3 : ℝ)/8) (5/8) ↔
      v ∈ section9FiniteTube i n (-(5 : ℝ)/8) (3/8)) := by
  constructor
  · rw [mem_section9FiniteTube i n (-(5 : ℝ)/8) (3/8) (by norm_num) (by norm_num),
      mem_section9FiniteTube i n (-(3 : ℝ)/8) (5/8) (by norm_num) (by norm_num)]
    simpa only [neg_div,neg_neg] using source_reflect_tube_shape i n v (-(5 : ℝ)/8) (3/8)
  · rw [mem_section9FiniteTube i n (-(3 : ℝ)/8) (5/8) (by norm_num) (by norm_num),
      mem_section9FiniteTube i n (-(5 : ℝ)/8) (3/8) (by norm_num) (by norm_num)]
    simpa only [neg_div,neg_neg] using source_reflect_tube_shape i n v (-(3 : ℝ)/8) (5/8)

/-- Exact source T12/T23 reflection, with no parity or rounding condition. -/
theorem section8_reflection_source_tubes {d : ℕ} (i : Fin d) (n : ℕ) :
    (section9FiniteTube i n (-(5 : ℝ)/8) (3/8)).image
        (affineReflection (Pi.single i (2*(n : ℤ)))) =
      section9FiniteTube i n (-(3 : ℝ)/8) (5/8) ∧
    (section9FiniteTube i n (-(3 : ℝ)/8) (5/8)).image
        (affineReflection (Pi.single i (2*(n : ℤ)))) =
      section9FiniteTube i n (-(5 : ℝ)/8) (3/8) := by
  constructor <;> ext v <;> rw [source_reflect_mem_image]
  · exact (source_reflect_tube_iff i n v).1
  · exact (source_reflect_tube_iff i n v).2

/-- The actual side-n/2 middle core is invariant about its axial center n. -/
theorem section8_reflection_middle_core {d : ℕ} (i : Fin d) (n : ℕ) :
    (section8ExtensionMiddleCore i n).image (affineReflection (Pi.single i (2*(n : ℤ)))) =
      section8ExtensionMiddleCore i n := by
  ext v
  rw [source_reflect_mem_image,section8_mem_extension_middle_core,section8_mem_extension_middle_core]
  have hc : 2*(n : ℝ)-(n : ℝ) = (n : ℝ) := by linarith
  simpa only [hc] using source_reflect_end_shape i n v ((n : ℝ)/2) (n : ℝ)

private theorem source_reflect_predecessor {d : ℕ} (c v : Vertex d) (i : Fin d) :
    affineReflection c (bondPredecessor v i) = bondTip (affineReflection c v,i) := by
  funext j
  by_cases hji : j = i
  · subst j
    simp only [affineReflection,Equiv.coe_fn_mk,bondPredecessor,bondTip,Pi.sub_apply,Function.update_self]
    omega
  · simp [affineReflection,bondPredecessor,bondTip,Pi.sub_apply,hji]

/-- The positive face maps EXACTLY to the negative predecessor-outside core.
The affine center is 2n, not the 2n+1 used for asymmetric closed water cubes. -/
theorem section8_reflection_positive_face_core {d : ℕ} (i : Fin d) (n : ℕ) :
    (section8ExtensionPositiveFaceCore i n).image (affineReflection (Pi.single i (2*(n : ℤ)))) =
      section8ExtensionNegativeFaceCore i n := by
  ext v
  rw [source_reflect_mem_image]
  have hcube := (source_reflect_cube_iff i n v).1
  have htip : bondTip (affineReflection (Pi.single i (2*(n : ℤ))) v,i) ∈ section9FiniteEndCube i n 0 ↔
      bondPredecessor v i ∈ section9FiniteEndCube i n (2*(n : ℝ)) := by
    rw [← source_reflect_predecessor]
    exact (source_reflect_cube_iff i n (bondPredecessor v i)).1
  have htrans :
      (∀ j, j ≠ i → -(n : ℝ)/4 <
          (affineReflection (Pi.single i (2*(n : ℤ))) v j : ℝ) ∧
          (affineReflection (Pi.single i (2*(n : ℤ))) v j : ℝ) < (n : ℝ)/4) ↔
      (∀ j, j ≠ i → -(n : ℝ)/4 < (v j : ℝ) ∧ (v j : ℝ) < (n : ℝ)/4) := by
    constructor <;> intro h j hji <;> have ht := h j hji
    · rw [source_reflect_coord_ne i n v j hji] at ht
      constructor <;> linarith [ht.1,ht.2]
    · rw [source_reflect_coord_ne i n v j hji]
      constructor <;> linarith [ht.1,ht.2]
  simp only [section8ExtensionPositiveFaceCore,section8ExtensionNegativeFaceCore,Finset.mem_filter]
  exact and_congr hcube (and_congr (not_congr htip) htrans)

end NearCritical
