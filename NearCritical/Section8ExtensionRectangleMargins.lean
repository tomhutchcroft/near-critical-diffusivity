module
public import NearCritical.Section8ExtensionSourceGeometry

/-! Literal coordinate margins for the source unique-extension rectangle. -/
@[expose] public section
noncomputable section
namespace NearCritical
open scoped Classical

private theorem rectangle_face_axial_bounds {d : ℕ} (i : Fin d) (n : ℕ)
    {x : Vertex d} (hx : x ∈ section8ExtensionPositiveFaceCore i n) :
    (x i : ℝ) < (n : ℝ)/2 ∧ (n : ℝ)/2 ≤ (x i : ℝ)+1 := by
  obtain ⟨hxQ,hxTip,hxTrans⟩ := Finset.mem_filter.mp hx
  have hxShape := (Finset.mem_filter.mp hxQ).2
  have hxi := hxShape i
  simp only [ite_true,sub_zero] at hxi
  refine ⟨hxi.2,?_⟩
  apply le_of_not_gt
  intro htipUpper
  apply hxTip
  apply (mem_section9FiniteEndCube i n 0 (by constructor <;> nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]) (bondTip (x,i))).mpr
  intro j
  by_cases hji : j = i
  · subst j
    simp only [bondTip,Function.update_self,Int.cast_add,Int.cast_one,ite_true,sub_zero]
    constructor <;> linarith [hxi.1]
  · simpa [bondTip,hji] using hxShape j

/-- Both source endpoints have margin n/16 inside the literal T12 rectangle.
The finite enumeration agrees exactly with the open coordinate rectangle. -/
theorem section8_extension_rectangle_margins {d : ℕ} (i : Fin d) (n r : ℕ)
    (hn : 16*(r+1) ≤ n) {x z : Vertex d}
    (hx : x ∈ section8ExtensionPositiveFaceCore i n)
    (hz : z ∈ section8ExtensionMiddleCore i n) :
    let l : Fin d → ℝ := fun j => if j = i then 3/8 else -3/8
    let u : Fin d → ℝ := fun j => if j = i then 11/8 else 3/8
    let a : Vertex d := Function.update x i (x i + (r : ℤ))
    (∀ j, u j - l j ≤ 1) ∧
    (∀ j, l j * (n : ℝ) + (n : ℝ)/16 ≤ (a j : ℝ) ∧
      (a j : ℝ) ≤ u j * (n : ℝ) - (n : ℝ)/16) ∧
    (∀ j, l j * (n : ℝ) + (n : ℝ)/16 ≤ (z j : ℝ) ∧
      (z j : ℝ) ≤ u j * (n : ℝ) - (n : ℝ)/16) ∧
    {v : Vertex d | ∀ j, l j * (n : ℝ) < (v j : ℝ) ∧
      (v j : ℝ) < u j * (n : ℝ)} =
      (↑(section9FiniteTube i n (-(5 : ℝ)/8) (3/8)) : Set (Vertex d)) := by
  dsimp only
  have hnR : 16*((r : ℝ)+1) ≤ n := by exact_mod_cast hn
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hxAxial := rectangle_face_axial_bounds i n hx
  have hxTrans := (Finset.mem_filter.mp hx).2.2
  have hzShape := (section8_mem_extension_middle_core i n z).mp hz
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j
    split_ifs <;> norm_num
  · intro j
    by_cases hji : j = i
    · subst j
      simp only [ite_true, Function.update_self, Int.cast_add, Int.cast_natCast]
      constructor <;> linarith [hxAxial.1, hxAxial.2]
    · simp only [hji, ite_false, Function.update_of_ne hji]
      obtain ⟨hl, hu⟩ := hxTrans j hji
      constructor <;> linarith
  · intro j
    have hj := hzShape j
    by_cases hji : j = i
    · subst j
      simp only [ite_true] at hj ⊢
      constructor <;> linarith [hj.1, hj.2]
    · simp only [hji, ite_false, sub_zero] at hj ⊢
      constructor <;> linarith [hj.1, hj.2]
  · ext v
    change (∀ j, (if j = i then (3 : ℝ)/8 else -3/8) * (n : ℝ) < (v j : ℝ) ∧
      (v j : ℝ) < (if j = i then (11 : ℝ)/8 else 3/8) * (n : ℝ)) ↔
      v ∈ section9FiniteTube i n (-(5 : ℝ)/8) (3/8)
    rw [mem_section9FiniteTube i n (-(5 : ℝ)/8) (3/8)
      (by norm_num) (by norm_num) v]
    change _ ↔ (n : ℝ) + (-(5 : ℝ)/8)*(n : ℝ) < (v i : ℝ) ∧
      (v i : ℝ) < (n : ℝ) + (3/8)*(n : ℝ) ∧
      ∀ j, j ≠ i → -3*(n : ℝ)/8 < (v j : ℝ) ∧ (v j : ℝ) < 3*(n : ℝ)/8
    constructor
    · intro hv
      have hi := hv i
      simp only [ite_true] at hi
      refine ⟨by linarith [hi.1], by linarith [hi.2], ?_⟩
      intro j hji
      have hj := hv j
      simp only [hji, ite_false] at hj
      constructor <;> linarith [hj.1, hj.2]
    · rintro ⟨hl, hu, ht⟩ j
      by_cases hji : j = i
      · subst j
        simp only [ite_true]
        constructor <;> linarith
      · simp only [hji, ite_false]
        obtain ⟨hjl, hju⟩ := ht j hji
        constructor <;> linarith

end NearCritical
