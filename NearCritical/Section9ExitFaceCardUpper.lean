module
public import NearCritical.Section9ExitFace
public import NearCritical.Section8CubePlaneGeometry
public import Mathlib.Algebra.Order.Floor.Defs

/-! Actual surface cardinality of the discrete source exit face. -/
@[expose] public section
noncomputable section
namespace NearCritical
open scoped Classical

/-- The open upper wall selects one integer level, including nonintegral walls.
No parity or divisibility convention is used. -/
theorem section9_exit_face_coordinate {d : ℕ} (i : Fin d) (n : ℕ)
    {v : Vertex d} (hv : v ∈ section9ExitFace i n) :
    v i = Int.ceil (11*(n : ℝ)/8)-1 := by
  obtain ⟨hvT,hvTip⟩ := Finset.mem_filter.mp hv
  have hshape := (Finset.mem_filter.mp hvT).2
  have hlower : (n : ℝ)+(3/8)*(n : ℝ) ≤ (v i : ℝ)+1 := by
    apply le_of_not_gt
    intro hupper
    apply hvTip
    apply (mem_section9FiniteTube i n (-(5 : ℝ)/8) (3/8)
      (by norm_num) (by norm_num) (bondTip (v,i))).mpr
    refine ⟨?_,?_,?_⟩
    · simp only [bondTip,Function.update_self,Int.cast_add,Int.cast_one]
      linarith [hshape.1]
    · simpa only [bondTip,Function.update_self,Int.cast_add,Int.cast_one] using hupper
    · intro j hji
      simpa only [bondTip,Function.update_of_ne hji] using hshape.2.2 j hji
  have hlo : Int.ceil (11*(n : ℝ)/8) ≤ v i+1 := by
    apply Int.ceil_le.mpr
    push_cast
    linarith
  have hhi : v i < Int.ceil (11*(n : ℝ)/8) := by
    apply Int.lt_ceil.mpr
    linarith [hshape.2.1]
  omega

/-- Actual source exit face has surface order. The finite ambient cube gives
only transverse factors because the axial coordinate is fixed exactly. -/
theorem section9_exit_face_card_upper {d : ℕ} (i : Fin d) (n : ℕ) :
    (section9ExitFace i n).card ≤ (6*n+1)^(d-1) := by
  have hcube (v : Vertex d) (hv : v ∈ section9ExitFace i n) (j : Fin d) :
      (0 : Vertex d) j - ((3*n : ℕ) : ℤ) ≤ v j ∧
        v j ≤ (0 : Vertex d) j + ((3*n : ℕ) : ℤ) := by
    have hvT := (Finset.mem_filter.mp hv).1
    have hb := mem_centeredBox.mp (Finset.mem_filter.mp hvT).1 j
    simpa only [Pi.zero_apply,zero_sub,zero_add] using hb
  have hcount := Section8.translated_cube_plane_card_le (n := 3*n)
    (section9ExitFace i n) (0 : Vertex d) i (Int.ceil (11*(n : ℝ)/8)-1) hcube
  have heq : (section9ExitFace i n).filter
      (fun v => v i = Int.ceil (11*(n : ℝ)/8)-1) = section9ExitFace i n := by
    apply Finset.filter_eq_self.mpr
    exact fun v hv => section9_exit_face_coordinate i n hv
  rw [heq] at hcount
  convert hcount using 1 <;> congr 1 <;> omega

end NearCritical
