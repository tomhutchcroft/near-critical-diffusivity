module
public import NearCritical.Section8OutwardSegment
public import NearCritical.Section9FiniteGeometry

/-! Actual source geometry for the finite unique-extension surgery. -/
@[expose] public section
noncomputable section
namespace NearCritical
open scoped Classical

/-- Interior of the positive axial face of the source OPEN side-n cube. -/
def section8ExtensionPositiveFaceCore {d : ℕ} (i : Fin d) (n : ℕ) : Finset (Vertex d) :=
  (section9FiniteEndCube i n 0).filter fun x =>
    bondTip (x,i) ∉ section9FiniteEndCube i n 0 ∧
      ∀ j, j ≠ i → -(n : ℝ)/4 < (x j : ℝ) ∧ (x j : ℝ) < (n : ℝ)/4

/-- Literal S2'=n e_i+Λ_(n/2), with side length n/2 and axial center n. -/
def section8ExtensionMiddleCore {d : ℕ} (i : Fin d) (n : ℕ) : Finset (Vertex d) :=
  (centeredBox d (3*n)).filter fun z => z ∈ sprinklingEndCube i ((n : ℝ)/2) (n : ℝ)

/-- The finite enumeration box removes no point of the actual S2' shape. -/
theorem section8_mem_extension_middle_core {d : ℕ} (i : Fin d) (n : ℕ) (z : Vertex d) :
    z ∈ section8ExtensionMiddleCore i n ↔ z ∈ sprinklingEndCube i ((n : ℝ)/2) (n : ℝ) := by
  constructor
  · exact fun hz => (Finset.mem_filter.mp hz).2
  · intro hz
    apply Finset.mem_filter.mpr
    refine ⟨mem_centeredBox.mpr ?_,hz⟩
    intro j
    have hj := hz j
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hb : -3*(n : ℝ) ≤ (z j : ℝ) ∧ (z j : ℝ) ≤ 3*(n : ℝ) := by
      by_cases hji : j = i
      · subst j
        simp only [ite_true] at hj
        constructor <;> linarith [hj.1,hj.2]
      · simp only [hji,ite_false,sub_zero] at hj
        constructor <;> linarith [hj.1,hj.2]
    constructor
    · exact_mod_cast hb.1
    · exact_mod_cast hb.2

private theorem extension_face_axial_bounds {d : ℕ} (i : Fin d) (n : ℕ)
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

/-- At scales n≥16(r+1), the actual source face/core geometry supplies
all remaining surgery geometry: Q lies behind x, the whole outward segment
lies in T12, and the target z is outside that segment. -/
theorem section8_extension_source_geometry {d : ℕ} (i : Fin d) (n r : ℕ)
    (hn : 16*(r+1) ≤ n) {x z : Vertex d}
    (hx : x ∈ section8ExtensionPositiveFaceCore i n)
    (hz : z ∈ section8ExtensionMiddleCore i n) :
    (∀ y ∈ section9FiniteEndCube i n 0, y i ≤ x i) ∧
    section8OutwardSegment x i r ⊆ section9FiniteTube i n (-(5 : ℝ)/8) (3/8) ∧
    z ∉ section8OutwardSegment x i r := by
  have hnR : 16*((r : ℝ)+1) ≤ n := by exact_mod_cast hn
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hn16 : (16 : ℝ) ≤ n := by linarith
  have hxAxial := extension_face_axial_bounds i n hx
  have hxTrans := (Finset.mem_filter.mp hx).2.2
  have hwall : ∀ y ∈ section9FiniteEndCube i n 0, y i ≤ x i := by
    intro y hy
    have hyUpper := ((Finset.mem_filter.mp hy).2 i).2
    simp only [ite_true,sub_zero] at hyUpper
    have hylt : (y i : ℝ) < (x i : ℝ)+1 := hyUpper.trans_le hxAxial.2
    have hyInt : y i < x i+1 := by exact_mod_cast hylt
    omega
  refine ⟨hwall,?_,?_⟩
  · intro y hy
    obtain ⟨k,hkr,rfl⟩ := (section8_mem_outward_segment x y i r).mp hy
    have hkR : (k : ℝ) ≤ r := by exact_mod_cast hkr
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    apply (mem_section9FiniteTube i n (-(5 : ℝ)/8) (3/8)
      (by norm_num) (by norm_num) _).mpr
    refine ⟨?_,?_,?_⟩
    · simp only [Function.update_self,Int.cast_add,Int.cast_natCast]
      linarith [hxAxial.2]
    · simp only [Function.update_self,Int.cast_add,Int.cast_natCast]
      linarith [hxAxial.1]
    · intro j hji
      simp only [Function.update_of_ne hji]
      obtain ⟨hl,hu⟩ := hxTrans j hji
      constructor <;> linarith
  · intro hzI
    obtain ⟨k,hkr,hzk⟩ := (section8_mem_outward_segment x z i r).mp hzI
    have hkR : (k : ℝ) ≤ r := by exact_mod_cast hkr
    have hzShape := (Finset.mem_filter.mp hz).2 i
    simp only [ite_true] at hzShape
    have hzCoord : (z i : ℝ) = (x i : ℝ)+(k : ℝ) := by
      rw [hzk]
      simp only [Function.update_self,Int.cast_add,Int.cast_natCast]
    linarith [hzShape.1,hxAxial.1]

end NearCritical
