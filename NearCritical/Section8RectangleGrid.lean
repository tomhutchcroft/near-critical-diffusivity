module
public import NearCritical.Section8RectangleLowerInput
public import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Finite fixed-shape rectangle grid for moving interior endpoint pairs. -/
@[expose] public section
noncomputable section
namespace NearCritical
open scoped Classical

/-- The 64 strictly positive aspect ratios used in the finite shape grid. -/
def section8RectangleGridWidth {d : ℕ} (κ : Fin d → Fin 64) (j : Fin d) : ℝ :=
  (((κ j).val : ℝ)+1)/64

/-- Every grid shape has positive aspect ratios at most one. -/
theorem section8_rectangle_grid_width_bounds {d : ℕ} (κ : Fin d → Fin 64) (j : Fin d) :
    0 < section8RectangleGridWidth κ j ∧ section8RectangleGridWidth κ j ≤ 1 := by
  have hk0 : (0 : ℝ) ≤ (κ j).val := Nat.cast_nonneg _
  have hk63 : ((κ j).val : ℝ) ≤ 63 := by
    exact_mod_cast (show (κ j).val ≤ 63 by have := (κ j).isLt; omega)
  dsimp [section8RectangleGridWidth]
  constructor <;> linarith

private theorem rectangle_grid_rounding (N D : ℝ) (hN : 0 < N) (hD : D ≤ 7*N/8) :
    ∃ k : Fin 64,
      max 0 D ≤ (((k.val : ℝ)+1)/64)*N ∧
      (((k.val : ℝ)+1)/64)*N ≤ max 0 D+N/32 ∧
      (((k.val : ℝ)+1)/64) ≤ 1 := by
  let q : ℝ := max 0 (D/N)
  have hq0 : 0 ≤ q := le_max_left _ _
  have hq7 : q ≤ 7/8 := max_le (by norm_num)
    ((div_le_iff₀ hN).mpr (by linarith))
  have hceil56 : Nat.ceil (64*q) ≤ 56 := Nat.ceil_le.mpr (by norm_num only [Nat.cast_ofNat]; linarith)
  let k : Fin 64 := ⟨Nat.ceil (64*q),by omega⟩
  have hkLow : 64*q ≤ (k.val : ℝ) := Nat.le_ceil _
  have hkHigh : (k.val : ℝ) ≤ 64*q+1 := (Nat.ceil_lt_add_one (by positivity : 0 ≤ 64*q)).le
  have hqN : q*N = max 0 D := by
    dsimp only [q]
    rw [max_mul_of_nonneg _ _ hN.le,zero_mul,div_mul_cancel₀ _ hN.ne']
  have hl := mul_le_mul_of_nonneg_right hkLow hN.le
  have hh := mul_le_mul_of_nonneg_right hkHigh hN.le
  have hk56 : (k.val : ℝ) ≤ 56 := by exact_mod_cast hceil56
  refine ⟨k,?_,?_,?_⟩
  · nlinarith only [hl,hqN,hN]
  · nlinarith only [hh,hqN]
  · linarith

private theorem rectangle_grid_coordinate (N A Z L U : ℝ) (hN : 0 < N)
    (hwidth : U-L ≤ 1)
    (hAlo : L*N+N/16 ≤ A) (hAhi : A ≤ U*N-N/16)
    (hZlo : L*N+N/16 ≤ Z) (hZhi : Z ≤ U*N-N/16) :
    ∃ k ℓ : Fin 64,
      (-((((k.val : ℝ)+1)/64))*N ≤ Z-A ∧ Z-A ≤ ((((ℓ.val : ℝ)+1)/64))*N) ∧
      (L*N < A-(65/64)*((((k.val : ℝ)+1)/64))*N) ∧
      (A+(65/64)*((((ℓ.val : ℝ)+1)/64))*N < U*N) ∧ |Z-A| ≤ N := by
  have hwN := mul_le_mul_of_nonneg_right hwidth hN.le
  have hgap₁ : A-Z ≤ 7*N/8 := by nlinarith only [hwN,hAhi,hZlo]
  have hgap₂ : Z-A ≤ 7*N/8 := by nlinarith only [hwN,hZhi,hAlo]
  obtain ⟨k,hkLow,hkHigh,hk1⟩ := rectangle_grid_rounding N (A-Z) hN hgap₁
  obtain ⟨ℓ,hℓLow,hℓHigh,hℓ1⟩ := rectangle_grid_rounding N (Z-A) hN hgap₂
  let α : ℝ := ((k.val : ℝ)+1)/64
  let β : ℝ := ((ℓ.val : ℝ)+1)/64
  have hαDil : (65/64)*α*N ≤ α*N+N/64 := by
    have hh := mul_le_mul_of_nonneg_right hk1 (by positivity : 0 ≤ N/64)
    dsimp only [α]
    nlinarith only [hh]
  have hβDil : (65/64)*β*N ≤ β*N+N/64 := by
    have hh := mul_le_mul_of_nonneg_right hℓ1 (by positivity : 0 ≤ N/64)
    dsimp only [β]
    nlinarith only [hh]
  refine ⟨k,ℓ,⟨?_,?_⟩,?_,?_,?_⟩
  · have hh := le_max_right 0 (A-Z)
    linarith only [hh,hkLow]
  · exact (le_max_right 0 (Z-A)).trans hℓLow
  · change L*N < A-(65/64)*α*N
    change α*N ≤ max 0 (A-Z)+N/32 at hkHigh
    rcases le_total Z A with hZA | hAZ
    · rw [max_eq_right (sub_nonneg.mpr hZA)] at hkHigh
      nlinarith only [hkHigh,hαDil,hZlo,hN]
    · rw [max_eq_left (sub_nonpos.mpr hAZ)] at hkHigh
      nlinarith only [hkHigh,hαDil,hAlo,hN]
  · change A+(65/64)*β*N < U*N
    change β*N ≤ max 0 (Z-A)+N/32 at hℓHigh
    rcases le_total A Z with hAZ | hZA
    · rw [max_eq_right (sub_nonneg.mpr hAZ)] at hℓHigh
      nlinarith only [hℓHigh,hβDil,hZhi,hN]
    · rw [max_eq_left (sub_nonpos.mpr hZA)] at hℓHigh
      nlinarith only [hℓHigh,hβDil,hAhi,hN]
  · exact abs_le.mpr ⟨by linarith only [hgap₁,hN],by linarith only [hgap₂,hN]⟩

/-- Every moving pair with n/16 coordinate margins and ambient widths at
most n belongs to one of finitely many fixed grid shapes. Its translated
65/64 dilation remains inside the OPEN ambient rectangle. -/
theorem section8_rectangle_grid_cover {d : ℕ} (n : ℕ) (hn : 1 ≤ n)
    (a z : Vertex d) (l u : Fin d → ℝ) (hwidth : ∀ j, u j-l j ≤ 1)
    (ha : ∀ j, l j*(n : ℝ)+(n : ℝ)/16 ≤ (a j : ℝ) ∧
      (a j : ℝ) ≤ u j*(n : ℝ)-(n : ℝ)/16)
    (hz : ∀ j, l j*(n : ℝ)+(n : ℝ)/16 ≤ (z j : ℝ) ∧
      (z j : ℝ) ≤ u j*(n : ℝ)-(n : ℝ)/16) :
    ∃ κ : (Fin d → Fin 64) × (Fin d → Fin 64),
      z-a ∈ section8Rectangle (section8RectangleGridWidth κ.1) (section8RectangleGridWidth κ.2) n ∧
      ((fun w : Vertex d => a+w) '' section8Rectangle
        (fun j => (65/64)*section8RectangleGridWidth κ.1 j)
        (fun j => (65/64)*section8RectangleGridWidth κ.2 j) n) ⊆
          {v | ∀ j, l j*(n : ℝ) < (v j : ℝ) ∧ (v j : ℝ) < u j*(n : ℝ)} ∧
      max 1 (latticeDistance 0 (z-a)) ≤ (n : ℝ) := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := zero_lt_one.trans_le hnR
  have hcoord (j : Fin d) := rectangle_grid_coordinate (n : ℝ) (a j : ℝ) (z j : ℝ)
    (l j) (u j) hn0 (hwidth j) (ha j).1 (ha j).2 (hz j).1 (hz j).2
  choose κ₁ κ₂ hκ using hcoord
  refine ⟨(κ₁,κ₂),?_,?_,?_⟩
  · intro j
    simpa only [section8RectangleGridWidth,Pi.sub_apply,Int.cast_sub] using (hκ j).1
  · rintro v ⟨w,hw,rfl⟩ j
    have hj := hw j
    have hlow := (hκ j).2.1
    have hhigh := (hκ j).2.2.1
    simp only [section8RectangleGridWidth] at hj
    change l j*(n : ℝ) < ((a+w) j : ℝ) ∧ ((a+w) j : ℝ) < u j*(n : ℝ)
    simp only [Pi.add_apply,Int.cast_add]
    constructor <;> nlinarith only [hj.1,hj.2,hlow,hhigh]
  · apply max_le hnR
    change dist (vertexReal (0 : Vertex d)) (vertexReal (z-a)) ≤ (n : ℝ)
    apply (dist_pi_le_iff hn0.le).mpr
    intro j
    simpa only [vertexReal,Pi.zero_apply,Int.cast_zero,Pi.sub_apply,Int.cast_sub,Real.dist_eq,zero_sub,abs_neg] using (hκ j).2.2.2

end NearCritical
