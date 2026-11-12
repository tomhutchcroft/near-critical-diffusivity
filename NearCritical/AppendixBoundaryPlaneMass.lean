module
public import NearCritical.Section8BoundaryKernels
public import NearCritical.AppendixBoxFaceBudget

/-! Step R2 of the repaired route to eq.boundary_0_mean_segment (main.tex ~6315):
the total restricted connection mass from the origin to a separating plane at
sup-distance at least `R - h`, inside a domain contained in the half-space
`{w i₀ ≥ 0}`, is at most `|S| · C (1+h)/(R-h)^d`. The only input is the cited
Panis half-space two-point upper bound `PanisHalfSpaceTwoPointUpper`
(lem.halfspace_twopoint, Panis 2026 Thm 1.4). -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory
open scoped Classical
open NearCritical.Section8

theorem plane_mass_le_panis {d : ℕ} {C : ℝ} (hC : 0 ≤ C) (panis : PanisHalfSpaceTwoPointUpper d C)
    (i₀ j : Fin d) (h R : ℕ) (hRh : h < R)
    (Bx : Finset (Vertex d)) (hB : ∀ w ∈ Bx, 0 ≤ w i₀)
    (S : Finset (Vertex d))
    (hS : ∀ z ∈ S, 0 ≤ z i₀ ∧ z i₀ ≤ (h : ℤ) ∧ ((R : ℤ)-h) ≤ |z j|) :
    ∑ z ∈ S, (percolation d (criticalPoint d)).real
        (connectionToSetEvent ((Bx : Finset (Vertex d)) : Set (Vertex d)) 0 {z}) ≤
      (S.card : ℝ)*(C*(1+(h : ℝ))/(((R : ℝ)-h)^d)) := by
  have hRhR : (0 : ℝ) < (R : ℝ)-h := by
    have : (h : ℝ) < R := by exact_mod_cast hRh
    linarith
  let H := coordinateHalfSpace i₀ (0 : ℤ) true
  have hBH : ((Bx : Finset (Vertex d)) : Set (Vertex d)) ⊆ H := by
    intro w hw
    change 0 ≤ coordinateDepth i₀ 0 true w
    simp [coordinateDepth]
    exact_mod_cast hB w hw
  rw [← nsmul_eq_mul,← Finset.sum_const]
  apply Finset.sum_le_sum
  intro z hz
  obtain ⟨hz0,hzh,hzj⟩ := hS z hz
  have hzH : z ∈ H := by
    change 0 ≤ coordinateDepth i₀ 0 true z
    simp [coordinateDepth]
    exact_mod_cast hz0
  have h0H : (0 : Vertex d) ∈ H := by
    change 0 ≤ coordinateDepth i₀ 0 true 0
    simp [coordinateDepth]
  have hmono : connectionToSetEvent ((Bx : Finset (Vertex d)) : Set (Vertex d)) 0 {z} ⊆
      connectionToSetEvent H 0 {z} := by
    rintro ω ⟨haD,v,hvz,hvD,hav⟩
    refine ⟨hBH haD,v,hvz,hBH hvD,hav.mono ?_⟩
    exact fun _ _ h => ⟨h.1,hBH h.2.1,hBH h.2.2⟩
  have hp := panis i₀ 0 true 0 z h0H hzH
  let L := latticeDistance (0 : Vertex d) z
  have hL0 : 0 ≤ L := latticeDistance_nonneg _ _
  have hLR : (R : ℝ)-h ≤ L := by
    have hc := latticeDistance_coord_le (0 : Vertex d) z j
    have hzjR : ((R : ℝ)-h) ≤ |(z j : ℝ)| := by
      have := hzj
      have h' : (((R : ℤ)-h : ℤ) : ℝ) ≤ ((|z j| : ℤ) : ℝ) := by exact_mod_cast this
      push_cast at h'
      exact h'
    have : |((0 : Vertex d) j : ℝ)-(z j : ℝ)| = |(z j : ℝ)| := by
      simp [abs_neg]
    show (R : ℝ)-h ≤ latticeDistance (0 : Vertex d) z
    linarith
  have hdep0 : coordinateDepth i₀ 0 true (0 : Vertex d) = 0 := by simp [coordinateDepth]
  have hdepz : coordinateDepth i₀ 0 true z ≤ (h : ℝ) := by
    simp [coordinateDepth]
    exact_mod_cast hzh
  have hdepz0 : 0 ≤ coordinateDepth i₀ 0 true z := hzH
  have hnum : (1+min (coordinateDepth i₀ 0 true (0 : Vertex d)) L)*
      (1+min (coordinateDepth i₀ 0 true z) L) ≤ 1+(h : ℝ) := by
    rw [hdep0,min_eq_left hL0,add_zero,one_mul]
    have := min_le_left (coordinateDepth i₀ 0 true z) L
    linarith
  have hden : ((R : ℝ)-h)^d ≤ 1+L^d := by
    have := pow_le_pow_left₀ hRhR.le hLR d
    linarith
  have hdenpos : (0 : ℝ) < ((R : ℝ)-h)^d := pow_pos hRhR d
  have hnum0 : 0 ≤ (1+min (coordinateDepth i₀ 0 true (0 : Vertex d)) L)*
      (1+min (coordinateDepth i₀ 0 true z) L) := by
    rw [hdep0,min_eq_left hL0]
    have := le_min hdepz0 hL0
    nlinarith
  calc (percolation d (criticalPoint d)).real
        (connectionToSetEvent ((Bx : Finset (Vertex d)) : Set (Vertex d)) 0 {z})
      ≤ (percolation d (criticalPoint d)).real (connectionToSetEvent H 0 {z}) :=
        measureReal_mono hmono (measure_ne_top _ _)
    _ ≤ C*((1+min (coordinateDepth i₀ 0 true (0 : Vertex d)) L)*
          (1+min (coordinateDepth i₀ 0 true z) L))/(1+L^d) := hp
    _ ≤ C*(1+(h : ℝ))/(1+L^d) := by
        refine div_le_div_of_nonneg_right ?_ ?_
        · exact mul_le_mul_of_nonneg_left hnum hC
        · have := pow_nonneg hL0 d
          linarith
    _ ≤ C*(1+(h : ℝ))/(((R : ℝ)-h)^d) :=
        div_le_div_of_nonneg_left (mul_nonneg hC (by positivity)) hdenpos hden

end NearCritical
