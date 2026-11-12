module

public import NearCritical.AppendixErrBoundaryUniform

/-! Discharge both Appendix A errors and obtain the source box lower bound. -/
@[expose] public section
noncomputable section
namespace NearCritical
open AppendixVariance MeasureTheory Section8
open scoped Classical ENNReal

/-- Both errors in the actual wider exploration box, with one coefficient. -/
theorem appendix_wide_box_error_bounds {d : ℕ} (hd : 7 ≤ d) {α : ℝ}
    (hα0 : 0 < α) (hα1 : α ≤ 1)
    (C A B : ℝ) (hC : 0 ≤ C) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (panis : PanisHalfSpaceTwoPointUpper d C)
    (arm : ∀ i : Fin d, HalfSpaceCriticalArmInput i A)
    (second : ∀ i : Fin d, SlabBoundarySecondMomentUpper i B) :
    ∀ m : ℕ, 2 ≤ m → AppendixWideBoxErrorBounds d α m := by
  cases d with
  | zero => omega
  | succ k =>
    intro m hm
    obtain ⟨K₁, hK₁, hcluster⟩ := appendix_wide_box_errCluster_bound hd hα0 hα1 m hm
      C A B hC hA hB panis arm second
    obtain ⟨K₂, hK₂, hboundary⟩ := appendix_wide_box_errBoundary_bound (k := k) (by omega)
      hα0 hα1 m hm C A B hC hA hB panis arm second
    refine ⟨K₁ + K₂, add_nonneg hK₁ hK₂, ?_⟩
    intro i n r x hn hr hlarge hxi hx h Q F hrh
    have hmon {a b : ℝ} (hab : a ≤ b) :
        a * (r : ℝ) ^ ((6 : ℝ) - (k + 1 : ℕ)) / (n : ℝ) ≤
          b * (r : ℝ) ^ ((6 : ℝ) - (k + 1 : ℕ)) / (n : ℝ) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hab (by positivity)) (by positivity)
    exact ⟨(hcluster i n r x hn hr hlarge hxi hx hrh).trans (hmon (by linarith)),
      (hboundary i n r x hn hr hlarge hxi hx hrh).trans (hmon (by linarith))⟩

/-- Source Appendix A box lower bound from the cited critical estimates and
the wider-prism proof. -/
theorem appendix_box_twopoint_lower_from_pioneers {d : ℕ} (hd : 7 ≤ d)
    (asymp : TwoPointAsymptotics d) (lower : RestrictedRectangleLowerInput d)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1)
    {A B C c K : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hc : 0 < c) (hK : 0 < K)
    (arm : ∀ i : Fin d, HalfSpaceCriticalArmInput i A)
    (second : ∀ i : Fin d, SlabBoundarySecondMomentUpper i B)
    (panis : PanisHalfSpaceTwoPointUpper d C)
    (hslab : ∀ (i : Fin d) (h : ℕ), 1 ≤ h → ENNReal.ofReal (c / (h : ℝ)) ≤
      slabPioneerMass (criticalPoint d) i 0 (h : ℤ) 0 (h : ℤ))
    (hpioneer : ∀ (i : Fin d) (m : ℕ),
      halfSpacePioneerMass (criticalPoint d) i (m : ℤ) ≤ ENNReal.ofReal K) :
    ∃ b : ℝ, 0 < b ∧ ∀ (i : Fin d) (n : ℕ) (x y : Vertex d), 1 ≤ n →
      (x i = -(n : ℤ) ∨ x i = (n : ℤ)) →
      (∀ j, j ≠ i → |(x j : ℝ)| ≤ (n : ℝ) - α * (n : ℝ)) →
      (∀ j, |(y j : ℝ)| ≤ (n : ℝ) - α * (n : ℝ)) →
      b / (n : ℝ) ^ (d - 1) ≤
        (percolation d (criticalPoint d)).real (connectionToSetEvent (centeredBox d n : Set (Vertex d)) x {y}) :=
  appendix_box_twopoint_lower_of_wide_errors hd asymp lower hα0 hα1 hA hB hC hc hK
    arm second panis hslab hpioneer
    (appendix_wide_box_error_bounds hd hα0 hα1 C A B hC hA hB panis arm second)

/-- The exact half-margin box premise of the marked moment theorem. -/
theorem marked_box_lower_from_pioneers (e : ℕ)
    (asymp : TwoPointAsymptotics (e + 7)) (lower : RestrictedRectangleLowerInput (e + 7))
    {A B C c K : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hc : 0 < c) (hK : 0 < K)
    (arm : ∀ i : Fin (e + 7), HalfSpaceCriticalArmInput i A)
    (second : ∀ i : Fin (e + 7), SlabBoundarySecondMomentUpper i B)
    (panis : PanisHalfSpaceTwoPointUpper (e + 7) C)
    (hslab : ∀ (i : Fin (e + 7)) (h : ℕ), 1 ≤ h → ENNReal.ofReal (c / (h : ℝ)) ≤
      slabPioneerMass (criticalPoint (e + 7)) i 0 (h : ℤ) 0 (h : ℤ))
    (hpioneer : ∀ (i : Fin (e + 7)) (m : ℕ),
      halfSpacePioneerMass (criticalPoint (e + 7)) i (m : ℤ) ≤ ENNReal.ofReal K) :
    ∃ b : ℝ, 0 < b ∧ ∀ (i : Fin (e + 7)) (R : ℕ) (x : Vertex (e + 7)), 1 ≤ R →
      (x i = -(R : ℤ) ∨ x i = (R : ℤ)) →
      (∀ j, j ≠ i → |(x j : ℝ)| ≤ (R : ℝ) - (1 / 2 : ℝ) * (R : ℝ)) →
      ∀ y ∈ centeredBox (e + 7) R, R ≤ 2 * (R - linfDist 0 y) →
        b / (R : ℝ) ^ (e + 6) ≤ (percolation (e + 7) (criticalPoint (e + 7))).real
          (connectionToSetEvent (centeredBox (e + 7) R : Set (Vertex (e + 7))) x {y}) := by
  obtain ⟨b, hb, hbox⟩ := appendix_box_twopoint_lower_from_pioneers (α := (1 : ℝ) / 2)
    (by omega : 7 ≤ e + 7) asymp lower (by norm_num) (by norm_num) hA hB hC hc hK
    arm second panis hslab hpioneer
  refine ⟨b, hb, ?_⟩
  intro i R x hR hface hx y _hy hdepth
  have hD : 2 * linfDist (0 : Vertex (e + 7)) y ≤ R := by omega
  have hD' : 2 * (linfDist (0 : Vertex (e + 7)) y : ℝ) ≤ R := by exact_mod_cast hD
  have hym (j : Fin (e + 7)) : |(y j : ℝ)| ≤ (R : ℝ) - (1 / 2 : ℝ) * (R : ℝ) := by
    have h := latticeDistance_coord_le y 0 j
    rw [← linfDist_cast_eq_latticeDistance, linfDist_comm y 0] at h
    simp only [Pi.zero_apply, Int.cast_zero, sub_zero] at h
    linarith
  simpa only [show e + 7 - 1 = e + 6 by omega] using hbox i R x y hR hface hx hym

end NearCritical
