module

public import NearCritical.SplitCrossFirstMoment
public import NearCritical.SplitCrossSecondMoment
public import NearCritical.SplitCrossDirectSecondMoment

/-! The first and second moments of the direct discrete count yield the
split-crossing probability used in Section 10. -/
@[expose] public section
noncomputable section

namespace NearCritical.SplitCrossDirect

open Section8 MeasureTheory
open scoped Classical

theorem splitCrossInput_direct {d : ℕ} (hd : 7 ≤ d)
    (asymp : TwoPointAsymptotics d) (lower : RestrictedRectangleLowerInput d)
    {A B C c K : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hc : 0 < c) (hK : 0 < K)
    (arm : ∀ i : Fin d, HalfSpaceCriticalArmInput i A)
    (second : ∀ i : Fin d, SlabBoundarySecondMomentUpper i B)
    (panis : PanisHalfSpaceTwoPointUpper d C)
    (hslab : ∀ (i : Fin d) (h : ℕ), 1 ≤ h → ENNReal.ofReal (c / (h : ℝ)) ≤
      slabPioneerMass (criticalPoint d) i 0 (h : ℤ) 0 (h : ℤ))
    (hpioneer : ∀ (i : Fin d) (m : ℕ),
      halfSpacePioneerMass (criticalPoint d) i (m : ℤ) ≤ ENNReal.ofReal K) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ Section10.SplitCrossInput d c₀ := by
  obtain ⟨a, ha, T, hT⟩ :=
    crossing_placement_first_moment hd asymp lower hA hB hC hc hK arm second panis hslab hpioneer
  obtain ⟨G, hG, green⟩ := criticalSupGreenUpper_of_asymptotics (by omega : 2 ≤ d) asymp
  obtain ⟨b, hb, hupper⟩ := crossing_placement_second_moment hd hG green hK
    (Section10.boxFaceFirstMoment_of_pioneerMass hK.le hpioneer)
  refine ⟨a ^ 2 / b, div_pos (by positivity) hb, T, ?_⟩
  intro t ht x hx
  obtain ⟨ht4, hlow⟩ := hT t ht
  let axis : Fin d := ⟨0, by omega⟩
  let p := criticalPoint d
  let μ := percolation d p
  let N := crossingPlacementCount t x axis
  let E := Section10.crossAll t t x
  let k := 2 * (20 * d - 1)
  let l := 2 * (40 * d - 1)
  have ht' : 0 < (t : ℝ) := by exact_mod_cast (show 0 < t by omega)
  have hN : Integrable N μ := by
    simpa only [pow_one] using crossingPlacementCount_integrable t x axis p 1
  have hN2 := crossingPlacementCount_integrable t x axis p 2
  have hsupport : {θ | N θ ≠ 0} ⊆ E := by
    intro θ hθ
    by_contra hn
    exact hθ (Set.indicator_of_notMem hn _)
  have hcs := sq_integral_le_integral_sq_mul_measure_ne_zero μ N
    (crossingPlacementCount_measurable t x axis) hN hN2
  have hp : μ.real {θ | N θ ≠ 0} ≤ μ.real E :=
    measureReal_mono hsupport (measure_ne_top _ _)
  have hfirst : a * (t : ℝ) ^ k ≤ ∫ θ, N θ ∂μ := hlow x hx axis
  have hsecond : (∫ θ, N θ ^ 2 ∂μ) ≤ b * (t : ℝ) ^ l :=
    hupper t (by omega) x hx axis
  have hbound : (a * (t : ℝ) ^ k) ^ 2 ≤ (b * (t : ℝ) ^ l) * μ.real E :=
    ((pow_le_pow_left₀ (by positivity) hfirst 2).trans hcs).trans
      (mul_le_mul hsecond hp measureReal_nonneg (by positivity))
  have hl : k * 2 + 2 = l := by dsimp [k, l]; omega
  change a ^ 2 / b / (t : ℝ) ^ 2 ≤ μ.real E
  rw [div_div]
  apply (div_le_iff₀ (mul_pos hb (pow_pos ht' _))).mpr
  refine le_of_mul_le_mul_right ?_ (pow_pos ht' l)
  calc
    _ = (a * (t : ℝ) ^ k) ^ 2 * (t : ℝ) ^ 2 := by
      rw [mul_pow, ← pow_mul, mul_assoc, ← pow_add, hl]
    _ ≤ ((b * (t : ℝ) ^ l) * μ.real E) * (t : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_right hbound (sq_nonneg _)
    _ = _ := by ring

end NearCritical.SplitCrossDirect
