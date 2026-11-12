module

public import NearCritical.SplitCrossPlacementCount
public import NearCritical.SplitCrossPlacementPower

/-! The first moment of the terminal count is of order
at least `t^(40*d-2)` in the direct crossing construction. -/
@[expose] public section
noncomputable section

namespace NearCritical.SplitCrossDirect

open Section8 MeasureTheory

theorem crossing_placement_first_moment {d : ℕ} (hd : 7 ≤ d)
    (asymp : TwoPointAsymptotics d) (lower : RestrictedRectangleLowerInput d)
    {A B C c K : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hc : 0 < c) (hK : 0 < K)
    (arm : ∀ i : Fin d, HalfSpaceCriticalArmInput i A)
    (second : ∀ i : Fin d, SlabBoundarySecondMomentUpper i B)
    (panis : PanisHalfSpaceTwoPointUpper d C)
    (hslab : ∀ (i : Fin d) (h : ℕ), 1 ≤ h → ENNReal.ofReal (c / (h : ℝ)) ≤
      slabPioneerMass (criticalPoint d) i 0 (h : ℤ) 0 (h : ℤ))
    (hpioneer : ∀ (i : Fin d) (m : ℕ),
      halfSpacePioneerMass (criticalPoint d) i (m : ℤ) ≤ ENNReal.ofReal K) :
    ∃ a : ℝ, 0 < a ∧ ∃ T : ℕ, ∀ t ≥ T, 4096 ≤ t ∧
      ∀ (x : Vertex d), x ∈ centeredBox d ((t - 1) / 32) → ∀ axis : Fin d,
      a * (t : ℝ) ^ (2 * (20 * d - 1)) ≤
        ∫ θ, crossingPlacementCount t x axis θ ∂percolation d (criticalPoint d) := by
  have hd3 : 3 ≤ d := by omega
  have hL : 2 ≤ 4 * d := by omega
  obtain ⟨R, c₀, hc₀, T, hT⟩ :=
    uniform_face_assignment_moment_lower hd hd3 hL asymp lower hA hB hC hc hK arm second panis hslab hpioneer
  let m := (crossingPlacementMultiplicity d R : ℝ)
  let b := ((2048 * (d : ℝ))⁻¹ ^ d) ^ (20 * d - 1)
  have hm : 0 < m := Nat.cast_pos.mpr (crossingPlacementMultiplicity_pos d R)
  have hb : 0 < b := by
    have hd' : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
    dsimp [b]
    positivity
  refine ⟨c₀ * b / m, div_pos (mul_pos hc₀ hb) hm, T, ?_⟩
  intro t ht
  obtain ⟨ht4, hts, htl, hout, hunif⟩ := hT t ht
  refine ⟨ht4, ?_⟩
  intro x hx axis
  have hgap : 2 * ((R + 1 : ℕ) : ℝ) < (spineRadius (4 * d - 1) t : ℝ) := by
    have h : ((R + 1 : ℕ) : ℝ) ≤ ((R + 1 + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ (R + 1)
    linarith
  have h := crossing_placement_moment_lower ht4 hd3 hL x hx axis R hts htl hgap _ (hunif x hx axis)
  have hV := crossing_placement_scale_lower (by omega : 1 ≤ d) (by omega : 0 < t) x axis
  dsimp only at hV
  rw [crossingInteriorPlacement_card_index] at hV
  have hV' := mul_le_mul_of_nonneg_left hV hc₀.le
  rw [integral_crossingPlacementCount (by omega : 64 ≤ t) x hx axis (criticalPoint d)]
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hm).mpr
  rw [mul_comm _ m]
  exact (by
    calc
      _ = c₀ * (b * (t : ℝ) ^ (2 * (20 * d - 1))) := by ring
      _ ≤ _ := hV'
      _ = _ := by ring
      _ ≤ _ := h)

end NearCritical.SplitCrossDirect
