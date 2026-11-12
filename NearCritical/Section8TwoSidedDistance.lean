module
public import NearCritical.Section8TwoSidedScale

/-! Actual-distance two-sided estimate, including the clipped small-distance range. -/
@[expose] public section
noncomputable section
namespace NearCritical.Section8
open Set MeasureTheory
open scoped Classical

private theorem half_floor_scale (R : ℝ) (hR : 2 ≤ R) :
    1 ≤ ⌊R/2⌋₊ ∧ 2*(⌊R/2⌋₊ : ℝ) ≤ R ∧ R ≤ 4*(⌊R/2⌋₊ : ℝ) := by
  have hn : 1 ≤ ⌊R/2⌋₊ := (Nat.one_le_floor_iff _).mpr (by linarith)
  have hnR : (1 : ℝ) ≤ (⌊R/2⌋₊ : ℝ) := by exact_mod_cast hn
  have hlo := Nat.floor_le (by linarith : (0 : ℝ) ≤ R/2)
  have hhi := Nat.lt_floor_add_one (R/2)
  exact ⟨hn,by linarith,by linarith⟩

private theorem inverse_scale_power_le {n d : ℕ} (R : ℝ)
    (hn : 0 < (n : ℝ)) (hR : 0 < R) (hscale : R ≤ 4*(n : ℝ)) :
    (n : ℝ)^(-(d : ℝ)) ≤ (4 : ℝ)^d * R^(-(d : ℝ)) := by
  have hp : R^d ≤ (4 : ℝ)^d*(n : ℝ)^d := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ hR.le hscale d
  have hdiv : (1 : ℝ)/(n : ℝ)^d ≤ (4 : ℝ)^d/R^d := by
    apply (div_le_div_iff₀ (pow_pos hn d) (pow_pos hR d)).mpr
    simpa only [one_mul] using hp
  simpa only [Real.rpow_neg hn.le,Real.rpow_natCast,Real.rpow_neg hR.le,
    one_div,div_eq_mul_inv,one_mul] using hdiv

/-- Both endpoint-depth gains for the actual finite-domain connection.
The clipped kernel covers x=y as well as every off-diagonal distance. -/
theorem two_halfspaces_connection_le_distance {d : ℕ} (hd : 1 ≤ d)
    (C A B : ℝ) (hC : 0 ≤ C) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (panis : PanisHalfSpaceTwoPointUpper d C)
    (arm : ∀ i : Fin d, HalfSpaceCriticalArmInput i A)
    (second : ∀ i : Fin d, SlabBoundarySecondMomentUpper i B)
    (Q : Finset (Vertex d)) (x y : Vertex d) (hx : x ∈ Q) (hy : y ∈ Q)
    (ix iy : Fin d) (wx wy : ℤ) (sx sy : Bool)
    (hDx : (Q : Set (Vertex d)) ⊆ coordinateHalfSpace ix wx sx)
    (hDy : (Q : Set (Vertex d)) ⊆ coordinateHalfSpace iy wy sy) :
    (percolation d (criticalPoint d)).real (connectionToSetEvent (Q : Set (Vertex d)) x {y}) ≤
      (4*C+((2*(d : ℝ))*(4*C*(A+B)*(9 : ℝ)^(d-1))*(2*C))*(4 : ℝ)^d)*
        (1+coordinateDepth ix wx sx x)*(1+coordinateDepth iy wy sy y)*
        (max 1 (latticeDistance x y))^(-(d : ℝ)) := by
  let R := latticeDistance x y
  let M := max 1 R
  let a := 1+coordinateDepth ix wx sx x
  let b := 1+coordinateDepth iy wy sy y
  let K := (2*(d : ℝ))*(4*C*(A+B)*(9 : ℝ)^(d-1))*(2*C)
  have ha : 1 ≤ a := by
    have h : 0 ≤ coordinateDepth ix wx sx x := hDx hx
    dsimp [a]
    linarith
  have hb : 1 ≤ b := by
    have h : 0 ≤ coordinateDepth iy wy sy y := hDy hy
    dsimp [b]
    linarith
  have ha0 : 0 ≤ a := by linarith
  have hb0 : 0 ≤ b := by linarith
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hpow : 0 ≤ M^(-(d : ℝ)) := Real.rpow_nonneg hMpos.le _
  change _ ≤ (4*C+K*(4 : ℝ)^d)*a*b*M^(-(d : ℝ))
  by_cases hR : 2 ≤ R
  · let n := ⌊R/2⌋₊
    obtain ⟨hn,hsep,hscale⟩ := half_floor_scale R hR
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
    have hRpos : 0 < R := by linarith
    have hMR : M = R := max_eq_right (by linarith)
    have hp := two_halfspaces_connection_le_scale hd hn C A B hC hA hB panis arm second
      Q x y hx hy ix iy wx wy sx sy hDx hDy hsep
    have hdecay := inverse_scale_power_le (d := d) R hnpos hRpos hscale
    change _ ≤ K*a*b*(n : ℝ)^(-(d : ℝ)) at hp
    rw [hMR]
    calc
      _ ≤ K*a*b*(n : ℝ)^(-(d : ℝ)) := hp
      _ ≤ K*a*b*((4 : ℝ)^d*R^(-(d : ℝ))) :=
        mul_le_mul_of_nonneg_left hdecay (by positivity)
      _ = (K*(4 : ℝ)^d)*a*b*R^(-(d : ℝ)) := by ring
      _ ≤ (4*C+K*(4 : ℝ)^d)*a*b*R^(-(d : ℝ)) := by
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hRpos.le _)
        apply mul_le_mul_of_nonneg_right _ hb0
        apply mul_le_mul_of_nonneg_right _ ha0
        linarith
  · have hM2 : M ≤ 2 := max_le (by norm_num) (by linarith)
    have hp := restricted_halfSpace_one_sided C hC panis ix wx sx
      (Q : Set (Vertex d)) hDx x y hx hy
    have hpower : M^((1 : ℝ)-(d : ℝ)) = M*M^(-(d : ℝ)) := by
      rw [show (1 : ℝ)-(d : ℝ) = 1+(-(d : ℝ)) by ring,
        Real.rpow_add hMpos,Real.rpow_one]
    change _ ≤ (2*C)*a*M^((1 : ℝ)-(d : ℝ)) at hp
    have hc : 2*C*M ≤ 4*C*b := by
      nlinarith [mul_nonneg hC (sub_nonneg.mpr hM2),
        mul_nonneg hC (sub_nonneg.mpr hb)]
    calc
      _ ≤ (2*C)*a*M^((1 : ℝ)-(d : ℝ)) := hp
      _ = (2*C*M)*a*M^(-(d : ℝ)) := by rw [hpower]; ring
      _ ≤ (4*C*b)*a*M^(-(d : ℝ)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc ha0) hpow
      _ = (4*C)*a*b*M^(-(d : ℝ)) := by ring
      _ ≤ (4*C+K*(4 : ℝ)^d)*a*b*M^(-(d : ℝ)) := by
        apply mul_le_mul_of_nonneg_right _ hpow
        apply mul_le_mul_of_nonneg_right _ hb0
        apply mul_le_mul_of_nonneg_right _ ha0
        exact le_add_of_nonneg_right (by positivity)

end NearCritical.Section8
