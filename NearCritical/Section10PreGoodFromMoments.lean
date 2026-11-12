module

public import NearCritical.Section10PreGoodEventually

/-! The pre-good hypothesis of the time-constant capstone, from the cited inputs
and ONE moment package.

`pregood_hypothesis_of_moments`: given `0 < q0 < 1` and a tolerance `δ > 0`
(those of `time_constant_sandwich_final`) and the moment package `hmom` at
tolerance `δ` (a heart ratio `cc <= 1/16`, constants `Cm Cp Cb` and a radius
`rstar` such that for every `typ` with that heart ratio, tolerance `δ` and radius
`>= rstar` the five energy-moment bounds hold on `typMark t 0` for all large
`t`), there are `typ`, `κ >= 1` with `κ^2 q0 < 1` and `t_0` with
`κ^{-1} <= P_pc[IsPreGoodCube typ t a]` for all `t >= t_0` and all `a`.

Choices: `η = (1 - q0)/2`, `κ = 2/(1 + q0)`, constants from `pregood_eventually`,
radius `r = max(1, rstar, ceil(3X/η))` with `X = 16 Cm Cp Cb/(δ^2 2 bL c1)`.
-/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open MeasureTheory
open scoped Classical

set_option maxHeartbeats 800000 in
theorem pregood_hypothesis_of_moments {d : ℕ} (hd : 9 ≤ d) (hA : TwoPointAsymptotics d)
    {c₀ K B Carm α A c : ℝ} (hc₀ : 0 < c₀) (hK : 0 ≤ K) (hB0 : 0 ≤ B) (hCarm : 0 < Carm)
    (hcross : SplitCrossInput d c₀)
    (htail : ∀ (N : ℕ) (x : Vertex d), x ∈ centeredBox d N →
      ∀ (f : Fin d × Bool) (T : ℝ), 0 < T →
        (percolation d (criticalPoint d)).real (Section7.farFaceEvent N x f T) ≤ K / T)
    (hBm : BoxFaceFirstMoment d B) (hsize : ClusterSizeInput d α A c) (ordinary : OrdinaryArmWindowInput d Carm)
    {a₁ a₂ a₃ : ℝ}
    (ha₁ : 0 ≤ a₁) (ha₂ : 0 ≤ a₂) (ha₃ : 0 ≤ a₃) (hsum : a₁ + a₂ + a₃ < 1)
    (hc : 0 < c) (ha₁' : 0 < a₁) (ha₂' : 0 < a₂) (ha₃' : 0 < a₃)
    {q0 δ : ℝ} (hq0 : 0 < q0) (hq1 : q0 < 1) (hδ0 : 0 < δ)
    (hmom : ∃ cc : ℝ, 0 < cc ∧ cc ≤ 1 / 16 ∧ ∃ Cm Cp Cb : ℝ, 0 ≤ Cm ∧ 0 ≤ Cp ∧ 0 ≤ Cb ∧
      ∃ rstar : ℕ, ∀ typ : TypicalParameters, typ.heartRatio = cc →
        typ.regularTolerance = δ → rstar ≤ typ.regularRadius →
        ∃ t₁ : ℕ, ∀ t : ℕ, t₁ ≤ t →
          (∀ x ∈ typMark t (0 : Vertex d),
      heartConditionalMean (criticalPoint d) (typicalCube t 0)
        (typicalHeart t 0 typ.heartRatio)
        (fun F => regularityEnergyOne F (typicalInnerCube t 0) typ.regularRadius x) x ≤
          typ.regularTolerance / 2) ∧
          (∀ x ∈ typMark t (0 : Vertex d),
      heartConditionalMean (criticalPoint d) (typicalCube t 0)
        (typicalHeart t 0 typ.heartRatio)
        (fun F => regularityEnergyTwo F (typicalBoundary t 0) typ.regularRadius x) x ≤
          typ.regularTolerance / 2) ∧
          (∀ x ∈ typMark t (0 : Vertex d),
      heartCenteredMoment (criticalPoint d) (typicalCube t 0)
        (typicalHeart t 0 typ.heartRatio)
        (fun F => regularityEnergyOne F (typicalInnerCube t 0) typ.regularRadius x) x +
      heartCenteredMoment (criticalPoint d) (typicalCube t 0)
        (typicalHeart t 0 typ.heartRatio)
        (fun F => regularityEnergyTwo F (typicalBoundary t 0) typ.regularRadius x) x ≤
      (Cm / (typ.regularRadius : ℝ) ^ (d - 6)) * (percolation d (criticalPoint d)).real
        {ω | x ∈ heartClusterUnion ω (typicalCube t 0) (typicalHeart t 0 typ.heartRatio)}) ∧
          (∀ x ∈ typMark t (0 : Vertex d), (percolation d (criticalPoint d)).real
        {ω | x ∈ heartClusterUnion ω (typicalCube t 0) (typicalHeart t 0 typ.heartRatio)} ≤
      Cp / (2 * (t : ℝ)) ^ 3) ∧
          (((typMark t (0 : Vertex d)).card : ℝ) ≤ Cb * (2 * (t : ℝ)) ^ (d - 1))) :
    ∃ (typ : TypicalParameters) (κ : ℝ) (t₀ : ℕ), 1 ≤ typ.regularRadius ∧
      typ.regularTolerance ≤ δ ∧ 0 < typ.boundaryLower ∧ 0 < typ.countLower ∧
      0 ≤ typ.boundaryUpper ∧ 0 ≤ typ.countUpper ∧ 0 ≤ typ.diameterUpper ∧
      1 ≤ κ ∧ κ ^ 2 * q0 < 1 ∧ ∀ t : ℕ, t₀ ≤ t → ∀ a : Vertex d,
      κ⁻¹ ≤ ∫ ω, (if IsPreGoodCube typ t a ω then (1:ℝ) else 0) ∂(percolation d (criticalPoint d)) := by
  obtain ⟨cc, hcc0, hcc, Cm, Cp, Cb, hCm, hCp, hCb, rstar, hpack⟩ := hmom
  obtain ⟨η, hηdef⟩ : ∃ η : ℝ, η = (1 - q0) / 2 := ⟨_, rfl⟩
  have hη : 0 < η := by rw [hηdef]; linarith
  obtain ⟨vL, vU, bL, bU, dU, cL, cU, c1, D, hvL, hbL, hcL, hbU, hcU, hdU, hc1, hD, t₀, ht₀, h⟩ :=
    pregood_eventually hd hA hc₀ hK hB0 hCarm hcross htail hBm hsize ordinary hcc0 hcc
      ha₁ ha₂ ha₃ hsum hc ha₁' ha₂' ha₃' hη
  obtain ⟨X, hX⟩ : ∃ X : ℝ, X = 16 * Cm * Cp * Cb / (δ ^ 2 * (2 * bL) * c1) := ⟨_, rfl⟩
  have hX0 : 0 ≤ X := by rw [hX]; positivity
  obtain ⟨r, hr⟩ : ∃ r : ℕ, r = max (max 1 rstar) ⌈3 * X / η⌉₊ := ⟨_, rfl⟩
  have hr1 : 1 ≤ r := by rw [hr]; exact le_trans (le_max_left _ _) (le_max_left _ _)
  have hrs : rstar ≤ r := by rw [hr]; exact le_trans (le_max_right _ _) (le_max_left _ _)
  have hrX : ⌈3 * X / η⌉₊ ≤ r := by rw [hr]; exact le_max_right _ _
  obtain ⟨typ, htyp⟩ : ∃ typ : TypicalParameters,
      typ = ⟨r, cc, δ, vL, vU, bL, bU, dU, cL, cU⟩ := ⟨_, rfl⟩
  have e_r : typ.regularRadius = r := by rw [htyp]
  have e_cc : typ.heartRatio = cc := by rw [htyp]
  have e_tol : typ.regularTolerance = δ := by rw [htyp]
  have e_vL : typ.volumeLower = vL := by rw [htyp]
  have e_vU : typ.volumeUpper = vU := by rw [htyp]
  have e_bL : typ.boundaryLower = bL := by rw [htyp]
  have e_bU : typ.boundaryUpper = bU := by rw [htyp]
  have e_dU : typ.diameterUpper = dU := by rw [htyp]
  have e_cL : typ.countLower = cL := by rw [htyp]
  have e_cU : typ.countUpper = cU := by rw [htyp]
  obtain ⟨t₁, hmomt⟩ := hpack typ e_cc e_tol (by rw [e_r]; exact hrs)
  have hq : (0:ℝ) < 1 + q0 := by linarith
  refine ⟨typ, 2 / (1 + q0), max t₀ t₁, by rw [e_r]; exact hr1, by rw [e_tol],
    by rw [e_bL]; exact hbL, by rw [e_cL]; exact hcL, by rw [e_bU]; exact hbU,
    by rw [e_cU]; exact hcU, by rw [e_dU]; exact hdU, ?_, ?_, ?_⟩
  · rw [le_div_iff₀ hq]
    linarith
  · rw [div_pow, div_mul_eq_mul_div, div_lt_one (by positivity)]
    nlinarith [sq_pos_of_pos (show 0 < 1 - q0 by linarith)]
  · intro t ht a
    obtain ⟨m1, m2, m3, m4, m5⟩ := hmomt t (le_trans (le_max_right _ _) ht)
    have hE : 16 * Cm * Cp * Cb / (typ.regularTolerance ^ 2 * (2 * bL) * c1 *
        (typ.regularRadius : ℝ) ^ (d - 6)) ≤ η / 3 := by
      rw [e_tol, e_r]
      have hrew : 16 * Cm * Cp * Cb / (δ ^ 2 * (2 * bL) * c1 * (r : ℝ) ^ (d - 6)) =
          X / (r : ℝ) ^ (d - 6) := by rw [hX, div_div]
      rw [hrew]
      have rR : (1:ℝ) ≤ (r : ℝ) := by exact_mod_cast hr1
      have hpow : (r : ℝ) ≤ (r : ℝ) ^ (d - 6) := le_self_pow₀ rR (by omega)
      have h3 : 3 * X / η ≤ (r : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hrX)
      rw [div_le_iff₀ (by positivity)]
      have a1 : η / 3 * (r : ℝ) ≤ η / 3 * (r : ℝ) ^ (d - 6) :=
        mul_le_mul_of_nonneg_left hpow (by positivity)
      have a3 : 3 * X ≤ (r : ℝ) * η := (div_le_iff₀ hη).mp h3
      linarith
    have hfin := h typ t ((t - 1) / 2) (le_trans (le_max_left _ _) ht) rfl e_cc e_vL e_vU e_bL
      e_bU e_dU e_cL e_cU Cm Cp Cb hCm hCp (by rw [e_r]; exact hr1) (by rw [e_tol]; exact hδ0)
      hE m1 m2 m3 m4 m5 a
    have hκ : (2 / (1 + q0))⁻¹ = 1 - η := by
      rw [inv_div, hηdef]
      ring
    rw [hκ]
    exact hfin

end NearCritical.Section10
