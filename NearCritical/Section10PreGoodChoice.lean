module

public import NearCritical.Section10PreGoodConstRelations

/-! Choice of the typical-cluster constants for prop.proba.pregood.

`exists_small_volume_const`: for `c, Carm, tau > 0` there is `x > 0` with
`exp(-c x^(-1/3)) Carm <= tau` (the small-volume fraction of eq.cluster_size can
be made as small as wanted).

`pregood_uniform_choice`: for failure fractions `a_i > 0` with sum `< 1` and any
`eta > 0` there are constants `vL vU bL bU dU cL cU c1 D` such that for every
`typ` carrying them (heart ratio `cc`; radius and tolerance free), every
`t >= 64` at which the eq.cluster_size threshold holds, `D/(N+1)^(d-8) <= eta/3`
and the regularity error is `<= eta/3`, the pre-good probability of every cube is
at least `1 - eta`, GIVEN the energy moments (`hm1 hm2 hvar hhit hcard`).

Order of choices as in the source: `dU, bU` large, `bL, vL` small, then
`vU = Cc/16`, `c1 = kappa_0/(Cc 4^(d-6))`, `cL = c1/2`, `cU = 27 Carm/(vL eta)`.
-/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open MeasureTheory
open scoped Classical

theorem exists_small_volume_const {c Carm τ lam0 : ℝ} (hc : 0 < c) (hCarm : 0 < Carm)
    (hτ : 0 < τ) (hl : 0 < lam0) :
    ∃ x : ℝ, 0 < x ∧ Real.exp (-c * x ^ (-(1 / 3 : ℝ))) * Carm ≤ τ ∧ x ≤ lam0 := by
  have hℓ : 0 < min 1 lam0 := lt_min one_pos hl
  have hcℓ : 0 ≤ c / min 1 lam0 := by positivity
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = Carm / τ + 1 + c / min 1 lam0 := ⟨_, rfl⟩
  have hM0 : 0 < M := by rw [hM]; positivity
  obtain ⟨y, hy⟩ : ∃ y : ℝ, y = c / M := ⟨_, rfl⟩
  have hy0 : 0 < y := by rw [hy]; positivity
  have hyℓ : y ≤ min 1 lam0 := by
    rw [hy, div_le_iff₀ hM0, hM]
    have h1 : 0 ≤ Carm / τ := by positivity
    have h2 : min 1 lam0 * (c / min 1 lam0) = c := by field_simp
    nlinarith [mul_nonneg hℓ.le (add_nonneg h1 zero_le_one)]
  have hy3 : y ^ 3 ≤ lam0 := by
    have hℓ1 : min 1 lam0 ≤ 1 := min_le_left _ _
    calc y ^ 3 ≤ (min 1 lam0) ^ 3 := pow_le_pow_left₀ hy0.le hyℓ 3
      _ ≤ min 1 lam0 := pow_le_of_le_one hℓ.le hℓ1 (by norm_num)
      _ ≤ lam0 := min_le_right _ _
  refine ⟨y ^ 3, by positivity, ?_, hy3⟩
  have e3 : ((3 : ℕ) : ℝ) * -(1 / 3 : ℝ) = -1 := by norm_num
  have hpow : (y ^ 3) ^ (-(1 / 3 : ℝ)) = y⁻¹ := by
    rw [← Real.rpow_natCast y 3, ← Real.rpow_mul hy0.le, e3, Real.rpow_neg_one]
  have harg : -c * (y ^ 3) ^ (-(1 / 3 : ℝ)) = -M := by
    rw [hpow, hy]
    field_simp
  rw [harg, Real.exp_neg, inv_mul_le_iff₀ (Real.exp_pos M)]
  have h1 := Real.add_one_le_exp M
  have h2 : Carm / τ ≤ Real.exp M := by rw [hM] at h1 ⊢; linarith
  calc Carm = Carm / τ * τ := by field_simp
    _ ≤ Real.exp M * τ := mul_le_mul_of_nonneg_right h2 hτ.le

set_option maxHeartbeats 800000 in
theorem pregood_uniform_choice {d : ℕ} (hd : 9 ≤ d) (hA : TwoPointAsymptotics d)
    {c₀ K B Carm α A c : ℝ} (hc₀ : 0 < c₀) (hK : 0 ≤ K) (hB0 : 0 ≤ B) (hCarm : 0 < Carm)
    (hcross : SplitCrossInput d c₀)
    (htail : ∀ (N : ℕ) (x : Vertex d), x ∈ centeredBox d N →
      ∀ (f : Fin d × Bool) (T : ℝ), 0 < T →
        (percolation d (criticalPoint d)).real (Section7.farFaceEvent N x f T) ≤ K / T)
    (hBm : BoxFaceFirstMoment d B) (hsize : ClusterSizeInput d α A c) (ordinary : OrdinaryArmWindowInput d Carm)
    {cc : ℝ} (hcc0 : 0 < cc) (hcc : cc ≤ 1 / 16) {a₁ a₂ a₃ : ℝ}
    (ha₁ : 0 ≤ a₁) (ha₂ : 0 ≤ a₂) (ha₃ : 0 ≤ a₃) (hsum : a₁ + a₂ + a₃ < 1)
    (hc : 0 < c) (ha₁' : 0 < a₁) (ha₂' : 0 < a₂) (ha₃' : 0 < a₃) {η : ℝ} (hη : 0 < η) :
    ∃ vL vU bL bU dU cL cU c1 D : ℝ, 0 < vL ∧ 0 < bL ∧ 0 < cL ∧ 0 ≤ bU ∧ 0 ≤ cU ∧ 0 ≤ dU ∧
      0 < c1 ∧ 0 < D ∧
      ∀ (typ : TypicalParameters) (t N : ℕ), max 64 hcross.threshold ≤ t → (t - 1) / 2 = N →
      typ.heartRatio = cc → typ.volumeLower = vL → typ.volumeUpper = vU →
      typ.boundaryLower = bL → typ.boundaryUpper = bU → typ.diameterUpper = dU →
      typ.countLower = cL → typ.countUpper = cU →
      ∀ (hlam : A * (Real.log ((N - (t - 1) / 32 : ℕ) : ℝ)) ^ α / ((N - (t - 1) / 32 : ℕ) : ℝ) ^ 3 <
        4096 * typ.volumeLower)
        (hD3 : D / (N + 1 : ℝ) ^ (d - 8) ≤ η / 3)
        (Cm Cp Cb : ℝ) (hCm : 0 ≤ Cm) (hCp : 0 ≤ Cp)
        (hr : 1 ≤ typ.regularRadius) (hδ : 0 < typ.regularTolerance)
        (hE : 16 * Cm * Cp * Cb / (typ.regularTolerance ^ 2 * (2 * bL) * c1 *
          (typ.regularRadius : ℝ) ^ (d - 6)) ≤ η / 3)
        (hm1 : ∀ x ∈ typMark t (0 : Vertex d),
      heartConditionalMean (criticalPoint d) (typicalCube t 0)
        (typicalHeart t 0 typ.heartRatio)
        (fun F => regularityEnergyOne F (typicalInnerCube t 0) typ.regularRadius x) x ≤
          typ.regularTolerance / 2)
    (hm2 : ∀ x ∈ typMark t (0 : Vertex d),
      heartConditionalMean (criticalPoint d) (typicalCube t 0)
        (typicalHeart t 0 typ.heartRatio)
        (fun F => regularityEnergyTwo F (typicalBoundary t 0) typ.regularRadius x) x ≤
          typ.regularTolerance / 2)
    (hvar : ∀ x ∈ typMark t (0 : Vertex d),
      heartCenteredMoment (criticalPoint d) (typicalCube t 0)
        (typicalHeart t 0 typ.heartRatio)
        (fun F => regularityEnergyOne F (typicalInnerCube t 0) typ.regularRadius x) x +
      heartCenteredMoment (criticalPoint d) (typicalCube t 0)
        (typicalHeart t 0 typ.heartRatio)
        (fun F => regularityEnergyTwo F (typicalBoundary t 0) typ.regularRadius x) x ≤
      (Cm / (typ.regularRadius : ℝ) ^ (d - 6)) * (percolation d (criticalPoint d)).real
        {ω | x ∈ heartClusterUnion ω (typicalCube t 0) (typicalHeart t 0 typ.heartRatio)})
    (hhit : ∀ x ∈ typMark t (0 : Vertex d), (percolation d (criticalPoint d)).real
        {ω | x ∈ heartClusterUnion ω (typicalCube t 0) (typicalHeart t 0 typ.heartRatio)} ≤
      Cp / (2 * (t : ℝ)) ^ 3)
    (hcard : ((typMark t (0 : Vertex d)).card : ℝ) ≤ Cb * (2 * (t : ℝ)) ^ (d - 1))
        (a : Vertex d),
      1 - η ≤ ∫ ω, (if IsPreGoodCube typ t a ω then (1:ℝ) else 0) ∂(percolation d (criticalPoint d)) := by
  have hdR : (0:ℝ) < (d : ℝ) := by exact_mod_cast (show 0 < d by omega)
  have hs : 0 < 1 - a₁ - a₂ - a₃ := by linarith
  have hδp : 0 < (1 - a₁ - a₂ - a₃) * c₀ / (4 * (64 * Carm)) :=
    div_pos (mul_pos hs hc₀) (by positivity)
  have hk0 : 0 < ((((1 - a₁ - a₂ - a₃) * c₀ / (4 * (64 * Carm))) * (c₀ / 4) * (cc / 4) ^ d / 4)) :=
    div_pos (mul_pos (mul_pos hδp (by positivity)) (by positivity)) (by norm_num)
  obtain ⟨Cc, D, hCc, hD, h⟩ := pregood_origin_const_relations hd hA hc₀ hK hB0 hCarm hcross htail
    hBm hsize ordinary hcc0 hcc ha₁ ha₂ ha₃ hsum
  have hCc' : Cc ≠ 0 := hCc.ne'
  obtain ⟨x, hx, hxε, hx1⟩ := exists_small_volume_const hc hCarm
    (show 0 < ((1 - a₁ - a₂ - a₃) * c₀ / (4 * (64 * Carm))) / 4 * (c₀ / 4) by positivity)
    hsize.cap_pos
  have hw1 : 0 < a₁ * (c₀ / 4) := by positivity
  have hw3 : 0 < 2 * a₃ * (c₀ / 4) := by positivity
  have hc1 : 0 < ((((1 - a₁ - a₂ - a₃) * c₀ / (4 * (64 * Carm))) * (c₀ / 4) * (cc / 4) ^ d / 4)) / (Cc * 4 ^ (d - 6)) := div_pos hk0 (by positivity)
  have hvL : 0 < x / 4096 := by positivity
  refine ⟨x / 4096, Cc / 16, a₂ * c₀ / (2048 * (d : ℝ) * Carm ^ 2),
    (d : ℝ) * B / (2 * a₃ * (c₀ / 4)) + 1, (d : ℝ) * K / (a₁ * (c₀ / 4)) + 1,
    ((((1 - a₁ - a₂ - a₃) * c₀ / (4 * (64 * Carm))) * (c₀ / 4) * (cc / 4) ^ d / 4)) / (Cc * 4 ^ (d - 6)) / 2, 27 * Carm / (x / 4096 * η),
    ((((1 - a₁ - a₂ - a₃) * c₀ / (4 * (64 * Carm))) * (c₀ / 4) * (cc / 4) ^ d / 4)) / (Cc * 4 ^ (d - 6)), D, hvL, by positivity, by positivity, by positivity,
    by positivity, by positivity, hc1, hD, ?_⟩
  intro typ t N htT hN hratio evL evU ebL ebU edU ecL ecU hlam hD3 Cm Cp Cb hCm hCp hr hδ hE
    hm1 hm2 hvar hhit hcard a
  have e4 : 4096 * typ.volumeLower = x := by rw [evL]; ring
  have hfin := h typ t N htT hN hratio (by rw [edU]; positivity) (by rw [ebU]; positivity)
    (by rw [ebL]; positivity) (by rw [evU]; linarith)
    (by
      rw [edU]
      have : a₁ * (c₀ / 4) * ((d : ℝ) * K / (a₁ * (c₀ / 4)) + 1) =
          (d : ℝ) * K + a₁ * (c₀ / 4) := by field_simp
      linarith)
    (by
      rw [ebU]
      have : 2 * a₃ * (c₀ / 4) * ((d : ℝ) * B / (2 * a₃ * (c₀ / 4)) + 1) =
          (d : ℝ) * B + 2 * a₃ * (c₀ / 4) := by field_simp
      linarith)
    (by
      rw [ebL]
      refine le_of_eq ?_
      field_simp)
    (by rw [evL]; exact hvL.le) (by rw [e4]; exact hx1) hlam (by rw [e4]; exact hxε)
    Cm Cp Cb (((((1 - a₁ - a₂ - a₃) * c₀ / (4 * (64 * Carm))) * (c₀ / 4) * (cc / 4) ^ d / 4)) / (Cc * 4 ^ (d - 6))) η hCm hCp hc1 hη hr hδ
    (by rw [ebL]; positivity) (by rw [evL]; exact hvL)
    (by rw [evL, ecU]) (by rw [ecL]; exact le_of_eq (by ring))
    (le_of_eq (by field_simp)) hm1 hm2 hvar hhit hcard a
  rw [ebL] at hfin
  linarith

end NearCritical.Section10
