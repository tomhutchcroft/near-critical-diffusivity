module

public import NearCritical.Section10PreGoodChoice
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! prop.proba.pregood for all large scales, given the energy moments.

`eventually_cluster_threshold`: `A (log m)^α / m^3 < x` for all large `m`
(the eq.cluster_size threshold is eventually satisfied by any fixed `x > 0`).

`pregood_eventually`: `pregood_uniform_choice` with the threshold and the
candidate-count error `D/(N+1)^(d-8) <= eta/3` discharged for `t >= t_0`.
Remaining hypotheses at each scale: the regularity error `<= eta/3` and the
energy moments (`hm1 hm2 hvar hhit hcard`).
-/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open MeasureTheory
open scoped Classical

theorem eventually_cluster_threshold (A α : ℝ) {x : ℝ} (hx : 0 < x) :
    ∃ M : ℕ, ∀ m : ℕ, M ≤ m → A * (Real.log (m : ℝ)) ^ α / (m : ℝ) ^ 3 < x := by
  have ho := isLittleO_log_rpow_rpow_atTop α (show (0:ℝ) < ((3 : ℕ) : ℝ) by norm_num)
  have ht := (ho.tendsto_div_nhds_zero).const_mul A
  rw [mul_zero] at ht
  obtain ⟨Y, hY⟩ := Filter.eventually_atTop.mp (ht.eventually (gt_mem_nhds hx))
  refine ⟨⌈Y⌉₊, fun m hm => ?_⟩
  have h := hY (m : ℝ) (Nat.ceil_le.mp hm)
  rw [Real.rpow_natCast] at h
  rwa [mul_div_assoc]

set_option maxHeartbeats 800000 in
theorem pregood_eventually {d : ℕ} (hd : 9 ≤ d) (hA : TwoPointAsymptotics d)
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
      0 < c1 ∧ 0 < D ∧ ∃ t₀ : ℕ, 64 ≤ t₀ ∧
      ∀ (typ : TypicalParameters) (t N : ℕ), t₀ ≤ t → (t - 1) / 2 = N →
      typ.heartRatio = cc → typ.volumeLower = vL → typ.volumeUpper = vU →
      typ.boundaryLower = bL → typ.boundaryUpper = bU → typ.diameterUpper = dU →
      typ.countLower = cL → typ.countUpper = cU →
      ∀ (Cm Cp Cb : ℝ) (hCm : 0 ≤ Cm) (hCp : 0 ≤ Cp)
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
  obtain ⟨vL, vU, bL, bU, dU, cL, cU, c1, D, hvL, hbL, hcL, hbU, hcU, hdU, hc1, hD, h⟩ :=
    pregood_uniform_choice hd hA hc₀ hK hB0 hCarm hcross htail hBm hsize ordinary hcc0 hcc
      ha₁ ha₂ ha₃ hsum hc ha₁' ha₂' ha₃' hη
  obtain ⟨M, hM⟩ := eventually_cluster_threshold A α (show 0 < 4096 * vL by positivity)
  refine ⟨vL, vU, bL, bU, dU, cL, cU, c1, D, hvL, hbL, hcL, hbU, hcU, hdU, hc1, hD,
    max (max 64 hcross.threshold) (max (4 * M) ⌈6 * D / η⌉₊),
      (le_max_left _ _).trans (le_max_left _ _), ?_⟩
  intro typ t N ht hN hratio evL evU ebL ebU edU ecL ecU Cm Cp Cb hCm hCp hr hδ hE
    hm1 hm2 hvar hhit hcard a
  have htCross : max 64 hcross.threshold ≤ t := (le_max_left _ _).trans ht
  have ht64 : 64 ≤ t := (le_max_left _ _).trans htCross
  have htM : 4 * M ≤ t := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) ht
  have htD : ⌈6 * D / η⌉₊ ≤ t := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) ht
  refine h typ t N htCross hN hratio evL evU ebL ebU edU ecL ecU ?_ ?_ Cm Cp Cb hCm hCp hr hδ hE
    hm1 hm2 hvar hhit hcard a
  · rw [evL]
    exact hM (N - (t - 1) / 32) (by omega)
  · have h6 : 6 * D / η ≤ (t : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast htD)
    have hN1 : (t : ℝ) ≤ 2 * ((N : ℝ) + 1) := by
      exact_mod_cast (show t ≤ 2 * (N + 1) by omega)
    have hN0 : (1:ℝ) ≤ (N : ℝ) + 1 := by
      have : (0:ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
      linarith
    have hpow : (N : ℝ) + 1 ≤ ((N : ℝ) + 1) ^ (d - 8) := le_self_pow₀ hN0 (by omega)
    rw [div_le_iff₀ (by positivity)]
    have a1 : η / 3 * ((N : ℝ) + 1) ≤ η / 3 * ((N : ℝ) + 1) ^ (d - 8) :=
      mul_le_mul_of_nonneg_left hpow (by positivity)
    have a2 : η * (t : ℝ) ≤ η * (2 * ((N : ℝ) + 1)) := mul_le_mul_of_nonneg_left hN1 hη.le
    have a3 : 6 * D ≤ (t : ℝ) * η := (div_le_iff₀ hη).mp h6
    linarith

end NearCritical.Section10
