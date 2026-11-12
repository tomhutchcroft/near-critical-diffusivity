module

public import NearCritical.Section10PreGoodOrigin

/-! `pregood_origin_of_moments` with its three scale-dependent relations
replaced by relations between constants (valid for all `t >= 64`):

* volume: `Cc <= 16 volumeUpper` (since `N + 1 <= t`);
* lower split-face failure: `2048 d boundaryLower Carm^2 <= a_2 c_0`
  (floor bound and `t <= 8 (t/4)`);
* rate: `c1 4^(d-6) <= kappa_0 / Cc` (since `2t <= 4 (N+1)`).

The eq.cluster_size threshold (`A log^α m / m^3 < 4096 volumeLower`) is the only
remaining scale-dependent non-moment hypothesis.
-/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open MeasureTheory
open scoped Classical

set_option maxHeartbeats 800000 in
theorem pregood_origin_const_relations {d : ℕ} (hd : 9 ≤ d) (hA : TwoPointAsymptotics d)
    {c₀ K B Carm α A c : ℝ} (hc₀ : 0 < c₀) (hK : 0 ≤ K) (hB0 : 0 ≤ B) (hCarm : 0 < Carm)
    (hcross : SplitCrossInput d c₀)
    (htail : ∀ (N : ℕ) (x : Vertex d), x ∈ centeredBox d N →
      ∀ (f : Fin d × Bool) (T : ℝ), 0 < T →
        (percolation d (criticalPoint d)).real (Section7.farFaceEvent N x f T) ≤ K / T)
    (hBm : BoxFaceFirstMoment d B) (hsize : ClusterSizeInput d α A c) (ordinary : OrdinaryArmWindowInput d Carm)
    {cc : ℝ} (hcc0 : 0 < cc) (hcc : cc ≤ 1 / 16) {a₁ a₂ a₃ : ℝ}
    (ha₁ : 0 ≤ a₁) (ha₂ : 0 ≤ a₂) (ha₃ : 0 ≤ a₃) (hsum : a₁ + a₂ + a₃ < 1) :
    ∃ Cc D : ℝ, 0 < Cc ∧ 0 < D ∧
      ∀ (typ : TypicalParameters) (t N : ℕ), max 64 hcross.threshold ≤ t → (t - 1) / 2 = N →
      typ.heartRatio = cc → 0 < typ.diameterUpper → 0 < typ.boundaryUpper →
      0 ≤ typ.boundaryLower →
      Cc ≤ 16 * typ.volumeUpper →
      (d : ℝ) * K ≤ a₁ * (c₀ / 4) * typ.diameterUpper →
      (d : ℝ) * B ≤ 2 * a₃ * (c₀ / 4) * typ.boundaryUpper →
      2048 * (d : ℝ) * typ.boundaryLower * Carm ^ 2 ≤ a₂ * c₀ →
      0 ≤ typ.volumeLower →
      4096 * typ.volumeLower ≤ hsize.cap →
      A * (Real.log ((N - (t - 1) / 32 : ℕ) : ℝ)) ^ α / ((N - (t - 1) / 32 : ℕ) : ℝ) ^ 3 <
        4096 * typ.volumeLower →
      Real.exp (-c * (4096 * typ.volumeLower) ^ (-(1 / 3 : ℝ))) * Carm ≤
        (((1 - a₁ - a₂ - a₃) * c₀ / (4 * (64 * Carm))) / 4) * (c₀ / 4) →
      ∀ (Cm Cp Cb c1 ε : ℝ) (hCm : 0 ≤ Cm) (hCp : 0 ≤ Cp) (hc1 : 0 < c1) (hε0 : 0 < ε)
        (hr : 1 ≤ typ.regularRadius) (hδ : 0 < typ.regularTolerance)
        (hbLpos : 0 < typ.boundaryLower) (hvLpos : 0 < typ.volumeLower)
        (hup : 27 * Carm / (typ.volumeLower * ε) ≤ typ.countUpper)
        (hcount : typ.countLower * (2 * (t : ℝ)) ^ (d - 6) ≤ c1 * (2 * (t : ℝ)) ^ (d - 6) / 2)
        (hrate : c1 * 4 ^ (d - 6) ≤ (((1 - a₁ - a₂ - a₃) * c₀ / (4 * (64 * Carm))) * (c₀ / 4) * (cc / 4) ^ d / 4) / Cc)
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
      1 - (D / (N + 1 : ℝ) ^ (d - 8) + 16 * Cm * Cp * Cb / (typ.regularTolerance ^ 2 *
          (2 * typ.boundaryLower) * c1 * (typ.regularRadius : ℝ) ^ (d - 6))) - ε / 3 ≤
        ∫ ω, (if IsPreGoodCube typ t a ω then (1:ℝ) else 0) ∂(percolation d (criticalPoint d)) := by
  obtain ⟨Cc, D, hCc, hD, h⟩ := pregood_origin_of_moments hd hA hc₀ hK hB0 hCarm hcross htail hBm
    hsize ordinary hcc0 hcc ha₁ ha₂ ha₃ hsum
  refine ⟨Cc, D, hCc, hD, ?_⟩
  intro typ t N htT hN hratio hdU hbU hbL hvol hrel1 hrel3 hrel2 hvL hv1 hlam hε Cm Cp Cb c1 ε hCm hCp
    hc1 hε0 hr hδ hbLpos hvLpos hup hcount hrate hm1 hm2 hvar hhit hcard a
  have ht : 64 ≤ t := (le_max_left _ _).trans htT
  have hT : (0:ℝ) < (t : ℝ) := by exact_mod_cast (show 0 < t by omega)
  have hNt : (N : ℝ) + 1 ≤ (t : ℝ) := by exact_mod_cast (show N + 1 ≤ t by omega)
  have htN : 2 * (t : ℝ) ≤ 4 * ((N : ℝ) + 1) := by
    exact_mod_cast (show 2 * t ≤ 4 * (N + 1) by omega)
  have hvol' : Cc * (N + 1 : ℝ) ^ 4 ≤ typ.volumeUpper * (2 * (t : ℝ)) ^ 4 := by
    have h4 : ((N : ℝ) + 1) ^ 4 ≤ (t : ℝ) ^ 4 := pow_le_pow_left₀ (by positivity) hNt 4
    calc Cc * (N + 1 : ℝ) ^ 4 ≤ Cc * (t : ℝ) ^ 4 := mul_le_mul_of_nonneg_left h4 hCc.le
      _ ≤ 16 * typ.volumeUpper * (t : ℝ) ^ 4 :=
          mul_le_mul_of_nonneg_right hvol (by positivity)
      _ = typ.volumeUpper * (2 * (t : ℝ)) ^ 4 := by ring
  have hrate' : c1 * (2 * (t : ℝ)) ^ (d - 6) ≤ ((((1 - a₁ - a₂ - a₃) * c₀ / (4 * (64 * Carm))) * (c₀ / 4) * (cc / 4) ^ d / 4) / Cc) * (N + 1 : ℝ) ^ (d - 6) := by
    have hp : (2 * (t : ℝ)) ^ (d - 6) ≤ (4 * ((N : ℝ) + 1)) ^ (d - 6) :=
      pow_le_pow_left₀ (by positivity) htN _
    calc c1 * (2 * (t : ℝ)) ^ (d - 6) ≤ c1 * (4 * ((N : ℝ) + 1)) ^ (d - 6) :=
          mul_le_mul_of_nonneg_left hp hc1.le
      _ = c1 * 4 ^ (d - 6) * ((N : ℝ) + 1) ^ (d - 6) := by rw [mul_pow]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hrate (by positivity)
  have hrel2' : 4 * (d : ℝ) * ((⌊2 * (typ.boundaryLower * (2 * (t : ℝ)) ^ 2)⌋₊ : ℝ) *
      (Carm / (t : ℝ) ^ 2) * (Carm / ((t / 4 : ℕ) : ℝ) ^ 2)) ≤ a₂ * (c₀ / (t : ℝ) ^ 2) := by
    obtain ⟨n4, hn4⟩ : ∃ n, t / 4 = n := ⟨_, rfl⟩
    rw [hn4]
    have hn0 : (0:ℝ) < (n4 : ℝ) := by exact_mod_cast (show 0 < n4 by omega)
    have htn : (t : ℝ) ≤ 8 * (n4 : ℝ) := by exact_mod_cast (show t ≤ 8 * n4 by omega)
    have hA : ((⌊2 * (typ.boundaryLower * (2 * (t : ℝ)) ^ 2)⌋₊ : ℝ)) ≤
        8 * typ.boundaryLower * (t : ℝ) ^ 2 :=
      (Nat.floor_le (by positivity)).trans_eq (by ring)
    have h1 : Carm / (n4 : ℝ) ^ 2 ≤ 64 * Carm / (t : ℝ) ^ 2 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have hsq8 : (t : ℝ) ^ 2 ≤ (8 * (n4 : ℝ)) ^ 2 := pow_le_pow_left₀ hT.le htn 2
      have hsq : (t : ℝ) ^ 2 ≤ 64 * (n4 : ℝ) ^ 2 := hsq8.trans_eq (by ring)
      have hmul := mul_le_mul_of_nonneg_left hsq hCarm.le
      calc Carm * (t : ℝ) ^ 2 ≤ Carm * (64 * (n4 : ℝ) ^ 2) := hmul
        _ = 64 * Carm * (n4 : ℝ) ^ 2 := by ring
    have h0 : 0 ≤ Carm / (t : ℝ) ^ 2 := by positivity
    have h0' : 0 ≤ Carm / (n4 : ℝ) ^ 2 := by positivity
    have hprod : (⌊2 * (typ.boundaryLower * (2 * (t : ℝ)) ^ 2)⌋₊ : ℝ) *
        (Carm / (t : ℝ) ^ 2) * (Carm / (n4 : ℝ) ^ 2) ≤
        (8 * typ.boundaryLower * (t : ℝ) ^ 2) * (Carm / (t : ℝ) ^ 2) *
          (64 * Carm / (t : ℝ) ^ 2) :=
      mul_le_mul (mul_le_mul_of_nonneg_right hA h0) h1 h0'
        (mul_nonneg (by positivity) h0)
    have hd0 : (0:ℝ) ≤ 4 * (d : ℝ) := by positivity
    calc _ ≤ 4 * (d : ℝ) * ((8 * typ.boundaryLower * (t : ℝ) ^ 2) * (Carm / (t : ℝ) ^ 2) *
          (64 * Carm / (t : ℝ) ^ 2)) := mul_le_mul_of_nonneg_left hprod hd0
      _ = (2048 * (d : ℝ) * typ.boundaryLower * Carm ^ 2) / (t : ℝ) ^ 2 := by
          field_simp
          ring
      _ ≤ (a₂ * c₀) / (t : ℝ) ^ 2 := div_le_div_of_nonneg_right hrel2 (sq_nonneg _)
      _ = _ := by ring
  exact h typ t N htT hN hratio hdU hbU hbL hvol' hrel1 hrel3 hrel2' hvL hv1 hlam hε Cm Cp Cb c1 ε hCm
    hCp hc1 hε0 hr hδ hbLpos hvLpos hup hcount hrate' hm1 hm2 hvar hhit hcard a

end NearCritical.Section10
