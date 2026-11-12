module

public import NearCritical.Section10SmallVolume

/-! Candidate count at the origin cube with small-volume control discharged:
`hcand_origin` + `hlow_of_clusterSize` at `lam = 4096 * volumeLower` (valid since
`2t <= 8m`, `m = N - (t-1)/32`). All inputs are cited (assumption (A), split
crossing, far-face tail, boundary first moment, one arm, eq.cluster_size) or
explicit relations between constants.
-/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open MeasureTheory
open scoped Classical

theorem hcand_origin_final {d : ℕ} (hd : 9 ≤ d) (hA : TwoPointAsymptotics d)
    {c₀ K B Carm α A c : ℝ} (hc₀ : 0 < c₀) (hK : 0 ≤ K) (hB0 : 0 ≤ B) (hCarm : 0 < Carm)
    (hcross : SplitCrossInput d c₀)
    (htail : ∀ (N : ℕ) (x : Vertex d), x ∈ centeredBox d N →
      ∀ (f : Fin d × Bool) (T : ℝ), 0 < T →
        (percolation d (criticalPoint d)).real (Section7.farFaceEvent N x f T) ≤ K / T)
    (hBm : BoxFaceFirstMoment d B) (hsize : ClusterSizeInput d α A c) (ordinary : OrdinaryArmWindowInput d Carm)
    {cc : ℝ} (hcc0 : 0 < cc) (hcc : cc ≤ 1 / 16) {a₁ a₂ a₃ : ℝ}
    (ha₁ : 0 ≤ a₁) (ha₂ : 0 ≤ a₂) (ha₃ : 0 ≤ a₃) (hsum : a₁ + a₂ + a₃ < 1) :
    ∃ Cv D : ℝ, 0 < Cv ∧ 0 < D ∧
      ∀ (typ : TypicalParameters) (t N : ℕ), max 64 hcross.threshold ≤ t → (t - 1) / 2 = N →
      typ.heartRatio = cc → 0 < typ.diameterUpper → 0 < typ.boundaryUpper →
      0 ≤ typ.boundaryLower →
      Cv * (N + 1 : ℝ) ^ 4 ≤ typ.volumeUpper * (2 * (t : ℝ)) ^ 4 →
      (d : ℝ) * K ≤ a₁ * (c₀ / 4) * typ.diameterUpper →
      (d : ℝ) * B ≤ 2 * a₃ * (c₀ / 4) * typ.boundaryUpper →
      4 * (d : ℝ) * ((⌊2 * (typ.boundaryLower * (2 * (t : ℝ)) ^ 2)⌋₊ : ℝ) *
        (Carm / (t : ℝ) ^ 2) * (Carm / ((t / 4 : ℕ) : ℝ) ^ 2)) ≤ a₂ * (c₀ / (t : ℝ) ^ 2) →
      0 ≤ typ.volumeLower →
      4096 * typ.volumeLower ≤ hsize.cap →
      A * (Real.log ((N - (t - 1) / 32 : ℕ) : ℝ)) ^ α / ((N - (t - 1) / 32 : ℕ) : ℝ) ^ 3 <
        4096 * typ.volumeLower →
      Real.exp (-c * (4096 * typ.volumeLower) ^ (-(1 / 3 : ℝ))) * Carm ≤
        (((1 - a₁ - a₂ - a₃) * c₀ / (4 * (64 * Carm))) / 4) * (c₀ / 4) →
      ∀ L : ℝ, L ≤ ((((1 - a₁ - a₂ - a₃) * c₀ / (4 * (64 * Carm))) * (c₀ / 4) *
          (cc / 4) ^ d / 4) / Cv) * (N + 1 : ℝ) ^ (d - 6) →
      (percolation d (criticalPoint d)).real {ω | ¬ L ≤
        ((filteredClusterFamily ω (typicalCube t (0 : Vertex d))
          (CandidateCluster typ t 0 ω)).card : ℝ)} ≤ D / (N + 1 : ℝ) ^ (d - 8) := by
  obtain ⟨Cv, D, hCv, hD, h⟩ := hcand_origin hd hA hc₀ hK hB0 hCarm hcross htail hBm ordinary
    hcc0 hcc ha₁ ha₂ ha₃ hsum
  refine ⟨Cv, D, hCv, hD, ?_⟩
  intro typ t N htT hN hratio hdU hbU hbL hvol hrel1 hrel3 hrel2 hvL hv1 hlam hε L hL
  have ht : 64 ≤ t := (le_max_left _ _).trans htT
  have htCross : hcross.threshold ≤ t := (le_max_right _ _).trans htT
  refine h typ t N htT hN hratio hdU hbU hbL hvol hrel1 hrel3 hrel2 ?_ L hL
  intro x hx
  have hxk : x ∈ centeredBox d ((t - 1) / 32) :=
    heart_subset_rootRegion t (by omega) (by rw [hratio]; exact hcc) hx
  have hδ : 0 ≤ ((1 - a₁ - a₂ - a₃) * c₀ / (4 * (64 * Carm))) / 4 := by
    have : 0 ≤ 1 - a₁ - a₂ - a₃ := by linarith
    positivity
  obtain ⟨m, hm⟩ : ∃ m, N - (t - 1) / 32 = m := ⟨_, rfl⟩
  rw [hm] at hlam
  refine hlow_of_clusterSize (by omega) hc₀.le hsize hcross ordinary t N ((t - 1) / 32) m ht hN htCross
    rfl hm hxk hlam hv1 ?_ hδ hε
  have htm : 2 * (t : ℝ) ≤ 8 * (m : ℝ) := by
    have : 2 * t ≤ 8 * m := by omega
    exact_mod_cast this
  have h4 : (2 * (t : ℝ)) ^ 4 ≤ (8 * (m : ℝ)) ^ 4 := pow_le_pow_left₀ (by positivity) htm 4
  calc typ.volumeLower * (2 * (t : ℝ)) ^ 4 ≤ typ.volumeLower * (8 * (m : ℝ)) ^ 4 :=
        mul_le_mul_of_nonneg_left h4 hvL
    _ = 4096 * typ.volumeLower * (m : ℝ) ^ 4 := by ring

end NearCritical.Section10
