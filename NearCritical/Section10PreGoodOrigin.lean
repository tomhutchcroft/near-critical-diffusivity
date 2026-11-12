module

public import NearCritical.Section10CandidateFinal
public import NearCritical.Section10RegularityLoss

/-! prop.proba.pregood at one scale, from cited inputs and the regularity-energy
moments: `hcand_origin_final` and `hloss_of_energy_moments` fed into
`hpre_of_candidate_counts` with `L = c1 (2t)^(d-6)`.

Hypotheses: cited inputs (assumption (A), split crossing, far-face tail, boundary
first moment, one arm, eq.cluster_size), explicit relations between constants,
and the energy moments of prop.choice_c (`hm1 hm2 hvar hhit hcard`), which are
NOT derived.
-/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open MeasureTheory
open scoped Classical

theorem pregood_origin_of_moments {d : ℕ} (hd : 9 ≤ d) (hA : TwoPointAsymptotics d)
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
      Cc * (N + 1 : ℝ) ^ 4 ≤ typ.volumeUpper * (2 * (t : ℝ)) ^ 4 →
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
      ∀ (Cm Cp Cb c1 ε : ℝ) (hCm : 0 ≤ Cm) (hCp : 0 ≤ Cp) (hc1 : 0 < c1) (hε0 : 0 < ε)
        (hr : 1 ≤ typ.regularRadius) (hδ : 0 < typ.regularTolerance)
        (hbLpos : 0 < typ.boundaryLower) (hvLpos : 0 < typ.volumeLower)
        (hup : 27 * Carm / (typ.volumeLower * ε) ≤ typ.countUpper)
        (hcount : typ.countLower * (2 * (t : ℝ)) ^ (d - 6) ≤ c1 * (2 * (t : ℝ)) ^ (d - 6) / 2)
        (hrate : c1 * (2 * (t : ℝ)) ^ (d - 6) ≤ ((((1 - a₁ - a₂ - a₃) * c₀ / (4 * (64 * Carm))) * (c₀ / 4) * (cc / 4) ^ d / 4) / Cc) * (N + 1 : ℝ) ^ (d - 6))
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
  obtain ⟨Cc, D, hCc, hD, h⟩ := hcand_origin_final hd hA hc₀ hK hB0 hCarm hcross htail hBm hsize
    ordinary hcc0 hcc ha₁ ha₂ ha₃ hsum
  refine ⟨Cc, D, hCc, hD, ?_⟩
  intro typ t N htT hN hratio hdU hbU hbL hvol hrel1 hrel3 hrel2 hvL hv1 hlam hε Cm Cp Cb c1 ε hCm hCp
    hc1 hε0 hr hδ hbLpos hvLpos hup hcount hrate hm1 hm2 hvar hhit hcard a
  have ht : 64 ≤ t := (le_max_left _ _).trans htT
  exact hpre_of_candidate_counts (⟨0, by omega⟩ : Fin d) (by omega) typ t (by omega) hCarm
    ordinary hvLpos hε0 hup hcount
    (h typ t N htT hN hratio hdU hbU hbL hvol hrel1 hrel3 hrel2 hvL hv1 hlam hε _ hrate)
    (hloss_of_energy_moments (by omega) typ t (by omega) hr hδ hbLpos hCm hCp hc1 hm1 hm2 hvar
      hhit hcard) a

end NearCritical.Section10
