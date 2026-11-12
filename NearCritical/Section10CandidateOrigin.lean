module

public import NearCritical.Section10HeartBounds

/-! The candidate count of Step 1 of `prop.proba.pregood` at the origin cube.

`hcand_origin` assembles `hcand_of_raw` with

* the two-sided spanning probability (`span_lower_of_splitCross`,
  `span_upper_of_ordinary`),
* the Step 1 property probability (`hproperty_from_crossAll`),
* the heart as root set (`Section10HeartBounds`).

Result: constants `Cv, D > 0` (depending on the dimension, the cited constants,
the heart ratio and the failure fractions `a_i`) such that for every `typ` with
that heart ratio and every `t >= 64`, the number of candidate clusters of the
origin typical cube is at least `L` except with probability `D/(N+1)^(d-8)`,
for every `L <= ((delta c cz/4)/Cv)(N+1)^(d-6)`.

Hypotheses left: the cited inputs (assumption (A), split crossing, far-face
tail, boundary first moment, one arm), three relations between constants, the
volume relation `Cv (N+1)^4 <= C_v (2t)^4`, and SMALL-VOLUME CONTROL (`hlow`),
which is not derived here.
-/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open MeasureTheory
open scoped Classical

theorem hcand_origin {d : ℕ} (hd : 9 ≤ d) (hA : TwoPointAsymptotics d)
    {c₀ K B Carm : ℝ} (hc₀ : 0 < c₀) (hK : 0 ≤ K) (hB0 : 0 ≤ B) (hCarm : 0 < Carm)
    (hcross : SplitCrossInput d c₀)
    (htail : ∀ (N : ℕ) (x : Vertex d), x ∈ centeredBox d N →
      ∀ (f : Fin d × Bool) (T : ℝ), 0 < T →
        (percolation d (criticalPoint d)).real (Section7.farFaceEvent N x f T) ≤ K / T)
    (hBm : BoxFaceFirstMoment d B) (ordinary : OrdinaryArmWindowInput d Carm)
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
      (∀ x ∈ typicalHeart t (0 : Vertex d) typ.heartRatio,
        (percolation d (criticalPoint d)).real
          ({ω | ((finiteBoxCluster ω (centeredBox d N) x).card : ℝ) ≤
              typ.volumeLower * (2 * (t : ℝ)) ^ 4} ∩
            finiteRootSpanningEvent (centeredBox d N) (typicalFace t (0 : Vertex d)) x) ≤
        (((1 - a₁ - a₂ - a₃) * c₀ / (4 * (64 * Carm))) / 4) *
          (percolation d (criticalPoint d)).real
            (finiteRootSpanningEvent (centeredBox d N) (typicalFace t (0 : Vertex d)) x)) →
      ∀ L : ℝ, L ≤ ((((1 - a₁ - a₂ - a₃) * c₀ / (4 * (64 * Carm))) * (c₀ / 4) *
          (cc / 4) ^ d / 4) / Cv) * (N + 1 : ℝ) ^ (d - 6) →
      (percolation d (criticalPoint d)).real {ω | ¬ L ≤
        ((filteredClusterFamily ω (typicalCube t (0 : Vertex d))
          (CandidateCluster typ t 0 ω)).card : ℝ)} ≤ D / (N + 1 : ℝ) ^ (d - 8) := by
  have hδ : 0 < (1 - a₁ - a₂ - a₃) * c₀ / (4 * (64 * Carm)) := by
    have : 0 < 1 - a₁ - a₂ - a₃ := by linarith
    positivity
  obtain ⟨Cv, D, hCv, hD, h⟩ := hcand_of_raw hd hA
    ((1 - a₁ - a₂ - a₃) * c₀ / (4 * (64 * Carm))) (c₀ / 4) (64 * Carm) ((cc / 4) ^ d)
    ((2 : ℝ) ^ d) hδ (by positivity) (by positivity) (by positivity) (by positivity)
  refine ⟨Cv, D, hCv, hD, ?_⟩
  intro typ t N htT hN hratio hdU hbU hbL hvol hrel1 hrel3 hrel2 hlow L hL
  have ht : 64 ≤ t := (le_max_left _ _).trans htT
  have htCross : hcross.threshold ≤ t := (le_max_right _ _).trans htT
  subst hratio
  have ht1 : 1 ≤ t := by omega
  have ht8 : 8 ≤ t := by omega
  have hroot : ∀ x ∈ typicalHeart t (0 : Vertex d) typ.heartRatio,
      x ∈ centeredBox d ((t - 1) / 32) :=
    fun x hx => heart_subset_rootRegion t ht1 hcc hx
  have hup : ∀ x ∈ typicalHeart t (0 : Vertex d) typ.heartRatio,
      (percolation d (criticalPoint d)).real
        (finiteRootSpanningEvent (centeredBox d N) (typicalFace t (0 : Vertex d)) x) ≤
      64 * Carm / (N + 1 : ℝ) ^ 2 :=
    fun x hx => span_upper_of_ordinary hCarm.le ordinary t N ht8 hN (hroot x hx)
      ((⟨0, by omega⟩ : Fin d), true)
  exact h typ t N ht1 hN hvol (heart_card_lower t N ht hN hcc0 hcc)
    (heart_card_upper t N ht1 hN typ.heartRatio)
    (fun x hx => span_lower_of_splitCross hc₀.le hcross t N ht1 hN htCross (hroot x hx))
    hup
    (fun x hx => hproperty_from_crossAll hc₀.le hK hB0 (by positivity) hcross htail hBm ordinary
      typ hdU hbU hbL t N ht8 hN htCross (hroot x hx) ha₁ ha₂ ha₃ hsum.le hrel1 hrel3 hrel2 (hup x hx))
    hlow L hL

end NearCritical.Section10
