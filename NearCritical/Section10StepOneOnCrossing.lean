module

public import NearCritical.Section10FaceReachBeta
public import NearCritical.Section10FaceCountUpper

/-! Step 1 of `prop.proba.pregood` on the all-faces crossing event.

`stepOne_property_on_crossAll`: at `p_c`, for `t >= 8` and a root `x` in
`centeredBox d ((t-1)/32)`, with the cited inputs

* `SplitCrossInput d c` (crossing through the `4d` split faces),
* the far-face tail (`K`, from the cited longest-path moment),
* `BoxFaceFirstMoment d B` (boundary first moment),
* `OrdinaryArmWindowInput d C` (one arm),

and the relations `d K <= a₁ (c/4) K_spn`, `d B <= 2 a₃ (c/4) C_b`,
`4 d floor(2 c_b (2t)^2) (C/t^2)(C/(t/4)^2) <= a₂ c / t^2`:

  `(1 - a₁ - a₂ - a₃) P[crossAll] <= P[StepOneProperty and crossAll]`.

So a positive fraction of the crossing event has the diameter bound, the
split-face lower counts and the face upper counts of def.spanning.z.
-/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open MeasureTheory
open scoped Classical

theorem stepOne_property_on_crossAll {d : ℕ} {c K B C : ℝ} (hc : 0 ≤ c) (hK : 0 ≤ K)
    (hB0 : 0 ≤ B) (hcross : SplitCrossInput d c)
    (htail : ∀ (N : ℕ) (x : Vertex d), x ∈ centeredBox d N →
      ∀ (f : Fin d × Bool) (T : ℝ), 0 < T →
        (percolation d (criticalPoint d)).real (Section7.farFaceEvent N x f T) ≤ K / T)
    (hBm : BoxFaceFirstMoment d B) (ordinary : OrdinaryArmWindowInput d C)
    (typ : TypicalParameters) (hdU : 0 < typ.diameterUpper) (hbU : 0 < typ.boundaryUpper)
    (hbL : 0 ≤ typ.boundaryLower) (t N : ℕ) (ht : 8 ≤ t) (hN : (t - 1) / 2 = N) (htCross : hcross.threshold ≤ t)
    {x : Vertex d} (hx : x ∈ centeredBox d ((t - 1) / 32)) {a₁ a₂ a₃ : ℝ}
    (ha₁ : 0 ≤ a₁) (ha₂ : 0 ≤ a₂) (ha₃ : 0 ≤ a₃)
    (hrel1 : (d : ℝ) * K ≤ a₁ * (c / 4) * typ.diameterUpper)
    (hrel3 : (d : ℝ) * B ≤ 2 * a₃ * (c / 4) * typ.boundaryUpper)
    (hrel2 : 4 * (d : ℝ) * ((⌊2 * (typ.boundaryLower * (2 * (t : ℝ)) ^ 2)⌋₊ : ℝ) *
        (C / (t : ℝ) ^ 2) * (C / ((t / 4 : ℕ) : ℝ) ^ 2)) ≤ a₂ * (c / (t : ℝ) ^ 2)) :
    (1 - a₁ - a₂ - a₃) * (percolation d (criticalPoint d)).real (crossAll t t x) ≤
      (percolation d (criticalPoint d)).real
        ({ω | rootedClusterProperty (centeredBox d N) x
          (StepOneProperty typ t (0 : Vertex d)) ω} ∩ crossAll t t x) := by
  have ht1 : 1 ≤ t := by omega
  have hxN : x ∈ centeredBox d N := by
    rw [mem_centeredBox] at hx ⊢
    intro i
    obtain ⟨h1, h2⟩ := hx i
    constructor <;> omega
  have hcube : typicalCube t (0 : Vertex d) = centeredBox d N := by
    rw [typicalCube_zero t ht1, hN]
  have hxQ : x ∈ typicalCube t (0 : Vertex d) := by
    rw [hcube]
    exact hxN
  have hS := hcross.crossing t htCross x hx
  have htR : (0:ℝ) < (t : ℝ) := by exact_mod_cast (by omega : 0 < t)
  have hNt : (t : ℝ) ≤ 2 * ((N : ℝ) + 1) := by
    have : t ≤ 2 * (N + 1) := by omega
    exact_mod_cast this
  have hS' : (c / 4) / (N + 1 : ℝ) ^ 2 ≤
      (percolation d (criticalPoint d)).real (crossAll t t x) := by
    refine le_trans ?_ hS
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hsq : (t : ℝ) ^ 2 ≤ 4 * ((N : ℝ) + 1) ^ 2 := by nlinarith
    nlinarith
  have hdiam := stepOne_diam_failure hK htail typ hdU t N ht1 hN x hxN (crossAll t t x)
    (c := c / 4) (by positivity) ha₁ hS' hrel1
  have hup := stepOne_upper_failure hB0 hBm typ hbU t N ht1 hN x hxN (crossAll t t x)
    (c := c / 4) (by positivity) ha₃ hS' hrel3
  have hlow0 := crossAll_lower_failure_numeric ordinary t ht hx hxQ
    (b := 2 * (typ.boundaryLower * (2 * (t : ℝ)) ^ 2)) (by positivity)
  rw [hcube] at hlow0
  have hlow : (percolation d (criticalPoint d)).real (crossAll t t x ∩
      {ω | ¬ ∀ i : (Fin d × Bool) × Bool,
        2 * (typ.boundaryLower * (2 * (t : ℝ)) ^ 2) ≤
          ((finiteBoxCluster ω (centeredBox d N) x ∩ typPatch t (0 : Vertex d) i).card : ℝ)}) ≤
      a₂ * (percolation d (criticalPoint d)).real (crossAll t t x) :=
    hlow0.trans (hrel2.trans (mul_le_mul_of_nonneg_left hS ha₂))
  exact stepOne_property_of_failures (criticalPoint d) typ t 0 (centeredBox d N) x
    (crossAll t t x) hdiam hlow hup

end NearCritical.Section10
