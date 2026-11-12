module

public import NearCritical.Section10StepOneOnCrossing

/-! The property hypothesis of the candidate count, from the crossing event.

`hproperty_from_crossAll`: under the hypotheses of
`stepOne_property_on_crossAll` and an upper bound
`P[spanning] <= Cs/(N+1)^2` for the root,

  `delta * P[spanning] <= P[StepOneProperty and spanning]`,
  `delta = (1 - a₁ - a₂ - a₃) * c / (4 Cs)`.

This is the hypothesis `hproperty` of `hcand_of_raw` for that root. Proof:
`crossAll` is contained in spanning, has probability at least `c/t^2`, and a
fraction `1 - a₁ - a₂ - a₃` of it has the Step 1 property.
-/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open MeasureTheory
open scoped Classical

theorem hproperty_from_crossAll {d : ℕ} {c K B C Cs : ℝ} (hc : 0 ≤ c) (hK : 0 ≤ K)
    (hB0 : 0 ≤ B) (hCs : 0 < Cs) (hcross : SplitCrossInput d c)
    (htail : ∀ (N : ℕ) (x : Vertex d), x ∈ centeredBox d N →
      ∀ (f : Fin d × Bool) (T : ℝ), 0 < T →
        (percolation d (criticalPoint d)).real (Section7.farFaceEvent N x f T) ≤ K / T)
    (hBm : BoxFaceFirstMoment d B) (ordinary : OrdinaryArmWindowInput d C)
    (typ : TypicalParameters) (hdU : 0 < typ.diameterUpper) (hbU : 0 < typ.boundaryUpper)
    (hbL : 0 ≤ typ.boundaryLower) (t N : ℕ) (ht : 8 ≤ t) (hN : (t - 1) / 2 = N) (htCross : hcross.threshold ≤ t)
    {x : Vertex d} (hx : x ∈ centeredBox d ((t - 1) / 32)) {a₁ a₂ a₃ : ℝ}
    (ha₁ : 0 ≤ a₁) (ha₂ : 0 ≤ a₂) (ha₃ : 0 ≤ a₃) (hsum : a₁ + a₂ + a₃ ≤ 1)
    (hrel1 : (d : ℝ) * K ≤ a₁ * (c / 4) * typ.diameterUpper)
    (hrel3 : (d : ℝ) * B ≤ 2 * a₃ * (c / 4) * typ.boundaryUpper)
    (hrel2 : 4 * (d : ℝ) * ((⌊2 * (typ.boundaryLower * (2 * (t : ℝ)) ^ 2)⌋₊ : ℝ) *
        (C / (t : ℝ) ^ 2) * (C / ((t / 4 : ℕ) : ℝ) ^ 2)) ≤ a₂ * (c / (t : ℝ) ^ 2))
    (hspanhi : (percolation d (criticalPoint d)).real
      (finiteRootSpanningEvent (centeredBox d N) (typicalFace t (0 : Vertex d)) x) ≤
        Cs / (N + 1 : ℝ) ^ 2) :
    ((1 - a₁ - a₂ - a₃) * c / (4 * Cs)) * (percolation d (criticalPoint d)).real
        (finiteRootSpanningEvent (centeredBox d N) (typicalFace t (0 : Vertex d)) x) ≤
      (percolation d (criticalPoint d)).real
        ({ω | rootedClusterProperty (centeredBox d N) x
            (StepOneProperty typ t (0 : Vertex d)) ω} ∩
          finiteRootSpanningEvent (centeredBox d N) (typicalFace t (0 : Vertex d)) x) := by
  set μ := percolation d (criticalPoint d) with hμ
  have ht1 : 1 ≤ t := by omega
  have hcube : typicalCube t (0 : Vertex d) = centeredBox d N := by
    rw [typicalCube_zero t ht1, hN]
  have hxN : x ∈ centeredBox d N := by
    rw [mem_centeredBox] at hx ⊢
    intro i
    obtain ⟨h1, h2⟩ := hx i
    constructor <;> omega
  have hxQ : x ∈ typicalCube t (0 : Vertex d) := by
    rw [hcube]
    exact hxN
  have hsub := crossAll_subset_spanning t ht1 t hxQ
  rw [hcube] at hsub
  have hprop := stepOne_property_on_crossAll hc hK hB0 hcross htail hBm ordinary typ hdU hbU
    hbL t N ht hN htCross hx ha₁ ha₂ ha₃ hrel1 hrel3 hrel2
  have hmono : μ.real ({ω | rootedClusterProperty (centeredBox d N) x
        (StepOneProperty typ t (0 : Vertex d)) ω} ∩ crossAll t t x) ≤
      μ.real ({ω | rootedClusterProperty (centeredBox d N) x
        (StepOneProperty typ t (0 : Vertex d)) ω} ∩
        finiteRootSpanningEvent (centeredBox d N) (typicalFace t (0 : Vertex d)) x) :=
    measureReal_mono (Set.inter_subset_inter_right _ hsub) (measure_ne_top μ _)
  have hS := hcross.crossing t htCross x hx
  have hθ : 0 ≤ 1 - a₁ - a₂ - a₃ := by linarith
  have htR : (0:ℝ) < (t : ℝ) := by exact_mod_cast (by omega : 0 < t)
  have hNpos : (0:ℝ) < (N : ℝ) + 1 := by positivity
  have hNt : (t : ℝ) ≤ 2 * ((N : ℝ) + 1) := by
    have : t ≤ 2 * (N + 1) := by omega
    exact_mod_cast this
  -- P[spanning] * c / (4 Cs) <= c / t^2
  have hkey : c / (4 * Cs) * μ.real
      (finiteRootSpanningEvent (centeredBox d N) (typicalFace t (0 : Vertex d)) x) ≤
      c / (t : ℝ) ^ 2 := by
    have h1 : c / (4 * Cs) * μ.real
        (finiteRootSpanningEvent (centeredBox d N) (typicalFace t (0 : Vertex d)) x) ≤
        c / (4 * Cs) * (Cs / (N + 1 : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left hspanhi (by positivity)
    have h2 : c / (4 * Cs) * (Cs / (N + 1 : ℝ) ^ 2) = c / (4 * (N + 1 : ℝ) ^ 2) := by
      field_simp
    have h3 : c / (4 * (N + 1 : ℝ) ^ 2) ≤ c / (t : ℝ) ^ 2 := by
      apply div_le_div_of_nonneg_left hc (by positivity)
      nlinarith
    linarith
  calc ((1 - a₁ - a₂ - a₃) * c / (4 * Cs)) * μ.real
        (finiteRootSpanningEvent (centeredBox d N) (typicalFace t (0 : Vertex d)) x)
      = (1 - a₁ - a₂ - a₃) * (c / (4 * Cs) * μ.real
        (finiteRootSpanningEvent (centeredBox d N) (typicalFace t (0 : Vertex d)) x)) := by
        ring
    _ ≤ (1 - a₁ - a₂ - a₃) * (c / (t : ℝ) ^ 2) := mul_le_mul_of_nonneg_left hkey hθ
    _ ≤ (1 - a₁ - a₂ - a₃) * μ.real (crossAll t t x) := mul_le_mul_of_nonneg_left hS hθ
    _ ≤ _ := hprop.trans hmono

end NearCritical.Section10
