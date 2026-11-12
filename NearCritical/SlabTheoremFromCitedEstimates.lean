module

public import NearCritical.AppendixBoxWideFinal
public import NearCritical.Section10BoxFaceFromPioneer
public import NearCritical.Section10MarkedMomentPackage
public import NearCritical.SlabTheoremFromUpper
public import NearCritical.SlabUpperFinal

/-! The slab theorem from the percolation inputs used in the paper. -/

@[expose] public section
noncomputable section

namespace NearCritical

open MeasureTheory Section8 Section10
open scoped Classical ENNReal

/-- The inverse-square slab critical-point bounds in dimension at least nine.
The marked moments and the finite-box first moment are derived internally. -/
theorem slab_theorem_from_cited_estimates (e : ℕ) (he : 2 ≤ e)
    (asymp : TwoPointAsymptotics (e + 7)) (rectangle : RestrictedRectangleLowerInput (e + 7))
    (reimer : FiniteBernoulliBKRInput)
    {C Ar S cSlab Pioneer : ℝ} (hC : 0 ≤ C) (hAr : 0 ≤ Ar) (hS : 0 ≤ S)
    (hSlab : 0 < cSlab) (hPioneer : 0 < Pioneer)
    (panis : PanisHalfSpaceTwoPointUpper (e + 7) C)
    (arm : ∀ i : Fin (e + 7), HalfSpaceCriticalArmInput i Ar)
    (second : ∀ i : Fin (e + 7), SlabBoundarySecondMomentUpper i S)
    (hslab : ∀ (i : Fin (e + 7)) (h : ℕ), 1 ≤ h → ENNReal.ofReal (cSlab / (h : ℝ)) ≤
      slabPioneerMass (criticalPoint (e + 7)) i 0 (h : ℤ) 0 (h : ℤ))
    (hpioneer : ∀ (i : Fin (e + 7)) (n : ℕ),
      halfSpacePioneerMass (criticalPoint (e + 7)) i (n : ℤ) ≤ ENNReal.ofReal Pioneer)
    {c₀ K Carm α A c : ℝ} (hc₀ : 0 < c₀) (hK : 0 ≤ K) (hCarm : 0 < Carm)
    (hcross : SplitCrossInput (e + 7) c₀)
    (htail : ∀ (N : ℕ) (x : Vertex (e + 7)), x ∈ centeredBox (e + 7) N →
      ∀ (f : Fin (e + 7) × Bool) (T : ℝ), 0 < T →
        (percolation (e + 7) (criticalPoint (e + 7))).real (Section7.farFaceEvent N x f T) ≤ K / T)
    (hsize : ClusterSizeInput (e + 7) α A c) (ordinary : OrdinaryArmWindowInput (e + 7) Carm)
    {a₁ a₂ a₃ : ℝ} (ha₁ : 0 < a₁) (ha₂ : 0 < a₂) (ha₃ : 0 < a₃)
    (hsum : a₁ + a₂ + a₃ < 1) (hc : 0 < c)
    {η : ℝ} (hη : 0 < η) (κ : Measure Bool) [IsProbabilityMeasure κ]
    (hκ : κ {true} ≤ ENNReal.ofReal (1 - η))
    {θ : ℝ≥0∞} (hθ0 : θ ≠ 0) (hθ : MixedSiteBondPercolationInput 2 κ θ)
    {Cdec cdec : ℝ} (hCdec : 0 < Cdec) (hcdec : 0 < cdec)
    (decay : WeightedPositiveHeightPioneerDecay (criticalPoint (e + 7))
      (⟨e + 7 - 1, by omega⟩ : Fin (e + 7)) Cdec cdec) :
    ∃ a A : ℝ, 0 < a ∧ 0 < A ∧ ∀ n : ℕ, 1 ≤ n →
      a / (n : ℝ) ^ 2 ≤
        (restrictedCriticalPoint (e + 7) (slabVertices (e + 7) (e + 7 - 1) n) : ℝ) -
          criticalPoint (e + 7) ∧
      (restrictedCriticalPoint (e + 7) (slabVertices (e + 7) (e + 7 - 1) n) : ℝ) -
          criticalPoint (e + 7) ≤
        (restrictedCriticalPoint (e + 7) (slabVertices (e + 7) 2 n) : ℝ) -
          criticalPoint (e + 7) ∧
      (restrictedCriticalPoint (e + 7) (slabVertices (e + 7) 2 n) : ℝ) -
          criticalPoint (e + 7) ≤ A / (n : ℝ) ^ 2 := by
  obtain ⟨hp0, hp1⟩ :=
    criticalPoint_interior_of_twoPointAsymptotics (by omega) (0 : Fin (e + 7)) asymp
  obtain ⟨b, hb, hbox⟩ := marked_box_lower_from_pioneers e asymp rectangle hAr hS hC hSlab hPioneer
    arm second panis hslab hpioneer
  have ordinary' : OrdinaryArmWindowInput (e + 7) (max 1 Carm) := by
    intro p x n hn hp
    exact (ordinary p x n hn hp).trans (div_le_div_of_nonneg_right (le_max_right _ _) (by positivity))
  have hmom := marked_moment_package_of_box_lower e he asymp C Ar S (max 1 Carm)
    hC hAr hS (le_max_left _ _) panis arm second ordinary' b hb hbox
  have hBm := boxFaceFirstMoment_of_pioneerMass hPioneer.le hpioneer
  have hupper := slab_upper_final (by omega) asymp hc₀ hK hPioneer.le hCarm
    hcross htail hBm hsize ordinary ha₁.le ha₂.le ha₃.le hsum hc ha₁ ha₂ ha₃
    rectangle reimer hp0 hp1 hη hmom κ hκ hθ0 hθ
  exact slab_theorem_from_upper (by omega) asymp hCdec hcdec decay hupper

end NearCritical
