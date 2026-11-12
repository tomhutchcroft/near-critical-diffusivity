import NearCritical.DiffusivityFromCitedMoment
import NearCritical.VariableSpeedWalkMarginal

noncomputable section

namespace NearCritical

open MeasureTheory Filter Section8 Section10
open scoped Classical ENNReal NNReal

/-- The cited invariance principle and Einstein identification, at
time one and in a single coordinate, for the variable-speed walk. -/
def VariableSpeedEinsteinInput (d : ℕ) : Prop :=
  ∀ (p : unitInterval) (i : Fin d), criticalPoint d < p →
    VariableSpeedGaussianMarginal d p i (Real.toNNReal (einsteinDiffusivity d i p))

/-- The variance of the limiting variable-speed walk marginal has
the paper's two-sided near-critical bound. -/
theorem variableSpeedWalk_diffusivity_two_sided_from_cited_moment (e : ℕ) (he : 2 ≤ e)
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
    (hmoment : Section7.HalfSpaceLongPathMoment (e + 7) K)
    (hsize : ClusterSizeInput (e + 7) α A c) (ordinary : OrdinaryArmWindowInput (e + 7) Carm)
    {a₁ a₂ a₃ : ℝ} (ha₁ : 0 < a₁) (ha₂ : 0 < a₂) (ha₃ : 0 < a₃)
    (hsum : a₁ + a₂ + a₃ < 1) (hc : 0 < c)
    (i : Fin (e+7)) {BX bX : ℝ} (hBX : 0 < BX) (hbX : 0 < bX)
    (pioneers : HalfSpacePioneerExponentialInput i BX bX)
    (δupper : ℝ) (hδupper : 0 < δupper) (hδupper' : δupper < 1)
    (hθ : UpperPowerBound (criticalPoint (e+7):ℝ) (densityReal (e+7)) 1)
    (einstein : VariableSpeedEinsteinInput (e+7)) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ p : unitInterval, criticalPoint (e+7) < p →
      ∃ v : ℝ≥0, (∀ j : Fin (e+7), VariableSpeedGaussianMarginal (e+7) p j v) ∧
        c*((p:ℝ)-(criticalPoint (e+7):ℝ))^2 ≤ (v:ℝ) ∧
        (v:ℝ) ≤ C*((p:ℝ)-(criticalPoint (e+7):ℝ))^2 := by
  obtain ⟨c,C,hc',hC',h⟩ := einsteinDiffusivity_two_sided_from_cited_moment
    e he asymp rectangle reimer hC hAr hS hSlab hPioneer panis arm second hslab hpioneer
    hc₀ hK hCarm hcross hmoment hsize ordinary ha₁ ha₂ ha₃ hsum hc i hBX hbX pioneers
    δupper hδupper hδupper' hθ
  refine ⟨c,C,hc',hC',?_⟩
  intro p hp
  have ⟨hlo,hhi⟩ := h p (Subtype.coe_lt_coe.mpr hp) p.2.2
  have hv : 0 ≤ einsteinDiffusivity (e+7) i p :=
    (mul_nonneg hc'.le (sq_nonneg _)).trans hlo
  refine ⟨Real.toNNReal (einsteinDiffusivity (e+7) i p), ?_, ?_⟩
  · intro j
    rw [← einsteinDiffusivity_axes j i p hp]
    exact einstein p j hp
  · rw [Real.coe_toNNReal',max_eq_left hv]
    exact ⟨hlo,hhi⟩

end NearCritical
