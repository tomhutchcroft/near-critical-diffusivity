import NearCritical.MainResults
import NearCritical.VariableSpeedWalkPoissonClock

/-! The diffusivity theorem (source thm.main, random-walk form) with the
Poisson-clock premise discharged.

`variableSpeedSamplePath_diffusivity_two_sided_from_inputs` takes
`ExponentialClockPoissonInput` as a premise. That statement is proved in
`VariableSpeedWalkPoissonClock`, so it is supplied here. Every remaining
premise is a result cited by the paper; see `CITED-INPUTS.md`.

 -/

noncomputable section

namespace NearCritical

open MeasureTheory Filter Set Section8 Section10
open scoped Classical ENNReal NNReal

/-- **Source thm.main.** For every `p > p_c` the variable-speed walk on the
infinite cluster has Gaussian one-time marginals of a common variance `v` in
every coordinate, and `c (p - p_c)^2 ≤ v ≤ C (p - p_c)^2`. -/
theorem variableSpeedSamplePath_diffusivity_two_sided (e : ℕ) (he : 2 ≤ e)
    (asymp : TwoPointAsymptotics (e + 7)) (rectangle : RestrictedRectangleLowerInput (e + 7))
    (reimer : FiniteBernoulliBKRInput)
    {C Ar cPioneer Pioneer : ℝ} (hC : 0 ≤ C) (hAr : 0 ≤ Ar)
    (hcPioneer : 0 < cPioneer) (hPioneer : 0 < Pioneer)
    (panis : PanisHalfSpaceTwoPointUpper (e + 7) C)
    (arm : ∀ i : Fin (e + 7), HalfSpaceCriticalArmInput i Ar)
    (hpioneerLower : ∀ (i : Fin (e + 7)) (n : ℕ), 1 ≤ n →
      ENNReal.ofReal cPioneer ≤ halfSpacePioneerMass (criticalPoint (e + 7)) i (n : ℤ))
    (hpioneerUpper : ∀ (i : Fin (e + 7)) (n : ℕ), 1 ≤ n →
      halfSpacePioneerMass (criticalPoint (e + 7)) i (n : ℤ) ≤ ENNReal.ofReal Pioneer)
    {K Carm α A c : ℝ} (hK : 0 ≤ K) (hCarm : 0 < Carm)
    (hmoment : Section7.HalfSpaceLongPathMoment (e + 7) K)
    (hsize : ClusterSizeInput (e + 7) α A c) (ordinary : OrdinaryArmWindowInput (e + 7) Carm)
    {a₁ a₂ a₃ : ℝ} (ha₁ : 0 < a₁) (ha₂ : 0 < a₂) (ha₃ : 0 < a₃)
    (hsum : a₁ + a₂ + a₃ < 1) (hc : 0 < c)
    (i : Fin (e+7)) {BX bX : ℝ} (hBX : 0 < BX) (hbX : 0 < bX)
    (pioneers : HalfSpacePioneerExponentialInput i BX bX)
    (δupper : ℝ) (hδupper : 0 < δupper) (hδupper' : δupper < 1)
    (hθ : UpperPowerBound (criticalPoint (e+7):ℝ) (densityReal (e+7)) 1)
    (einstein : VariableSpeedSampleEinsteinInput (e+7)) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ p : unitInterval, criticalPoint (e+7) < p →
      ∃ v : ℝ≥0, (∀ j : Fin (e+7), VariableSpeedSampleGaussianMarginal (e+7) p j v) ∧
        c*((p:ℝ)-(criticalPoint (e+7):ℝ))^2 ≤ (v:ℝ) ∧
        (v:ℝ) ≤ C*((p:ℝ)-(criticalPoint (e+7):ℝ))^2 :=
  variableSpeedSamplePath_diffusivity_two_sided_from_inputs e he asymp rectangle reimer
    hC hAr hcPioneer hPioneer panis arm hpioneerLower hpioneerUpper hK hCarm hmoment hsize
    ordinary ha₁ ha₂ ha₃ hsum hc i hBX hbX pioneers δupper hδupper hδupper' hθ
    exponentialClockPoissonInput einstein

/-- At `p_c` the weighted pioneer bound of source eq.expansion_12 gives the
uniform positive-height bound of eq.expansion_2. -/
theorem halfSpacePioneerUpper_of_weighted_critical {d : ℕ} (i : Fin d) {C c : ℝ}
    (hC : 0 < C) (hpc : 0 < (criticalPoint d : ℝ))
    (decay : WeightedPositiveHeightPioneerDecay (criticalPoint d) i C c) :
    ∀ n : ℕ, 1 ≤ n → halfSpacePioneerMass (criticalPoint d) i (n : ℤ) ≤
      ENNReal.ofReal (2 * C / (criticalPoint d : ℝ)) := by
  intro n hn
  have h := positiveHeightPioneerDecay_of_weighted (criticalPoint d) i hC hpc
    (by linarith) decay n hn
  refine h.trans (ENNReal.ofReal_le_ofReal ?_)
  simp

/-- **Source thm.slab**, with a single pioneer upper premise: the critical
case of eq.expansion_12 along every axis. -/
theorem slab_theorem (e : ℕ) (he : 2 ≤ e)
    (asymp : TwoPointAsymptotics (e + 7)) (rectangle : RestrictedRectangleLowerInput (e + 7))
    (reimer : FiniteBernoulliBKRInput)
    {C Ar cPioneer : ℝ} (hC : 0 ≤ C) (hAr : 0 ≤ Ar) (hcPioneer : 0 < cPioneer)
    (panis : PanisHalfSpaceTwoPointUpper (e + 7) C)
    (arm : ∀ i : Fin (e + 7), HalfSpaceCriticalArmInput i Ar)
    (hpioneerLower : ∀ (i : Fin (e + 7)) (n : ℕ), 1 ≤ n →
      ENNReal.ofReal cPioneer ≤ halfSpacePioneerMass (criticalPoint (e + 7)) i (n : ℤ))
    {K Carm α A c : ℝ} (hK : 0 ≤ K) (hCarm : 0 < Carm)
    (hmoment : Section7.HalfSpaceLongPathMoment (e + 7) K)
    (hsize : ClusterSizeInput (e + 7) α A c) (ordinary : OrdinaryArmWindowInput (e + 7) Carm)
    {a₁ a₂ a₃ : ℝ} (ha₁ : 0 < a₁) (ha₂ : 0 < a₂) (ha₃ : 0 < a₃)
    (hsum : a₁ + a₂ + a₃ < 1) (hc : 0 < c)
    (planar : Grimmett1999PlanarMixedInput)
    {Cdec cdec : ℝ} (hCdec : 0 < Cdec) (hcdec : 0 < cdec)
    (decay : ∀ j : Fin (e + 7),
      WeightedPositiveHeightPioneerDecay (criticalPoint (e + 7)) j Cdec cdec) :
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
  have hpc : 0 < (criticalPoint (e + 7) : ℝ) := External.criticalPoint_pos (by omega)
  exact slab_theorem_from_inputs e he asymp rectangle reimer hC hAr hcPioneer
    (by positivity : 0 < 2 * Cdec / (criticalPoint (e + 7) : ℝ)) panis arm hpioneerLower
    (fun j => halfSpacePioneerUpper_of_weighted_critical j hCdec hpc (decay j))
    hK hCarm hmoment hsize ordinary ha₁ ha₂ ha₃ hsum hc planar hCdec hcdec (decay _)

/-- **Source thm.main**, with a single pioneer upper premise: eq.expansion_12
along every axis. The separate critical upper bound is its case `p = p_c`. -/
theorem diffusivity_theorem (e : ℕ) (he : 2 ≤ e)
    (asymp : TwoPointAsymptotics (e + 7)) (rectangle : RestrictedRectangleLowerInput (e + 7))
    (reimer : FiniteBernoulliBKRInput)
    {C Ar cPioneer : ℝ} (hC : 0 ≤ C) (hAr : 0 ≤ Ar) (hcPioneer : 0 < cPioneer)
    (panis : PanisHalfSpaceTwoPointUpper (e + 7) C)
    (arm : ∀ i : Fin (e + 7), HalfSpaceCriticalArmInput i Ar)
    (hpioneerLower : ∀ (i : Fin (e + 7)) (n : ℕ), 1 ≤ n →
      ENNReal.ofReal cPioneer ≤ halfSpacePioneerMass (criticalPoint (e + 7)) i (n : ℤ))
    {K Carm α A c : ℝ} (hK : 0 ≤ K) (hCarm : 0 < Carm)
    (hmoment : Section7.HalfSpaceLongPathMoment (e + 7) K)
    (hsize : ClusterSizeInput (e + 7) α A c) (ordinary : OrdinaryArmWindowInput (e + 7) Carm)
    {a₁ a₂ a₃ : ℝ} (ha₁ : 0 < a₁) (ha₂ : 0 < a₂) (ha₃ : 0 < a₃)
    (hsum : a₁ + a₂ + a₃ < 1) (hc : 0 < c)
    {BX bX : ℝ} (hBX : 0 < BX) (hbX : 0 < bX)
    (pioneers : ∀ j : Fin (e + 7), HalfSpacePioneerExponentialInput j BX bX)
    (δupper : ℝ) (hδupper : 0 < δupper) (hδupper' : δupper < 1)
    (hθ : UpperPowerBound (criticalPoint (e+7):ℝ) (densityReal (e+7)) 1)
    (einstein : VariableSpeedSampleEinsteinInput (e+7)) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ p : unitInterval, criticalPoint (e+7) < p →
      ∃ v : ℝ≥0, (∀ j : Fin (e+7), VariableSpeedSampleGaussianMarginal (e+7) p j v) ∧
        c*((p:ℝ)-(criticalPoint (e+7):ℝ))^2 ≤ (v:ℝ) ∧
        (v:ℝ) ≤ C*((p:ℝ)-(criticalPoint (e+7):ℝ))^2 := by
  have hpc : 0 < (criticalPoint (e + 7) : ℝ) := External.criticalPoint_pos (by omega)
  exact variableSpeedSamplePath_diffusivity_two_sided e he asymp rectangle reimer hC hAr
    hcPioneer (by positivity : 0 < 2 * BX / (criticalPoint (e + 7) : ℝ)) panis arm
    hpioneerLower
    (fun j => halfSpacePioneerUpper_of_weighted_critical j hBX hpc
      (pioneers j (criticalPoint (e + 7)) (by linarith) le_rfl))
    hK hCarm hmoment hsize ordinary ha₁ ha₂ ha₃ hsum hc (⟨0, by omega⟩ : Fin (e + 7))
    hBX hbX (pioneers _) δupper hδupper hδupper' hθ einstein

end NearCritical
