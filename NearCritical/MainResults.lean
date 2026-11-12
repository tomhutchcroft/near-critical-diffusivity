import NearCritical.VariableSpeedWalkDiffusivity
import NearCritical.VariableSpeedWalkMarginalLaw
import NearCritical.SplitCrossDirectFinal
import NearCritical.SlabBoundarySecondMomentFromPioneers
import NearCritical.SlabPioneerFirstMoment
import NearCritical.CriticalPioneerUniform

/-! The main results for the actual percolation model.

This entry point exports the slab and chemical time-constant capstones
and the Einstein and variable-speed walk diffusivity bounds. The wrapper
below states the diffusivity bound using the exponential-clock sample law.
The final statements derive the slab moments and eventual split-crossing
estimate from the explicit percolation inputs. -/

noncomputable section

namespace NearCritical

open MeasureTheory Filter Set Section8 Section10
open scoped Classical ENNReal NNReal

/-- The one-time consequence of the cited invariance principle and
Einstein identification, for the exponential-clock sample law. -/
def VariableSpeedSampleEinsteinInput (d : ℕ) : Prop :=
  ∀ (p : unitInterval) (i : Fin d), criticalPoint d < p →
    VariableSpeedSampleGaussianMarginal d p i (Real.toNNReal (einsteinDiffusivity d i p))

/-- The limiting variance of the variable-speed sample path satisfies
the paper's two-sided near-critical estimate along every coordinate. -/
theorem variableSpeedSamplePath_diffusivity_two_sided_from_cited_moment (e : ℕ) (he : 2 ≤ e)
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
    (hclock : ExponentialClockPoissonInput)
    (einstein : VariableSpeedSampleEinsteinInput (e+7)) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ p : unitInterval, criticalPoint (e+7) < p →
      ∃ v : ℝ≥0, (∀ j : Fin (e+7), VariableSpeedSampleGaussianMarginal (e+7) p j v) ∧
        c*((p:ℝ)-(criticalPoint (e+7):ℝ))^2 ≤ (v:ℝ) ∧
        (v:ℝ) ≤ C*((p:ℝ)-(criticalPoint (e+7):ℝ))^2 := by
  have hd : 0 < e+7 := by omega
  have einstein' : VariableSpeedEinsteinInput (e+7) := by
    intro p j hp
    exact (variableSpeedSampleGaussianMarginal_iff hclock hd p j _).mp (einstein p j hp)
  obtain ⟨c,C,hc',hC',h⟩ := variableSpeedWalk_diffusivity_two_sided_from_cited_moment
    e he asymp rectangle reimer hC hAr hS hSlab hPioneer panis arm second hslab hpioneer
    hc₀ hK hCarm hcross hmoment hsize ordinary ha₁ ha₂ ha₃ hsum hc i hBX hbX pioneers
    δupper hδupper hδupper' hθ einstein'
  refine ⟨c,C,hc',hC',?_⟩
  intro p hp
  obtain ⟨v,hv,hlo,hhi⟩ := h p hp
  exact ⟨v,fun j => (variableSpeedSampleGaussianMarginal_iff hclock hd p j v).mpr (hv j),hlo,hhi⟩

/-- The paper’s slab threshold bounds with the direct split-crossing estimate. -/
theorem slab_theorem_from_inputs (e : ℕ) (he : 2 ≤ e)
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
    (planar : Grimmett1999PlanarMixedInput)
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
  obtain ⟨cSlab, hSlab, hslab⟩ :=
    slab_first_moment_lower (by omega : 2 ≤ e + 7) hC hcPioneer panis hpioneerLower
  have hpc : 0 < (criticalPoint (e + 7) : ℝ) := External.criticalPoint_pos (by omega)
  let Kp := Pioneer / (criticalPoint (e + 7) : ℝ)
  have hKp : 0 < Kp := div_pos hPioneer hpc
  have hpioneer (i : Fin (e + 7)) (n : ℕ) :
      halfSpacePioneerMass (criticalPoint (e + 7)) i (n : ℤ) ≤ ENNReal.ofReal Kp :=
    halfSpace_pioneer_uniform_of_positive_heights _ i hpc hPioneer.le (hpioneerUpper i) n
  have hS : 0 ≤ 2 * Kp ^ 3 := by positivity
  have second (i : Fin (e + 7)) : SlabBoundarySecondMomentUpper i (2 * Kp ^ 3) :=
    slabBoundarySecondMomentUpper_of_pioneerMass i hKp.le (hpioneer i)
  obtain ⟨c₀, hc₀, hcross⟩ := SplitCrossDirect.splitCrossInput_direct (by omega : 7 ≤ e + 7)
    asymp rectangle hAr hS hC hSlab hKp arm second panis hslab hpioneer
  exact slab_theorem_from_cited_moment e he asymp rectangle reimer hC hAr hS hSlab hKp
    panis arm second hslab hpioneer hc₀ hK hCarm hcross hmoment hsize ordinary
    ha₁ ha₂ ha₃ hsum hc planar hCdec hcdec decay

/-- The paper’s chemical time constant bounds with the direct split-crossing estimate. -/
theorem time_constant_from_inputs (e : ℕ) (he : 2 ≤ e)
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
    {cH CH : ℝ} (hcH : 0 < cH)
    (hHMS : ∀ q : unitInterval, 0 < (q : ℝ) → (q : ℝ) ≤ (criticalPoint (e + 7) : ℝ) →
      RayExponentialConnectionBound (e + 7) q (Pi.single 0 1) CH
        (cH * Real.sqrt ((criticalPoint (e + 7) : ℝ) - (q : ℝ))))
    (M : unitInterval → ℝ) (N : unitInterval → Seminorm ℝ (Fin (e + 7) → ℝ))
    (hlimit : ∀ p : unitInterval, criticalPoint (e + 7) < p →
      AEConnectedChemicalLimit (e + 7) p (Pi.single 0 1) (M p))
    (hunit : ∀ p : unitInterval, criticalPoint (e + 7) < p → ∀ j, (N p) (Pi.single j 1) = 1)
    (hreflect : ∀ p : unitInterval, criticalPoint (e + 7) < p → ∀ j x,
      (N p) (coordinateReflection j x) = (N p) x)
    (hGM : ∀ p : unitInterval, criticalPoint (e + 7) < p → ∀ ε : ℝ, ε ∈ Ioo 0 1 →
      ∃ B : ℝ, 0 < B ∧ ∃ R : ℝ, UniformChemicalLowerTail (e + 7) p (N p) (M p) ε B R) :
    ∃ cl Cu : ℝ, 0 < cl ∧ 0 < Cu ∧ ∀ p : unitInterval, criticalPoint (e + 7) < p →
      cl / Real.sqrt ((p : ℝ) - (criticalPoint (e + 7) : ℝ)) ≤ M p ∧
        M p ≤ Cu / Real.sqrt ((p : ℝ) - (criticalPoint (e + 7) : ℝ)) := by
  obtain ⟨cSlab, hSlab, hslab⟩ :=
    slab_first_moment_lower (by omega : 2 ≤ e + 7) hC hcPioneer panis hpioneerLower
  have hpc : 0 < (criticalPoint (e + 7) : ℝ) := External.criticalPoint_pos (by omega)
  let Kp := Pioneer / (criticalPoint (e + 7) : ℝ)
  have hKp : 0 < Kp := div_pos hPioneer hpc
  have hpioneer (i : Fin (e + 7)) (n : ℕ) :
      halfSpacePioneerMass (criticalPoint (e + 7)) i (n : ℤ) ≤ ENNReal.ofReal Kp :=
    halfSpace_pioneer_uniform_of_positive_heights _ i hpc hPioneer.le (hpioneerUpper i) n
  have hS : 0 ≤ 2 * Kp ^ 3 := by positivity
  have second (i : Fin (e + 7)) : SlabBoundarySecondMomentUpper i (2 * Kp ^ 3) :=
    slabBoundarySecondMomentUpper_of_pioneerMass i hKp.le (hpioneer i)
  obtain ⟨c₀, hc₀, hcross⟩ := SplitCrossDirect.splitCrossInput_direct (by omega : 7 ≤ e + 7)
    asymp rectangle hAr hS hC hSlab hKp arm second panis hslab hpioneer
  exact time_constant_from_cited_moment e he asymp rectangle reimer hC hAr hS hSlab hKp
    panis arm second hslab hpioneer hc₀ hK hCarm hcross hmoment hsize ordinary
    ha₁ ha₂ ha₃ hsum hc hcH hHMS M N hlimit hunit hreflect hGM

/-- Uniform diffusivity bounds with the variance defined by the Einstein relation. -/
theorem einsteinDiffusivity_two_sided_from_inputs (e : ℕ) (he : 2 ≤ e)
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
    (hθ : UpperPowerBound (criticalPoint (e+7):ℝ) (densityReal (e+7)) 1) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ p : unitInterval, criticalPoint (e + 7) < p →
      ∀ j : Fin (e + 7),
        c * ((p : ℝ) - (criticalPoint (e + 7) : ℝ)) ^ 2 ≤ einsteinDiffusivity (e + 7) j p ∧
        einsteinDiffusivity (e + 7) j p ≤ C * ((p : ℝ) - (criticalPoint (e + 7) : ℝ)) ^ 2 := by
  obtain ⟨cSlab, hSlab, hslab⟩ :=
    slab_first_moment_lower (by omega : 2 ≤ e + 7) hC hcPioneer panis hpioneerLower
  have hpc : 0 < (criticalPoint (e + 7) : ℝ) := External.criticalPoint_pos (by omega)
  let Kp := Pioneer / (criticalPoint (e + 7) : ℝ)
  have hKp : 0 < Kp := div_pos hPioneer hpc
  have hpioneer (i : Fin (e + 7)) (n : ℕ) :
      halfSpacePioneerMass (criticalPoint (e + 7)) i (n : ℤ) ≤ ENNReal.ofReal Kp :=
    halfSpace_pioneer_uniform_of_positive_heights _ i hpc hPioneer.le (hpioneerUpper i) n
  have hS : 0 ≤ 2 * Kp ^ 3 := by positivity
  have second (i : Fin (e + 7)) : SlabBoundarySecondMomentUpper i (2 * Kp ^ 3) :=
    slabBoundarySecondMomentUpper_of_pioneerMass i hKp.le (hpioneer i)
  obtain ⟨c₀, hc₀, hcross⟩ := SplitCrossDirect.splitCrossInput_direct (by omega : 7 ≤ e + 7)
    asymp rectangle hAr hS hC hSlab hKp arm second panis hslab hpioneer
  obtain ⟨cl, Cu, hcl, hCu, hbounds⟩ :=
    einsteinDiffusivity_two_sided_from_cited_moment e he asymp rectangle reimer
      hC hAr hS hSlab hKp panis arm second hslab hpioneer hc₀ hK hCarm hcross
      hmoment hsize ordinary ha₁ ha₂ ha₃ hsum hc i hBX hbX pioneers
      δupper hδupper hδupper' hθ
  refine ⟨cl, Cu, hcl, hCu, ?_⟩
  intro p hp j
  simpa only [einsteinDiffusivity_axes i j p hp] using hbounds (p : ℝ) hp p.property.2

/-- The paper’s diffusivity bounds for the exponential-clock sample law. -/
theorem variableSpeedSamplePath_diffusivity_two_sided_from_inputs (e : ℕ) (he : 2 ≤ e)
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
    (hclock : ExponentialClockPoissonInput)
    (einstein : VariableSpeedSampleEinsteinInput (e+7)) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ p : unitInterval, criticalPoint (e+7) < p →
      ∃ v : ℝ≥0, (∀ j : Fin (e+7), VariableSpeedSampleGaussianMarginal (e+7) p j v) ∧
        c*((p:ℝ)-(criticalPoint (e+7):ℝ))^2 ≤ (v:ℝ) ∧
        (v:ℝ) ≤ C*((p:ℝ)-(criticalPoint (e+7):ℝ))^2 := by
  obtain ⟨cSlab, hSlab, hslab⟩ :=
    slab_first_moment_lower (by omega : 2 ≤ e + 7) hC hcPioneer panis hpioneerLower
  have hpc : 0 < (criticalPoint (e + 7) : ℝ) := External.criticalPoint_pos (by omega)
  let Kp := Pioneer / (criticalPoint (e + 7) : ℝ)
  have hKp : 0 < Kp := div_pos hPioneer hpc
  have hpioneer (i : Fin (e + 7)) (n : ℕ) :
      halfSpacePioneerMass (criticalPoint (e + 7)) i (n : ℤ) ≤ ENNReal.ofReal Kp :=
    halfSpace_pioneer_uniform_of_positive_heights _ i hpc hPioneer.le (hpioneerUpper i) n
  have hS : 0 ≤ 2 * Kp ^ 3 := by positivity
  have second (i : Fin (e + 7)) : SlabBoundarySecondMomentUpper i (2 * Kp ^ 3) :=
    slabBoundarySecondMomentUpper_of_pioneerMass i hKp.le (hpioneer i)
  obtain ⟨c₀, hc₀, hcross⟩ := SplitCrossDirect.splitCrossInput_direct (by omega : 7 ≤ e + 7)
    asymp rectangle hAr hS hC hSlab hKp arm second panis hslab hpioneer
  exact variableSpeedSamplePath_diffusivity_two_sided_from_cited_moment e he asymp rectangle reimer hC hAr hS hSlab hKp
    panis arm second hslab hpioneer hc₀ hK hCarm hcross hmoment hsize ordinary
    ha₁ ha₂ ha₃ hsum hc i hBX hbX pioneers
    δupper hδupper hδupper' hθ hclock einstein

end NearCritical
