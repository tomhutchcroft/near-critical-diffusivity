import NearCritical.MainTheoremsFromLiterature
import NearCritical.HalfSpaceLongPathMoment

/-!
`thm.slab` and `thm.time_constant` with the far-face tail replaced by the cited
moment bound itself (`Section7.HalfSpaceLongPathMoment`, CHS23 (105)); the
Markov step is `Section7.halfSpaceLongPathTail_of_moment`. Otherwise identical
to `MainTheoremsFromLiterature.lean`. No new mathematics.
-/

namespace NearCritical
open Set MeasureTheory ProbabilityTheory Section8 Section10
open scoped Classical ENNReal

/-- **`thm.slab`, `d ≥ 9`, from cited statements**: as
`slab_theorem_from_cited_estimates`, with the far-face tail replaced by the
cited moment bound CHS23 (105) and the planar input in the cited Grimmett form. -/
theorem slab_theorem_from_cited_moment (e : ℕ) (he : 2 ≤ e)
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
  obtain ⟨η, hη, κ, hκprob, hκ, θ, hθ0, hθ⟩ := exists_planar_law planar
  exact slab_theorem_from_cited_estimates e he asymp rectangle reimer hC hAr hS hSlab hPioneer
    panis arm second hslab hpioneer hc₀ hK hCarm hcross
    (Section7.faceReachTail_of_halfSpaceLongPath
      (Section7.halfSpaceLongPathTail_of_moment hK hmoment)) hsize ordinary ha₁ ha₂ ha₃ hsum hc
    hη κ hκ hθ0 hθ hCdec hcdec decay

/-- **`thm.time_constant`, `d ≥ 9`, from cited statements**: as
`time_constant_from_cited_estimates`, with the far-face tail replaced by the
cited moment bound CHS23 (105). -/
theorem time_constant_from_cited_moment (e : ℕ) (he : 2 ≤ e)
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
        M p ≤ Cu / Real.sqrt ((p : ℝ) - (criticalPoint (e + 7) : ℝ)) :=
  time_constant_from_cited_estimates e he asymp rectangle reimer hC hAr hS hSlab hPioneer
    panis arm second hslab hpioneer hc₀ hK hCarm hcross
    (Section7.faceReachTail_of_halfSpaceLongPath
      (Section7.halfSpaceLongPathTail_of_moment hK hmoment)) hsize ordinary ha₁ ha₂ ha₃ hsum hc
    hcH hHMS M N hlimit hunit hreflect hGM

end NearCritical
