import NearCritical.AppendixBoxWideFinal
import NearCritical.Section10BoxFaceFromPioneer
import NearCritical.Section10MarkedMomentPackage
import NearCritical.TimeConstantFromMoments

/-! The time-constant theorem with the internal marked moment and box
lower-bound hypotheses discharged. -/
noncomputable section
namespace NearCritical
open Set MeasureTheory Section8 Section10
open scoped Classical ENNReal

/-- The two-sided time-constant estimate from the cited percolation and
chemical-distance inputs. -/
theorem time_constant_from_cited_estimates (e : ℕ) (he : 2 ≤ e)
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
  obtain ⟨_, _, _, δ, hδ, hcap⟩ := time_constant_of_moments (e + 1) (by omega) (d := e + 7)
    (by omega) asymp rectangle reimer
  obtain ⟨b, hb, hbox⟩ := marked_box_lower_from_pioneers e asymp rectangle hAr hS hC hSlab hPioneer
    arm second panis hslab hpioneer
  have ordinary' : OrdinaryArmWindowInput (e + 7) (max 1 Carm) := by
    intro p x n hn hp
    exact (ordinary p x n hn hp).trans (div_le_div_of_nonneg_right (le_max_right _ _) (by positivity))
  have hmom := marked_moment_package_of_box_lower e he asymp C Ar S (max 1 Carm)
    hC hAr hS (le_max_left _ _) panis arm second ordinary' b hb hbox δ hδ
  have hBm := boxFaceFirstMoment_of_pioneerMass hPioneer.le hpioneer
  exact hcap hc₀ hK hPioneer.le hCarm hcross htail hBm hsize ordinary ha₁.le ha₂.le ha₃.le hsum hc
    ha₁ ha₂ ha₃ hmom hcH hHMS M N hlimit hunit hreflect hGM

end NearCritical
