import NearCritical.Section10NearTranslatedBudget
import NearCritical.DiffusivityFromTranslatedBudgets
import NearCritical.MainTheoremsFromCitedMoment
import Mathlib.Logic.Encodable.Pi
import Mathlib.Logic.Equiv.Finset

noncomputable section

namespace NearCritical

open Set MeasureTheory Filter Section8 Section10
open scoped Classical ENNReal

/-- The limiting conductivity coefficient is independent of the
coordinate direction by permutation symmetry of the finite cubes. -/
theorem fullCubeLimit_axes {d : ℕ} (i j : Fin d) (p : unitInterval) (hp : criticalPoint d < p) :
    fullCubeLimit d i p = fullCubeLimit d j p := by
  have hi := annealedFull_centeredBox_tendsto i (triadicDirichletLimitInput_fullCubeLimit d i) p hp
  have hj := annealedFull_centeredBox_tendsto j (triadicDirichletLimitInput_fullCubeLimit d j) p hp
  have he : (fun r => annealedFull (centeredBox d r) i p) =
      fun r => annealedFull (centeredBox d r) j p :=
    funext fun r => annealedFull_centeredBox_axis r i j p
  rw [he] at hi
  exact tendsto_nhds_unique hi hj

theorem einsteinDiffusivity_axes {d : ℕ} (i j : Fin d) (p : unitInterval) (hp : criticalPoint d < p) :
    einsteinDiffusivity d i p = einsteinDiffusivity d j p := by
  unfold einsteinDiffusivity
  rw [fullCubeLimit_axes i j p hp]

/-- The two-sided diffusivity bound for the Einstein-relation
coefficient. The lower bound uses the actual Section 10 issued flows,
and the typicality inputs are discharged by the same marked moments
as in the slab and time-constant results. -/
theorem einsteinDiffusivity_two_sided_from_cited_moment (e : ℕ) (he : 2 ≤ e)
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
    (hθ : UpperPowerBound (criticalPoint (e+7):ℝ) (densityReal (e+7)) 1) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ p : ℝ, (criticalPoint (e+7):ℝ) < p → p ≤ 1 →
      c*(p-(criticalPoint (e+7):ℝ))^2 ≤ einsteinDiffusivity (e+7) i p ∧
        einsteinDiffusivity (e+7) i p ≤ C*(p-(criticalPoint (e+7):ℝ))^2 := by
  letI : LinearOrder (Finset (Vertex (e+7))) :=
    LinearOrder.lift' (Encodable.encode : Finset (Vertex (e+7)) → ℕ) Encodable.encode_injective
  obtain ⟨amp,δ,hamp,hδ,hBuild⟩ :=
    near_translated_budgets_of_pregood (e+1) (by omega) asymp rectangle reimer
  obtain ⟨b,hb,hbox⟩ := marked_box_lower_from_pioneers e asymp rectangle hAr hS hC hSlab hPioneer
    arm second panis hslab hpioneer
  have ordinary' : OrdinaryArmWindowInput (e+7) (max 1 Carm) := by
    intro p x n hn hp
    exact (ordinary p x n hn hp).trans (div_le_div_of_nonneg_right (le_max_right _ _) (by positivity))
  have hmom := marked_moment_package_of_box_lower e he asymp C Ar S (max 1 Carm)
    hC hAr hS (le_max_left _ _) panis arm second ordinary' b hb hbox δ hδ
  have hBm := boxFaceFirstMoment_of_pioneerMass hPioneer.le hpioneer
  have hTail := Section7.faceReachTail_of_halfSpaceLongPath
    (Section7.halfSpaceLongPathTail_of_moment hK hmoment)
  have hamp₀ := zero_lt_one.trans hamp
  obtain ⟨typ,κ,t₀,hrad,htol,hbL,hcL,hbU,hcU,hdU,hκ,hκq,hpre⟩ :=
    pregood_hypothesis_of_moments (d := e+7) (by omega) asymp hc₀ hK hPioneer.le hCarm
      hcross hTail hBm hsize ordinary ha₁.le ha₂.le ha₃.le hsum hc ha₁ ha₂ ha₃
      (inv_pos.mpr hamp₀) (inv_lt_one_of_one_lt₀ hamp) hδ hmom
  have hκamp : κ^2 < amp := by
    have h : κ^2 / amp < 1 := by simpa only [div_eq_mul_inv] using hκq
    simpa only [one_mul] using (div_lt_iff₀ hamp₀).mp h
  have hbudget := hBuild typ hrad htol hbL hcL hbU hcU hdU κ hκ hκamp t₀
    (fun t ht a => hpre t ht (coarseCenter t a))
  have hpc1 := criticalPoint_lt_one_of_twoPointAsymptotics (by omega) i asymp
  exact einsteinDiffusivity_two_sided_of_near_translatedBudgets i 0 hBX hbX hCarm.le
    hpc1 pioneers ordinary δupper hδupper hδupper' hθ hbudget

end NearCritical
