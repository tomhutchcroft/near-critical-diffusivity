module

public import NearCritical.Section10MarkCard
public import NearCritical.Section10MarkHitting
public import NearCritical.Section10MarkedConditionalMeans
public import NearCritical.Section10MarkedConditionalVariance

/-! Assemble the exact moment hypothesis used by the pre-good cube theorem. -/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open NearCritical.Section8 AppendixVariance MeasureTheory
open scoped Classical

/-- The marked moment package for a fixed regularity tolerance. The
variance coefficient is fixed before choosing the cutoff, and the cube
threshold may depend on that cutoff. -/
theorem marked_moment_package_of_box_lower (e : ℕ) (he : 2 ≤ e)
    (asymp : TwoPointAsymptotics (e + 7)) (C B S A : ℝ)
    (hC : 0 ≤ C) (hB : 0 ≤ B) (hS : 0 ≤ S) (hA : 1 ≤ A)
    (panis : PanisHalfSpaceTwoPointUpper (e + 7) C)
    (arm : ∀ i : Fin (e + 7), HalfSpaceCriticalArmInput i B)
    (second : ∀ i : Fin (e + 7), SlabBoundarySecondMomentUpper i S)
    (ordinary : OrdinaryArmWindowInput (e + 7) A) (c : ℝ) (hc : 0 < c)
    (hbox : ∀ (i : Fin (e + 7)) (R : ℕ) (x : Vertex (e + 7)), 1 ≤ R →
      (x i = -(R : ℤ) ∨ x i = (R : ℤ)) →
      (∀ j, j ≠ i → |(x j : ℝ)| ≤ (R : ℝ) - (1 / 2 : ℝ) * (R : ℝ)) →
      ∀ y ∈ centeredBox (e + 7) R, R ≤ 2 * (R - linfDist 0 y) →
        c / (R : ℝ) ^ (e + 6) ≤ (percolation (e + 7) (criticalPoint (e + 7))).real
          (connectionToSetEvent (centeredBox (e + 7) R : Set (Vertex (e + 7))) x {y}))
    (δ : ℝ) (hδ : 0 < δ) :
    let d := e + 7
    ∃ cc : ℝ, 0 < cc ∧ cc ≤ 1 / 16 ∧ ∃ Cm Cp Cb : ℝ, 0 ≤ Cm ∧ 0 ≤ Cp ∧ 0 ≤ Cb ∧
      ∃ rstar : ℕ, ∀ typ : TypicalParameters, typ.heartRatio = cc →
        typ.regularTolerance = δ → rstar ≤ typ.regularRadius →
        ∃ t₁ : ℕ, ∀ t : ℕ, t₁ ≤ t →
          (∀ x ∈ typMark t (0 : Vertex d),
            heartConditionalMean (criticalPoint d) (typicalCube t 0) (typicalHeart t 0 typ.heartRatio)
              (fun F => regularityEnergyOne F (typicalInnerCube t 0) typ.regularRadius x) x ≤
              typ.regularTolerance / 2) ∧
          (∀ x ∈ typMark t (0 : Vertex d),
            heartConditionalMean (criticalPoint d) (typicalCube t 0) (typicalHeart t 0 typ.heartRatio)
              (fun F => regularityEnergyTwo F (typicalBoundary t 0) typ.regularRadius x) x ≤
              typ.regularTolerance / 2) ∧
          (∀ x ∈ typMark t (0 : Vertex d),
            heartCenteredMoment (criticalPoint d) (typicalCube t 0) (typicalHeart t 0 typ.heartRatio)
              (fun F => regularityEnergyOne F (typicalInnerCube t 0) typ.regularRadius x) x +
            heartCenteredMoment (criticalPoint d) (typicalCube t 0) (typicalHeart t 0 typ.heartRatio)
              (fun F => regularityEnergyTwo F (typicalBoundary t 0) typ.regularRadius x) x ≤
              (Cm / (typ.regularRadius : ℝ) ^ (d - 6)) * (percolation d (criticalPoint d)).real
                {ω | x ∈ heartClusterUnion ω (typicalCube t 0) (typicalHeart t 0 typ.heartRatio)}) ∧
          (∀ x ∈ typMark t (0 : Vertex d), (percolation d (criticalPoint d)).real
            {ω | x ∈ heartClusterUnion ω (typicalCube t 0) (typicalHeart t 0 typ.heartRatio)} ≤
              Cp / (2 * (t : ℝ)) ^ 3) ∧
          (((typMark t (0 : Vertex d)).card : ℝ) ≤ Cb * (2 * (t : ℝ)) ^ (d - 1)) := by
  intro d
  obtain ⟨cc, hcc, hcc1, rstar, tm, hrstar, htm, hmeans⟩ :=
    marked_conditional_means_of_box_lower e he asymp C B S A hC hB hS hA
      panis arm second ordinary c hc hbox (δ / 2) (by positivity)
  obtain ⟨Cm, hCm, hvariance⟩ :=
    marked_conditional_variance_of_box_lower e he asymp C B S A hC hB hS hA
      panis arm second ordinary c hc hbox cc hcc hcc1
  let Cp := 512 * ((2 * C) * 2 ^ (d - 1) * B * (2 * (d : ℝ) * 5 ^ (d - 1)))
  let Cb := 2 * (d : ℝ)
  have hcc' : cc ≤ 1 / 16 := hcc1.trans (by norm_num)
  refine ⟨cc, hcc, hcc', Cm, Cp, Cb, hCm, by dsimp [Cp]; positivity,
    by dsimp [Cb]; positivity, rstar, ?_⟩
  intro typ hratio htol hr
  obtain ⟨tv, htv⟩ := hvariance typ.regularRadius (hrstar.trans hr)
  refine ⟨max tm tv, fun t ht => ?_⟩
  have hmt : tm ≤ t := (le_max_left _ _).trans ht
  have hvt : tv ≤ t := (le_max_right _ _).trans ht
  have ht64 : 64 ≤ t := htm.trans hmt
  refine ⟨fun x hx => ?_, fun x hx => ?_, fun x hx => ?_, fun x hx => ?_,
    typMark_card_le t (by omega)⟩
  · rw [hratio, htol]
    exact (hmeans typ.regularRadius hr t hmt x hx).1
  · rw [hratio, htol]
    exact (hmeans typ.regularRadius hr t hmt x hx).2
  · rw [hratio]
    exact htv t hvt x hx
  · rw [hratio]
    exact typMark_hit_le (show 4 ≤ d by dsimp [d]; omega) t ht64 hcc' hC hB panis arm hx

end NearCritical.Section10
