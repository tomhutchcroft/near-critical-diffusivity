module

public import NearCritical.ChemicalUpperBound
public import NearCritical.ChemicalTimeConstantMonotonicity

/-! The full-parameter assembly of source prop.chem.upper. Standard time-constant,
norm and GM inputs and the unresolved NEW short-crossing probability input are
visible. The uniform constant and the macroscopic extension are proved. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Set MeasureTheory Filter
open scoped Topology

/-- Source prop.chem.upper, conditional on the explicit paper crossing input and
named standard shape/norm/GM inputs. The constant is uniform in p; the proof does
not assume either a near-critical or a global time-constant bound. -/
theorem chemical_timeConstant_upper_uniform {d : ℕ} (i : Fin d)
    (M : unitInterval → ℝ) (N : unitInterval → Seminorm ℝ (Fin d → ℝ))
    (p₁ : unitInterval) (h₁ : criticalPoint d < p₁) {C c : ℝ} (hC : 0 ≤ C) (hc : 0 < c)
    (huniq : ∀ p : unitInterval, criticalPoint d < p → AEInfiniteClusterUniqueness d p)
    (hlimit : ∀ p : unitInterval, criticalPoint d < p →
      AEConnectedChemicalLimit d p (Pi.single i 1) (M p))
    (hunit : ∀ p : unitInterval, criticalPoint d < p → ∀ j, (N p) (Pi.single j 1) = 1)
    (hreflect : ∀ p : unitInterval, criticalPoint d < p → ∀ j x,
      (N p) (coordinateReflection j x) = (N p) x)
    (hGM : ∀ p : unitInterval, criticalPoint d < p → ∀ ε : ℝ, ε ∈ Ioo 0 1 →
      ∃ B : ℝ, 0 < B ∧ ∃ R : ℝ, UniformChemicalLowerTail d p (N p) (M p) ε B R)
    (scales : unitInterval → ℕ → ℕ)
    (hscales : ∀ p : unitInterval, criticalPoint d < p → p ≤ p₁ →
      Tendsto (scales p) atTop atTop)
    (hcross : ∀ p : unitInterval, criticalPoint d < p → p ≤ p₁ → ∀ᶠ n : ℕ in atTop,
      c ≤ (percolation d p).real (chemicalSpanEvent i (scales p n)
        (C * (chemicalCorrelationScale d p : ℝ)))) :
    ∃ K : ℝ, 0 < K ∧ ∀ p : unitInterval, criticalPoint d < p →
      M p ≤ K / Real.sqrt ((p : ℝ) - (criticalPoint d : ℝ)) := by
  let K := max (2 * C) (|M p₁| + 1)
  have hKpos : 0 < K := lt_of_lt_of_le (by positivity : 0 < |M p₁| + 1) (le_max_right _ _)
  refine ⟨K, hKpos, ?_⟩
  intro p hp
  by_cases hpp₁ : p ≤ p₁
  · have hcross' : ∀ᶠ n : ℕ in atTop,
        c ≤ (percolation d p).real (chemicalShortCrossingEvent i (scales p n)
          (C * (chemicalCorrelationScale d p : ℝ))) := by
      simpa only [chemicalShortCrossingEvent_eq_span] using hcross p hp hpp₁
    have hnear := chemical_timeConstant_upper_near_critical p i (N p)
      (hunit p hp) (hreflect p hp) (μ := M p) hC hc (scales p)
      (hscales p hp hpp₁) hcross' (hGM p hp)
    exact hnear.trans (div_le_div_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _))
  · have hmac := chemical_timeConstant_upper_macroscopic p₁ p h₁ (le_of_not_ge hpp₁)
      (Pi.single i 1) (huniq p₁ h₁) (hlimit p₁ h₁) (hlimit p hp)
    exact hmac.trans (div_le_div_of_nonneg_right (le_max_right _ _) (Real.sqrt_nonneg _))

end NearCritical
