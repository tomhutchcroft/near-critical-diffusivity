module

public import NearCritical.ChemicalLowerBound
public import NearCritical.ChemicalUpperGlobal

/-! Conditional assembly of source thm.time_constant (main.tex 454):
`c(p-p_c)^{-1/2} ≤ μ(p) ≤ C(p-p_c)^{-1/2}` for every `p_c < p ≤ 1`.

This combines the verified `chemical_timeConstant_lower_uniform` (prop.chem.lower) and
`chemical_timeConstant_upper_uniform` (prop.chem.upper), with one constant on each side,
uniform in `p`.

STATUS: CONDITIONAL. Every input of the two halves stays an explicit hypothesis:
* `p_c > 0`;
* the uniform HMS ray decay below `p_c` (`hHMS`);
* a.s. uniqueness of the infinite cluster and existence of the chemical time constant
  (`huniq`, `hlimit`);
* the norm and Garet–Marchand lower-tail inputs (`hunit`, `hreflect`, `hGM`);
* the paper's short-crossing probability input `hcross` (lem.chem.crossing).
`ChemicalCrossingAssembly` reduces `hcross` to an actual chain-certificate event, but the
surviving-chain extraction behind it is still open. This is therefore NOT a proof of
thm.time_constant and must not be counted as a main theorem. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Set MeasureTheory Filter

theorem time_constant_sandwich_conditional {d : ℕ} (i : Fin d)
    (hpc : 0 < (criticalPoint d : ℝ))
    -- lower-bound inputs (prop.chem.lower)
    {cH CH : ℝ} (hcH : 0 < cH)
    (hHMS : ∀ q : unitInterval, 0 < (q : ℝ) → (q : ℝ) ≤ (criticalPoint d : ℝ) →
      RayExponentialConnectionBound d q (Pi.single i 1) CH
        (cH * Real.sqrt ((criticalPoint d : ℝ) - (q : ℝ))))
    -- shared standard inputs
    (M : unitInterval → ℝ) (N : unitInterval → Seminorm ℝ (Fin d → ℝ))
    (huniq : ∀ p : unitInterval, criticalPoint d < p → AEInfiniteClusterUniqueness d p)
    (hlimit : ∀ p : unitInterval, criticalPoint d < p →
      AEConnectedChemicalLimit d p (Pi.single i 1) (M p))
    -- upper-bound inputs (prop.chem.upper)
    (p₁ : unitInterval) (h₁ : criticalPoint d < p₁) {C c : ℝ} (hC : 0 ≤ C) (hc : 0 < c)
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
    ∃ cl Cu : ℝ, 0 < cl ∧ 0 < Cu ∧ ∀ p : unitInterval, criticalPoint d < p →
      cl / Real.sqrt ((p : ℝ) - (criticalPoint d : ℝ)) ≤ M p ∧
        M p ≤ Cu / Real.sqrt ((p : ℝ) - (criticalPoint d : ℝ)) := by
  obtain ⟨K, hK, hup⟩ := chemical_timeConstant_upper_uniform i M N p₁ h₁ hC hc huniq hlimit
    hunit hreflect hGM scales hscales hcross
  refine ⟨min (Real.sqrt ((criticalPoint d : ℝ) / 2)) (cH * (criticalPoint d : ℝ) / 8), K,
    chemical_lower_constant_pos hpc hcH, hK, fun p hp => ⟨?_, hup p hp⟩⟩
  exact chemical_timeConstant_lower_uniform i hpc hcH hHMS p hp (huniq p hp) (hlimit p hp)

end NearCritical
