module

public import NearCritical.CriticalPointInterior
public import NearCritical.ExternalHalfSpaceEntropicInput
public import NearCritical.HalfSpaceOneArmExtension

@[expose] public section
namespace NearCritical

/-- The finite half-space entropic comparison follows from the actual model
and assumption (A) in dimensions greater than two. -/
theorem finiteHalfSpaceEntropicInput_of_twoPointAsymptotics {d : ℕ}
    (hd : 2 < d) (i : Fin d) (h : TwoPointAsymptotics d) :
    ∃ E : ℝ, 0 < E ∧ FiniteHalfSpaceEntropicInput i E := by
  obtain ⟨hpc, hpc1⟩ := criticalPoint_interior_of_twoPointAsymptotics hd i h
  exact External.finiteHalfSpaceEntropicInput_of_pc_interior i hpc hpc1

/-- Under (A), the half-space extension needs only the two explicit arm
and pioneer estimates. The entropic comparison is supplied by the model. -/
theorem halfSpace_onearm_extension_of_twoPointAsymptotics {d : ℕ} (i : Fin d)
    (hd : 2 < d) (h : TwoPointAsymptotics d)
    {A B b : ℝ} (hA : 0 < A) (hB : 0 < B) (hb : 0 < b)
    (criticalArm : HalfSpaceCriticalArmInput i A)
    (pioneers : HalfSpacePioneerExponentialInput i B b) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (p : unitInterval) (k n : ℕ), 1 ≤ n → 2*k ≤ n →
      ((criticalPoint d : ℝ) < (p : ℝ) →
        (p : ℝ) ≤ (criticalPoint d : ℝ) + ((n : ℝ)^2)⁻¹ →
        (percolation d p).real (halfSpaceArmEvent i k n) ≤ C*((k+1 : ℝ)/(n : ℝ)^3)) ∧
      (p ≤ criticalPoint d →
        (percolation d p).real (halfSpaceArmEvent i k n) ≤ C*((k+1 : ℝ)/(n : ℝ)^3) *
          Real.exp (-c*Real.sqrt ((criticalPoint d : ℝ)-(p : ℝ))*(n : ℝ))) := by
  obtain ⟨hpc, hpc1⟩ := criticalPoint_interior_of_twoPointAsymptotics hd i h
  obtain ⟨E, hE, hEntropy⟩ := finiteHalfSpaceEntropicInput_of_twoPointAsymptotics hd i h
  exact halfSpace_onearm_extension_of_standard_inputs i hE hA hB hb hpc hpc1
    criticalArm pioneers hEntropy

end NearCritical
