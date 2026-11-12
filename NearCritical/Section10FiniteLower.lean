module

public import NearCritical.Section10ActualLower
public import NearCritical.Section10LowerScale

/-! Section10 eq.lowerObject: finite conductivity lower bound from actual flow
probability/energy estimates, including exact box-factor cancellation. Source
stochastic construction and infinite-volume identification remain separate. -/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open MeasureTheory
open scoped Classical

def cubeFlowNormalization (d r : ℕ) : ℝ :=
  (2*(r:ℝ)+1)^2/((centeredBox d r).card:ℝ)

/-- The actual base volume and squared face separation give a positive factor. -/
theorem cubeFlowNormalization_pos (d r : ℕ) : 0 < cubeFlowNormalization d r := by
  have hcard : 0 < ((centeredBox d r).card:ℝ) := by
    apply Nat.cast_pos.mpr
    apply Finset.card_pos.mpr
    refine ⟨0,mem_centeredBox.mpr ?_⟩
    intro j
    change -(r:ℤ) ≤ 0 ∧ 0 ≤ (r:ℤ)
    omega
  dsimp [cubeFlowNormalization]
  positivity

/-- Actual random supported flows and source probability/energy budgets imply
an actual annealed cube conductivity lower bound. The box factor cancels in
the proof, retaining exact issued boundary height and actual cube volume. -/
theorem annealed_cube_inverse_scale_lower {d r : ℕ} (i : Fin d) (p : unitInterval)
    (hp : criticalPoint d < p) {a C : ℝ} (ha : 0 < a) (hC : 0 < C)
    (θ : (IssuedBond (centeredBox d r) → Bool) → IssuedBond (centeredBox d r) → ℝ)
    (A : Set (IssuedBond (centeredBox d r) → Bool))
    (hflow : ∀ η ∈ A, Network.FlowSupported (cubeFlowWeights η) (θ η) ∧
      (issuedNetwork (centeredBox d r)).IsBoundaryUnitFlow
        (negativeFace (centeredBox d r) i) (positiveFace (centeredBox d r) i) (θ η))
    (hA : a ≤ (percolation d p).real (cubeFlowEvent (centeredBox d r) A))
    (henergy : (∫ ω, (if (issuedBondSet (centeredBox d r)).restrict ω ∈ A then
      cubeFlowEnergy (centeredBox d r) θ ((issuedBondSet (centeredBox d r)).restrict ω) else 0)
        ∂percolation d p) ≤ C*cubeFlowNormalization d r*(chemicalCorrelationScale d p:ℝ)^6) :
    a^2/(C*(chemicalCorrelationScale d p:ℝ)^6) ≤ annealedFull (centeredBox d r) i (p:ℝ) := by
  have hs := cubeFlowNormalization_pos d r
  have hstar : 0 < (chemicalCorrelationScale d p:ℝ) := by
    exact_mod_cast (show 0 < chemicalCorrelationScale d p by
      have h := chemicalCorrelationScale_pos p hp
      omega)
  have hK : 0 < C*cubeFlowNormalization d r*(chemicalCorrelationScale d p:ℝ)^6 := by positivity
  have hb := annealed_cube_lower_of_supported_flow i p θ A ha hK hflow hA henergy
  calc
    _ = (cubeFlowNormalization d r*a^2)/
        (C*cubeFlowNormalization d r*(chemicalCorrelationScale d p:ℝ)^6) := by
      field_simp [hC.ne',hs.ne',hstar.ne']
      <;> ring
    _ ≤ annealedFull (centeredBox d r) i (p:ℝ) := hb

/-- The cubic finite-volume rate is derived from the actual flow budgets and
the source floor scale; it is not an input to this reduction. -/
theorem annealed_cube_cubic_lower {d r : ℕ} (i : Fin d) (p : unitInterval)
    (hp : criticalPoint d < p) {a C : ℝ} (ha : 0 < a) (hC : 0 < C)
    (θ : (IssuedBond (centeredBox d r) → Bool) → IssuedBond (centeredBox d r) → ℝ)
    (A : Set (IssuedBond (centeredBox d r) → Bool))
    (hflow : ∀ η ∈ A, Network.FlowSupported (cubeFlowWeights η) (θ η) ∧
      (issuedNetwork (centeredBox d r)).IsBoundaryUnitFlow
        (negativeFace (centeredBox d r) i) (positiveFace (centeredBox d r) i) (θ η))
    (hA : a ≤ (percolation d p).real (cubeFlowEvent (centeredBox d r) A))
    (henergy : (∫ ω, (if (issuedBondSet (centeredBox d r)).restrict ω ∈ A then
      cubeFlowEnergy (centeredBox d r) θ ((issuedBondSet (centeredBox d r)).restrict ω) else 0)
        ∂percolation d p) ≤ C*cubeFlowNormalization d r*(chemicalCorrelationScale d p:ℝ)^6) :
    (a^2/C)*((p:ℝ)-(criticalPoint d:ℝ))^3 ≤ annealedFull (centeredBox d r) i (p:ℝ) := by
  have hb := annealed_cube_inverse_scale_lower i p hp ha hC θ A hflow hA henergy
  apply cubic_lower_of_inverse_scale_bound p hp (div_nonneg (sq_nonneg _) hC.le)
  simpa only [div_div] using hb

end NearCritical.Section10
