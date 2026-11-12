module

public import NearCritical.Section10CoupledLower
public import NearCritical.Section10FiniteLower

/-! Cubic conductivity lower bound from a flow on the coupled law
(`eq.lowerObject` of the proof of `prop.lower`).

`annealed_cube_cubic_lower_coupled`: for `p = p0 OR q > p_c`, if a flow and an
event depending on the configuration pair through finitely many layered bonds
satisfy `P[event] >= a` and
`E[energy; event] <= C * (2r+1)^2/|box| * l_*(p)^6`, then

  `(a^2 / C) (p - p_c)^3 <= annealedFull(box, p)`.

This is `annealed_cube_cubic_lower` with the flow allowed to depend on both
layers, which is what the Section 10 construction provides.
-/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open MeasureTheory
open scoped Classical BigOperators

theorem annealed_cube_cubic_lower_coupled {d r : ℕ} (i : Fin d) (p0 q : unitInterval)
    (hp : criticalPoint d < orParameter p0 q) {a C : ℝ} (ha : 0 < a) (hC : 0 < C)
    (R : Finset (LBond d))
    (orb : (R → Bool) → IssuedBond (centeredBox d r) → Bool)
    (horb : ∀ z : Configuration d × Configuration d, orb (R.restrict (layerVal z)) =
      (issuedBondSet (centeredBox d r)).restrict (sprinkleOrConfiguration z.1 z.2))
    (θ : (R → Bool) → IssuedBond (centeredBox d r) → ℝ) (A : Set (R → Bool))
    (hflow : ∀ b ∈ A, Network.FlowSupported (cubeFlowWeights (orb b)) (θ b) ∧
      (issuedNetwork (centeredBox d r)).IsBoundaryUnitFlow
        (negativeFace (centeredBox d r) i) (positiveFace (centeredBox d r) i) (θ b))
    (hA : a ≤ ∫ z : Configuration d × Configuration d,
      (if R.restrict (layerVal z) ∈ A then (1:ℝ) else 0)
        ∂((percolation d p0).prod (percolation d q)))
    (henergy : (∫ z : Configuration d × Configuration d,
      (if R.restrict (layerVal z) ∈ A then
        Network.flowEnergy (cubeFlowWeights (orb (R.restrict (layerVal z))))
          (θ (R.restrict (layerVal z))) else 0)
        ∂((percolation d p0).prod (percolation d q))) ≤
      C * cubeFlowNormalization d r *
        (chemicalCorrelationScale d (orParameter p0 q) : ℝ) ^ 6) :
    (a^2/C) * (((orParameter p0 q : unitInterval) : ℝ) - (criticalPoint d : ℝ))^3 ≤
      annealedFull (centeredBox d r) i ((orParameter p0 q : unitInterval) : ℝ) := by
  have hs := cubeFlowNormalization_pos d r
  have hstar : 0 < (chemicalCorrelationScale d (orParameter p0 q) : ℝ) := by
    exact_mod_cast (show 0 < chemicalCorrelationScale d (orParameter p0 q) by
      have h := chemicalCorrelationScale_pos (orParameter p0 q) hp
      omega)
  have hK : 0 < C * cubeFlowNormalization d r *
      (chemicalCorrelationScale d (orParameter p0 q) : ℝ) ^ 6 := by positivity
  have hb := annealed_cube_lower_coupled i p0 q R orb horb θ A ha hK hflow hA henergy
  have hinv : a^2/(C * (chemicalCorrelationScale d (orParameter p0 q) : ℝ)^6) ≤
      annealedFull (centeredBox d r) i ((orParameter p0 q : unitInterval) : ℝ) := by
    calc a^2/(C * (chemicalCorrelationScale d (orParameter p0 q) : ℝ)^6)
        = (cubeFlowNormalization d r * a^2) /
          (C * cubeFlowNormalization d r *
            (chemicalCorrelationScale d (orParameter p0 q) : ℝ)^6) := by
          field_simp [hC.ne', hs.ne', hstar.ne']
      _ ≤ _ := hb
  apply cubic_lower_of_inverse_scale_bound (orParameter p0 q) hp (div_nonneg (sq_nonneg _) hC.le)
  simpa only [div_div] using hinv

end NearCritical.Section10
