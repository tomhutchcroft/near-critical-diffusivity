module

public import NearCritical.Section10FiniteLower
public import NearCritical.ChemicalCoarseBox
public import Mathlib.Topology.Order.OrderClosed

/-! Section10 final limiting deduction along the actual supplied source box
sequence. The literal convergence is an explicit STANDARD homogenization
obligation; actual flow budgets remain NEW construction obligations. -/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open MeasureTheory Filter
open scoped Classical Topology

/-- Raw source reduction data on an actual issued cube. No conductivity bound
is part of this predicate: only a supported unit flow, event mass and energy. -/
def cubeFlowBudget {d : ℕ} (p : unitInterval) (i : Fin d) (r : ℕ) (a C : ℝ) : Prop :=
  ∃ (θ : (IssuedBond (centeredBox d r) → Bool) → IssuedBond (centeredBox d r) → ℝ)
    (A : Set (IssuedBond (centeredBox d r) → Bool)),
    (∀ η ∈ A, Network.FlowSupported (cubeFlowWeights η) (θ η) ∧
      (issuedNetwork (centeredBox d r)).IsBoundaryUnitFlow
        (negativeFace (centeredBox d r) i) (positiveFace (centeredBox d r) i) (θ η)) ∧
    a ≤ (percolation d p).real (cubeFlowEvent (centeredBox d r) A) ∧
    (∫ ω, (if (issuedBondSet (centeredBox d r)).restrict ω ∈ A then
      cubeFlowEnergy (centeredBox d r) θ ((issuedBondSet (centeredBox d r)).restrict ω) else 0)
        ∂percolation d p) ≤ C*cubeFlowNormalization d r*(chemicalCorrelationScale d p:ℝ)^6

/-- The actual affine source radius diverges with M; no arbitrary-sequence
limit is silently inferred from the existing triadic convergence interface. -/
theorem chemicalCoarseRadius_tendsto {t : ℕ} (ht : 1 ≤ t) (r : ℕ) :
    Tendsto (fun M : ℕ => chemicalCoarseRadius M t r) atTop atTop := by
  have hb (M : ℕ) : M ≤ chemicalCoarseRadius M t r+1 := by
    have hm : M-1 ≤ (M-1)*t := by
      have h := Nat.mul_le_mul_left (M-1) ht
      simpa only [Nat.mul_one] using h
    dsimp [chemicalCoarseRadius]
    omega
  apply tendsto_atTop.2
  intro b
  filter_upwards [eventually_ge_atTop (b+1)] with M hM
  have h := hb M
  omega

/-- The raw flow budget gives an actual finite cubic conductivity bound. -/
theorem annealed_cube_cubic_lower_of_budget {d : ℕ} (p : unitInterval) (i : Fin d)
    (hp : criticalPoint d < p) (r : ℕ) {a C : ℝ} (ha : 0 < a) (hC : 0 < C)
    (hbudget : cubeFlowBudget p i r a C) :
    (a^2/C)*((p:ℝ)-(criticalPoint d:ℝ))^3 ≤ annealedFull (centeredBox d r) i (p:ℝ) := by
  obtain ⟨θ,A,hflow,hA,henergy⟩ := hbudget
  exact annealed_cube_cubic_lower i p hp ha hC θ A hflow hA henergy

/-- Final source limiting deduction from actual means and eventual RAW flow
budgets on the SAME sequence. The coefficient is supplied, not redefined; no
desired coefficient lower bound or stronger all-radii flow theorem is assumed. -/
theorem coefficient_cubic_lower_of_flow_budgets {d : ℕ} (p : unitInterval) (i : Fin d)
    (hp : criticalPoint d < p) (radii : ℕ → ℕ) {κ a C : ℝ} (ha : 0 < a) (hC : 0 < C)
    (hlimit : Tendsto (fun M : ℕ => annealedFull (centeredBox d (radii M)) i (p:ℝ)) atTop (𝓝 κ))
    (hbudget : ∀ᶠ M : ℕ in atTop, cubeFlowBudget p i (radii M) a C) :
    (a^2/C)*((p:ℝ)-(criticalPoint d:ℝ))^3 ≤ κ := by
  apply ge_of_tendsto hlimit
  exact hbudget.mono (fun M hM => annealed_cube_cubic_lower_of_budget p i hp (radii M) ha hC hM)

end NearCritical.Section10
