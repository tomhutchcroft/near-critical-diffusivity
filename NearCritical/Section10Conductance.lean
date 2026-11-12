module

public import NearCritical.Section10Thomson
public import NearCritical.LatticeFullConductivity
public import NearCritical.WaterCube

/-! Section10 final deterministic reduction for the ACTUAL full-Dirichlet
conductivity. No minimizer-existence or resistance-comparison premise. -/
@[expose] public section
noncomputable section
namespace NearCritical
open scoped Classical BigOperators

namespace Network
variable {V E : Type*} [Fintype V] [Fintype E]

lemma energy_sub_constant (G : Network V E) (a : E → ℝ) (u : V → ℝ) (c : ℝ) :
    G.energy a (fun v => u v-c) = G.energy a u := by
  unfold energy gradient
  apply Finset.sum_congr rfl
  intro e _he
  ring

/-- The minimizer is constructed internally. Only actual unit flux, closed-edge
support and boundary-data constants are supplied, not a conductivity estimate. -/
theorem conductance_ge_boundary_unit_flow (G : Network V E)
    (a θ : E → ℝ) (ha : ∀ e, 0 ≤ a e) (hsupport : FlowSupported a θ)
    (boundary S T : Set V) (data : V → ℝ)
    (hS : S ⊆ boundary) (hT : T ⊆ boundary)
    (hθ : G.IsBoundaryUnitFlow S T θ) (c H : ℝ) (hH : H ≠ 0)
    (hdataS : ∀ v ∈ S, data v = c) (hdataT : ∀ v ∈ T, data v = c+H) :
    0 < flowEnergy a θ ∧ H^2/flowEnergy a θ ≤ G.conductance a boundary data := by
  let u := G.minimizer ha boundary data
  have hu := G.minimizer_spec ha boundary data
  have hs (v : V) (hv : v ∈ S) : u v-c = 0 := by
    dsimp [u]
    rw [hu.1 v (hS hv),hdataS v hv,sub_self]
  have ht (v : V) (hv : v ∈ T) : u v-c = H := by
    dsimp [u]
    rw [hu.1 v (hT hv),hdataT v hv]
    ring
  have hb := G.boundary_unit_flow_energy_div_lower S T a θ ha hsupport hθ
    (fun v => u v-c) H hH hs ht
  rw [energy_sub_constant] at hb
  rw [G.conductance_eq_energy_minimizer ha boundary data]
  exact hb

end Network

/-- The ACTUAL issued-network full conductivity of an odd-side centered cube
is bounded below by its squared face separation divided by supported unit-flow
energy and the exact vertex volume. The top face is the source's extra layer. -/
theorem full_cube_conductivity_ge_unit_flow {d r : ℕ} (i : Fin d)
    (ω : Configuration d) (θ : IssuedBond (centeredBox d r) → ℝ)
    (hsupport : Network.FlowSupported (domainWeights ω) θ)
    (hθ : (issuedNetwork (centeredBox d r)).IsBoundaryUnitFlow
      (negativeFace (centeredBox d r) i) (positiveFace (centeredBox d r) i) θ) :
    0 < Network.flowEnergy (domainWeights ω) θ ∧
      ((2*(r:ℝ)+1)^2/Network.flowEnergy (domainWeights ω) θ)/((centeredBox d r).card:ℝ) ≤
        fullConductivity (centeredBox d r) i ω := by
  have hsource (x : DomainVertex (centeredBox d r)) (hx : x ∈ negativeFace (centeredBox d r) i) :
      coordinateData i x = -(r:ℝ) := by
    have h := rectangularBox_negativeFace_coordinate (fun _ : Fin d => r) i hx
    change (x.val i:ℝ) = -(r:ℝ)
    exact_mod_cast h
  have htarget (x : DomainVertex (centeredBox d r)) (hx : x ∈ positiveFace (centeredBox d r) i) :
      coordinateData i x = -(r:ℝ)+(2*(r:ℝ)+1) := by
    have h := rectangularBox_positiveFace_coordinate (fun _ : Fin d => r) i hx
    have hr : (x.val i:ℝ) = (r:ℝ)+1 := by exact_mod_cast h
    change (x.val i:ℝ) = _
    linarith
  have hb := (issuedNetwork (centeredBox d r)).conductance_ge_boundary_unit_flow
    (domainWeights ω) θ (domainWeights_nonneg ω) hsupport
    (fullBoundary (centeredBox d r)) (negativeFace (centeredBox d r) i)
    (positiveFace (centeredBox d r) i) (coordinateData i)
    (fun _ hx => hx.1) (fun _ hx => hx.1) hθ (-(r:ℝ)) (2*(r:ℝ)+1)
    (by positivity) hsource htarget
  refine ⟨hb.1,?_⟩
  exact div_le_div_of_nonneg_right hb.2 (Nat.cast_nonneg _)

end NearCritical
