module

public import NearCritical.Section10FlowMean
public import NearCritical.CylinderDisjointOccurrence

/-! Section10 final reduction under the ACTUAL Bernoulli law. Source random
unit-flow and event/energy estimates remain explicit construction obligations. -/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open MeasureTheory Set
open scoped Classical BigOperators
set_option maxHeartbeats 800000

def cubeFlowWeights {d : ℕ} {U : Finset (Vertex d)} (η : IssuedBond U → Bool) : IssuedBond U → ℝ :=
  fun e => if η e then 1 else 0

def cubeFlowEnergy {d : ℕ} (U : Finset (Vertex d))
    (θ : (IssuedBond U → Bool) → IssuedBond U → ℝ) (η : IssuedBond U → Bool) : ℝ :=
  Network.flowEnergy (cubeFlowWeights η) (θ η)

def cubeFlowEvent {d : ℕ} (U : Finset (Vertex d)) (A : Set (IssuedBond U → Bool)) : Set (Configuration d) :=
  (issuedBondSet U).restrict ⁻¹' A

def cubeBernoulliWeight {J : Type*} [Fintype J] (p : unitInterval) (η : J → Bool) : ℝ :=
  ∏ e, if η e then (p:ℝ) else 1-(p:ℝ)

private lemma cubeBernoulliWeight_nonneg {J : Type*} [Fintype J] (p : unitInterval) (η : J → Bool) :
    0 ≤ cubeBernoulliWeight p η := by
  apply Finset.prod_nonneg
  intro e _he
  split_ifs
  · exact p.2.1
  · exact sub_nonneg.mpr p.2.2

private lemma finiteExpectation_weighted {J : Type*} [Fintype J] (p : unitInterval)
    (f : (J → Bool) → ℝ) : finiteExpectation (p:ℝ) f = ∑ η, cubeBernoulliWeight p η*f η := by
  unfold finiteExpectation cubeBernoulliWeight
  apply Finset.sum_congr rfl
  intro η _hη
  ring

/-- Exact event mass of the finite cube observable under actual percolation. -/
theorem cubeFlowEvent_probability {d : ℕ} (p : unitInterval) (U : Finset (Vertex d))
    (A : Set (IssuedBond U → Bool)) :
    (percolation d p).real (cubeFlowEvent U A) =
      ∑ η, if η ∈ A then cubeBernoulliWeight p η else 0 := by
  have hm : MeasurableSet (cubeFlowEvent U A) :=
    (Set.to_countable A).measurableSet.preimage (Finset.measurable_restrict _)
  have hOne : (∫ ω : Configuration d,
      (cubeFlowEvent U A).indicator (fun _ => (1:ℝ)) ω ∂percolation d p) =
      (percolation d p).real (cubeFlowEvent U A) := by
    exact integral_indicator_one hm
  calc
    _ = ∫ ω, (if (issuedBondSet U).restrict ω ∈ A then (1:ℝ) else 0) ∂percolation d p := by
      simpa only [Set.indicator,cubeFlowEvent,Set.mem_preimage,Set.mem_ofPred_eq] using hOne.symm
    _ = finiteExpectation (p:ℝ) (fun η => if η ∈ A then (1:ℝ) else 0) :=
      percolation_cylinder_expectation d p (issuedBondSet U)
        (fun η : IssuedBond U → Bool => if η ∈ A then (1:ℝ) else 0)
    _ = _ := by
      rw [finiteExpectation_weighted]
      simp only [mul_ite,mul_one,mul_zero]
      apply Finset.sum_congr
      · ext η; simp only [Finset.mem_univ]
      · intro η _; rfl

/-- Local issued-coordinate flows give the actual cube conductivity estimate;
the full configuration and its finite restriction are reconstructed internally. -/
theorem local_cube_flow_lower {d r : ℕ} (i : Fin d) (η : IssuedBond (centeredBox d r) → Bool)
    (θ : IssuedBond (centeredBox d r) → ℝ)
    (hsupport : Network.FlowSupported (cubeFlowWeights η) θ)
    (hθ : (issuedNetwork (centeredBox d r)).IsBoundaryUnitFlow
      (negativeFace (centeredBox d r) i) (positiveFace (centeredBox d r) i) θ) :
    0 < Network.flowEnergy (cubeFlowWeights η) θ ∧
      ((2*(r:ℝ)+1)^2/Network.flowEnergy (cubeFlowWeights η) θ)/((centeredBox d r).card:ℝ) ≤
        localFullConductivity (centeredBox d r) i η := by
  let U := centeredBox d r
  let ω := extendConfiguration (issuedBondSet U) (fun _ => false) η
  have hw : (domainWeights ω : IssuedBond U → ℝ) = cubeFlowWeights η := by
    funext e
    simp [domainWeights,ω,extendConfiguration,issuedBond,e.property,cubeFlowWeights]
  have hb := full_cube_conductivity_ge_unit_flow i ω θ (by simpa only [hw] using hsupport) hθ
  rw [hw,fullConductivity_restrict,restrict_extendConfiguration] at hb
  exact hb

/-- The source mean-energy reduction for existing ACTUAL annealedFull, with
no assumed Bernoulli law, expected-conductivity bound or Thomson comparison. -/
theorem annealed_cube_lower_of_supported_flow {d r : ℕ} (i : Fin d) (p : unitInterval)
    (θ : (IssuedBond (centeredBox d r) → Bool) → IssuedBond (centeredBox d r) → ℝ)
    (A : Set (IssuedBond (centeredBox d r) → Bool)) {a K : ℝ} (ha : 0 < a) (hK : 0 < K)
    (hflow : ∀ η ∈ A, Network.FlowSupported (cubeFlowWeights η) (θ η) ∧
      (issuedNetwork (centeredBox d r)).IsBoundaryUnitFlow
        (negativeFace (centeredBox d r) i) (positiveFace (centeredBox d r) i) (θ η))
    (hA : a ≤ (percolation d p).real (cubeFlowEvent (centeredBox d r) A))
    (henergy : (∫ ω, (if (issuedBondSet (centeredBox d r)).restrict ω ∈ A then
      cubeFlowEnergy (centeredBox d r) θ ((issuedBondSet (centeredBox d r)).restrict ω) else 0)
        ∂percolation d p) ≤ K) :
    (((2*(r:ℝ)+1)^2/((centeredBox d r).card:ℝ))*a^2)/K ≤
      annealedFull (centeredBox d r) i (p:ℝ) := by
  let U := centeredBox d r
  let s : ℝ := (2*(r:ℝ)+1)^2/(U.card:ℝ)
  have hcard : 0 < (U.card:ℝ) := by
    apply Nat.cast_pos.mpr
    apply Finset.card_pos.mpr
    refine ⟨0,?_⟩
    apply mem_centeredBox.mpr
    intro j
    change -(r:ℤ) ≤ 0 ∧ 0 ≤ (r:ℤ)
    omega
  have hs : 0 < s := by dsimp [s]; positivity
  have he (η : IssuedBond U → Bool) : 0 ≤ cubeFlowEnergy U θ η := by
    apply Finset.sum_nonneg
    intro e _he
    apply div_nonneg (sq_nonneg _)
    dsimp [cubeFlowWeights]
    split <;> norm_num
  have hpoint (η : IssuedBond U → Bool) (hη : η ∈ A) :
      s ≤ localFullConductivity U i η*cubeFlowEnergy U θ η := by
    obtain ⟨hp,hb⟩ := local_cube_flow_lower i η (θ η) (hflow η hη).1 (hflow η hη).2
    apply (div_le_iff₀ hp).mp
    convert hb using 1 <;> dsimp [s,cubeFlowEnergy] <;> ring
  rw [cubeFlowEvent_probability] at hA
  have hcyl := percolation_cylinder_expectation d p (issuedBondSet U)
    (fun η : IssuedBond U → Bool => if η ∈ A then cubeFlowEnergy U θ η else 0)
  have henergyFinite : finiteExpectation (p:ℝ)
      (fun η : IssuedBond U → Bool => if η ∈ A then cubeFlowEnergy U θ η else 0) ≤ K := by
    rw [← hcyl]
    exact henergy
  have henergy' : (∑ η, if η ∈ A then cubeBernoulliWeight p η*cubeFlowEnergy U θ η else 0) ≤ K := by
    calc
      _ = finiteExpectation (p:ℝ)
          (fun η : IssuedBond U → Bool => if η ∈ A then cubeFlowEnergy U θ η else 0) := by
        rw [finiteExpectation_weighted]
        simp only [mul_ite,mul_zero]
        apply Finset.sum_congr
        · ext η; simp only [Finset.mem_univ]
        · intro η _; rfl
      _ ≤ K := henergyFinite
  have hb := mean_conductivity_lower_of_energy_bound (cubeBernoulliWeight p)
    (localFullConductivity U i) (cubeFlowEnergy U θ) A (cubeBernoulliWeight_nonneg p)
    (localFullConductivity_nonneg U i) he hs ha hK hpoint hA henergy'
  have hmean : (∑ η : IssuedBond U → Bool,
      cubeBernoulliWeight p η*localFullConductivity U i η) = annealedFull U i (p:ℝ) := by
    rw [annealedFull,finiteExpectation_weighted]
    apply Finset.sum_congr
    · ext η; simp only [Finset.mem_univ]
    · intro η _; rfl
  rw [hmean] at hb
  exact hb

end NearCritical.Section10
