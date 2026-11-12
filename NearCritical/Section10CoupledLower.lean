module

public import NearCritical.Section10ActualLower
public import NearCritical.Section10ChainMean
public import NearCritical.Section9SprinkleOrLaw

/-! Conductivity lower bound from a random flow on the COUPLED law.

The Section 10 flow is a function of the configuration pair `z` (critical layer
and sprinkle), not of the supercritical configuration `z.1 OR z.2` alone. The
existing `annealed_cube_lower_of_supported_flow` takes a flow that is a function
of the supercritical configuration. `annealed_cube_lower_coupled` is the version
the source actually uses (5810--5835): for a flow and an event that depend on
`z` through finitely many layered bonds `R`,

  `((2r+1)^2 / |box|) * a^2 / K <= annealedFull(box, p OR q)`,

if on the event the flow is a unit flow supported on the open bonds of
`z.1 OR z.2`, the event has probability at least `a` and the expected energy on
the event is at most `K`. Proof: Thomson pointwise, Cauchy--Schwarz over the
finitely many bit patterns (`mean_conductivity_lower_of_energy_bound`), and the
law of `z.1 OR z.2` (`percolation_sprinkleOr_map`).
-/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open MeasureTheory
open scoped Classical BigOperators

/-- A function of finitely many layered bits, integrated as a finite sum. -/
lemma integral_bits_eq_sum {d : ℕ} (p q : unitInterval) (R : Finset (LBond d))
    (f : (R → Bool) → ℝ) :
    (∫ z, f (R.restrict (layerVal z)) ∂((percolation d p).prod (percolation d q))) =
      ∑ b : R → Bool, (∫ z : Configuration d × Configuration d,
        (if R.restrict (layerVal z) = b then (1:ℝ) else 0)
          ∂((percolation d p).prod (percolation d q))) * f b := by
  have hloc : ∀ b : R → Bool, IsLocal R (fun z : Configuration d × Configuration d =>
      (if R.restrict (layerVal z) = b then (1:ℝ) else 0) * f b) := fun b =>
    ⟨fun v => (if v = b then (1:ℝ) else 0) * f b, fun _ => rfl⟩
  have hpt : ∀ z : Configuration d × Configuration d, f (R.restrict (layerVal z)) =
      ∑ b : R → Bool, (if R.restrict (layerVal z) = b then (1:ℝ) else 0) * f b := by
    intro z
    rw [Finset.sum_eq_single (R.restrict (layerVal z))]
    · rw [if_pos rfl, one_mul]
    · intro b _ hb
      rw [if_neg (Ne.symm hb), zero_mul]
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt),
    integral_finsetSum _ (fun b _ => (hloc b).integrable p q)]
  exact Finset.sum_congr rfl (fun b _ => integral_mul_const _ _)

theorem annealed_cube_lower_coupled {d r : ℕ} (i : Fin d) (p q : unitInterval)
    (R : Finset (LBond d))
    (orb : (R → Bool) → IssuedBond (centeredBox d r) → Bool)
    (horb : ∀ z : Configuration d × Configuration d, orb (R.restrict (layerVal z)) =
      (issuedBondSet (centeredBox d r)).restrict (sprinkleOrConfiguration z.1 z.2))
    (θ : (R → Bool) → IssuedBond (centeredBox d r) → ℝ) (A : Set (R → Bool)) {a K : ℝ}
    (ha : 0 < a) (hK : 0 < K)
    (hflow : ∀ b ∈ A, Network.FlowSupported (cubeFlowWeights (orb b)) (θ b) ∧
      (issuedNetwork (centeredBox d r)).IsBoundaryUnitFlow
        (negativeFace (centeredBox d r) i) (positiveFace (centeredBox d r) i) (θ b))
    (hA : a ≤ ∫ z : Configuration d × Configuration d,
      (if R.restrict (layerVal z) ∈ A then (1:ℝ) else 0)
        ∂((percolation d p).prod (percolation d q)))
    (henergy : (∫ z : Configuration d × Configuration d,
      (if R.restrict (layerVal z) ∈ A then
        Network.flowEnergy (cubeFlowWeights (orb (R.restrict (layerVal z))))
          (θ (R.restrict (layerVal z))) else 0)
        ∂((percolation d p).prod (percolation d q))) ≤ K) :
    (((2*(r:ℝ)+1)^2/((centeredBox d r).card:ℝ))*a^2)/K ≤
      annealedFull (centeredBox d r) i ((orParameter p q : unitInterval) : ℝ) := by
  obtain ⟨μ, hμdef⟩ : ∃ μ : (R → Bool) → ℝ, μ = fun b =>
      ∫ z : Configuration d × Configuration d,
        (if R.restrict (layerVal z) = b then (1:ℝ) else 0)
          ∂((percolation d p).prod (percolation d q)) := ⟨_, rfl⟩
  have hμ0 : ∀ b, 0 ≤ μ b := fun b => by
    rw [hμdef]
    exact integral_nonneg (fun z => by split_ifs <;> norm_num)
  have hcard : 0 < ((centeredBox d r).card:ℝ) := by
    apply Nat.cast_pos.mpr
    apply Finset.card_pos.mpr
    refine ⟨0, mem_centeredBox.mpr ?_⟩
    intro j
    change -(r:ℤ) ≤ 0 ∧ 0 ≤ (r:ℤ)
    omega
  have hs : 0 < (2*(r:ℝ)+1)^2/((centeredBox d r).card:ℝ) := by positivity
  have he : ∀ b : R → Bool, 0 ≤ Network.flowEnergy (cubeFlowWeights (orb b)) (θ b) := by
    intro b
    apply Finset.sum_nonneg
    intro e _
    apply div_nonneg (sq_nonneg _)
    dsimp [cubeFlowWeights]
    split <;> norm_num
  have hpoint : ∀ b ∈ A, (2*(r:ℝ)+1)^2/((centeredBox d r).card:ℝ) ≤
      localFullConductivity (centeredBox d r) i (orb b) *
        Network.flowEnergy (cubeFlowWeights (orb b)) (θ b) := by
    intro b hb
    obtain ⟨hpos, hle⟩ := local_cube_flow_lower i (orb b) (θ b) (hflow b hb).1 (hflow b hb).2
    rw [div_right_comm] at hle
    exact (div_le_iff₀ hpos).mp hle
  have hA' : a ≤ ∑ b, if b ∈ A then μ b else 0 := by
    have h := integral_bits_eq_sum p q R (fun b => if b ∈ A then (1:ℝ) else 0)
    rw [h] at hA
    refine hA.trans (le_of_eq (Finset.sum_congr rfl (fun b _ => ?_)))
    rw [hμdef]
    simp only [mul_ite, mul_one, mul_zero]
  have henergy' : (∑ b, if b ∈ A then
      μ b * Network.flowEnergy (cubeFlowWeights (orb b)) (θ b) else 0) ≤ K := by
    have h := integral_bits_eq_sum p q R (fun b => if b ∈ A then
      Network.flowEnergy (cubeFlowWeights (orb b)) (θ b) else 0)
    rw [h] at henergy
    refine (le_of_eq (Finset.sum_congr rfl (fun b _ => ?_))).trans henergy
    rw [hμdef]
    simp only [mul_ite, mul_zero]
  have hb := mean_conductivity_lower_of_energy_bound μ
    (fun b => localFullConductivity (centeredBox d r) i (orb b))
    (fun b => Network.flowEnergy (cubeFlowWeights (orb b)) (θ b)) A hμ0
    (fun b => localFullConductivity_nonneg (centeredBox d r) i (orb b)) he hs ha hK hpoint hA'
    henergy'
  have hmean : (∑ b, μ b * localFullConductivity (centeredBox d r) i (orb b)) =
      annealedFull (centeredBox d r) i ((orParameter p q : unitInterval) : ℝ) := by
    have h := integral_bits_eq_sum p q R
      (fun b => localFullConductivity (centeredBox d r) i (orb b))
    rw [hμdef]
    rw [← h]
    simp only [horb]
    have hmap := percolation_sprinkleOr_map d p q
    rw [annealedFull, ← percolation_cylinder_expectation d (orParameter p q)
      (issuedBondSet (centeredBox d r)) (localFullConductivity (centeredBox d r) i), ← hmap]
    have hmeas : Measurable (fun ω : Configuration d =>
        localFullConductivity (centeredBox d r) i
          ((issuedBondSet (centeredBox d r)).restrict ω)) :=
      (measurable_of_finite (localFullConductivity (centeredBox d r) i)).comp
        (Finset.measurable_restrict (issuedBondSet (centeredBox d r)))
    exact (integral_map measurable_sprinkleOrConfiguration.aemeasurable
      hmeas.aestronglyMeasurable).symm
  rw [hmean] at hb
  exact hb

end NearCritical.Section10
