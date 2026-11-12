module

public import NearCritical.HalfSpaceSusceptibilityBounds
public import NearCritical.HalfSpaceEntropicTransfer

/-! Quantitative NEW interior-cluster correction in prop.onearm_half_plus Step3.
Consumes the proved minimum/pioneer reduction, not an assumed interior bound. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Set MeasureTheory
open scoped Classical ENNReal

/-- Bound the actual interior susceptibility by the number of possible minimum
heights, using the already proved minimum-vertex BK/pioneer reduction. -/
theorem halfSpace_interior_susceptibility_le_of_bounds {d : ℕ} (p : unitInterval) (i : Fin d)
    (x : Vertex d) (k : ℕ) (hx : x i = (k : ℤ)) {U V : ℝ} (hU : 0 ≤ U) (_hV : 0 ≤ V)
    (pioneers : ∀ m : ℕ, halfSpacePioneerMass p i (m : ℤ) ≤ ENNReal.ofReal U)
    (boundary : halfSpaceSusceptibility p i 0 ≤ ENNReal.ofReal V) :
    halfSpaceSusceptibility p i x ≤ ENNReal.ofReal ((k + 1 : ℝ) * U * V) := by
  calc
    _ ≤ ∑ j ∈ Finset.Icc 0 (x i), halfSpacePioneerMass p i (x i - j) *
        halfSpaceSusceptibility p i 0 := halfSpace_interior_susceptibility_le_pioneer_sum p i x
    _ ≤ ∑ _j ∈ Finset.Icc 0 (x i), ENNReal.ofReal U * ENNReal.ofReal V := by
      apply Finset.sum_le_sum
      intro j hj
      have hdiff : 0 ≤ x i - j := sub_nonneg.mpr (Finset.mem_Icc.mp hj).2
      have hpion : halfSpacePioneerMass p i (x i - j) ≤ ENNReal.ofReal U := by
        simpa only [Int.toNat_of_nonneg hdiff] using pioneers (x i - j).toNat
      exact mul_le_mul' hpion boundary
    _ = _ := by
      rw [hx, Finset.sum_const, nsmul_eq_mul]
      have hc : (Finset.Icc (0 : ℤ) (k : ℤ)).card = k + 1 := by rw [Int.card_Icc]; omega
      rw [hc, ENNReal.ofReal_mul (mul_nonneg (by positivity) hU), ENNReal.ofReal_mul (by positivity)]
      have hN : ENNReal.ofReal (k + 1 : ℝ) = ((k + 1 : ℕ) : ℝ≥0∞) := by
        rw [ENNReal.ofReal_add (Nat.cast_nonneg k) zero_le_one]
        simp
      rw [hN]
      ring

/-- Literal finite-domain connection sum is bounded by the actual full interior
susceptibility. This uses domain inclusion and nonnegative partial sums. -/
lemma finiteHalfSpaceClusterSum_ofReal_le {d : ℕ} (p : unitInterval) (i : Fin d) (k R : ℕ) :
    ENNReal.ofReal (finiteHalfSpaceClusterSum i p k R) ≤
      halfSpaceSusceptibility p i (halfSpaceArmBase i k) := by
  have hsum : ENNReal.ofReal (finiteHalfSpaceClusterSum i p k R) =
      ∑ y ∈ latticeSupCube d R, percolation d p
        (connectionToSetEvent (halfSpaceArmDomain i ∩ (latticeSupCube d R : Set (Vertex d)))
          (halfSpaceArmBase i k) {y}) := by
    unfold finiteHalfSpaceClusterSum
    rw [ENNReal.ofReal_sum_of_nonneg (f := fun y : Vertex d => (percolation d p).real
      (connectionToSetEvent (halfSpaceArmDomain i ∩ (latticeSupCube d R : Set (Vertex d)))
        (halfSpaceArmBase i k) {y})) (fun y hy => measureReal_nonneg)]
    apply Finset.sum_congr rfl
    intro y hy
    exact ofReal_measureReal
  rw [hsum]
  calc
    _ ≤ ∑ y ∈ latticeSupCube d R, percolation d p
        (connectionToSetEvent {z | 0 ≤ z i} (halfSpaceArmBase i k) {y}) := by
      apply Finset.sum_le_sum
      intro y hy
      apply measure_mono
      have hsub : halfSpaceArmDomain i ∩ (latticeSupCube d R : Set (Vertex d)) ⊆ {z | 0 ≤ z i} :=
        fun z hz => hz.1
      exact connectionToSetEvent_mono hsub (Subset.refl {y}) (halfSpaceArmBase i k)
    _ ≤ _ := ENNReal.sum_le_tsum _

/-- Discharge the interior-cluster estimate from the cited weighted positive-
height pioneer decay, with no interior-cluster or zero-layer premise. -/
theorem finiteHalfSpaceClusterSum_upper_of_weighted_pioneers {d : ℕ} (p : unitInterval) (i : Fin d)
    {C c : ℝ} (hC : 0 < C) (hc : 0 < c) (hpc : 0 < (criticalPoint d : ℝ))
    (hplo : (criticalPoint d : ℝ) / 2 ≤ (p : ℝ)) (hpp : (p : ℝ) < (criticalPoint d : ℝ))
    (decay : WeightedPositiveHeightPioneerDecay p i C c) (k R : ℕ) :
    finiteHalfSpaceClusterSum i p k R ≤
      ((4 * C / (criticalPoint d : ℝ) ^ 2) *
        (4 * C / (criticalPoint d : ℝ) ^ 2 + 2 * C / ((criticalPoint d : ℝ) * c))) *
        (k + 1 : ℝ) / Real.sqrt ((criticalPoint d : ℝ) - (p : ℝ)) := by
  let U : ℝ := 4 * C / (criticalPoint d : ℝ) ^ 2
  let S : ℝ := 4 * C / (criticalPoint d : ℝ) ^ 2 + 2 * C / ((criticalPoint d : ℝ) * c)
  let s : ℝ := Real.sqrt ((criticalPoint d : ℝ) - (p : ℝ))
  have hU : 0 ≤ U := by dsimp [U]; positivity
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hs : 0 < s := Real.sqrt_pos.mpr (sub_pos.mpr hpp)
  have hb := halfSpace_interior_susceptibility_le_of_bounds p i (halfSpaceArmBase i k) k
    (by simp [halfSpaceArmBase]) hU (div_nonneg hS hs.le)
    (fun m => halfSpace_pioneer_uniform_of_weighted p i hC hc hpc hplo decay m)
    (halfSpace_susceptibility_upper_of_weighted_pioneers p i hC hc hpc hplo hpp decay)
  have hprob : ENNReal.ofReal (finiteHalfSpaceClusterSum i p k R) ≤
      ENNReal.ofReal ((k + 1 : ℝ) * U * (S / s)) :=
    (finiteHalfSpaceClusterSum_ofReal_le p i k R).trans hb
  have hnonneg : 0 ≤ (k + 1 : ℝ) * U * (S / s) := by positivity
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hprob
  rw [ENNReal.toReal_ofReal (finiteHalfSpaceClusterSum_nonneg i p k R),
    ENNReal.toReal_ofReal hnonneg] at hreal
  convert hreal using 1
  dsimp [U, S, s]
  ring

/-- Assemble Step3's prerequisite from the remaining NEW subcritical-arm field
and cited positive-height pioneer input. The interior field is now a theorem. -/
theorem halfSpaceLowerTransferPrerequisites_of_arm_and_pioneers {d : ℕ} (i : Fin d)
    {A C c : ℝ} (hC : 0 < C) (hc : 0 < c) (hpc : 0 < (criticalPoint d : ℝ))
    (decay : ∀ q : unitInterval, (criticalPoint d : ℝ) / 2 ≤ (q : ℝ) →
      (q : ℝ) < (criticalPoint d : ℝ) → WeightedPositiveHeightPioneerDecay q i C c)
    (arm : ∀ (q : unitInterval) (k n R : ℕ), 1 ≤ n → 2 * k ≤ n → k ≤ R →
      (criticalPoint d : ℝ) / 2 ≤ (q : ℝ) → (q : ℝ) < (criticalPoint d : ℝ) →
      finiteHalfSpaceArmProbability i q k n R ≤ A * ((k + 1 : ℝ) / (n : ℝ) ^ 3)) :
    HalfSpaceLowerTransferPrerequisites i A
      ((4 * C / (criticalPoint d : ℝ) ^ 2) *
        (4 * C / (criticalPoint d : ℝ) ^ 2 + 2 * C / ((criticalPoint d : ℝ) * c))) := by
  intro q k n R hn hk hR hqlo hqhi
  exact ⟨arm q k n R hn hk hR hqlo hqhi,
    finiteHalfSpaceClusterSum_upper_of_weighted_pioneers q i hC hc hpc hqlo hqhi
      (decay q hqlo hqhi) k R⟩

/-- All-scales supercritical transfer with the interior-cluster prerequisite
DISCHARGED. Only the unresolved NEW subcritical-arm estimate remains from
Steps1/2; cited finite DM and positive-height pioneer decay stay explicit. -/
theorem halfSpace_entropic_transfer_of_arm_and_pioneers {d : ℕ} (i : Fin d)
    {E A C c : ℝ} (hE : 0 < E) (hA : 0 < A) (hC : 0 < C) (hc : 0 < c)
    (hpc : 0 < (criticalPoint d : ℝ)) (hpc1 : (criticalPoint d : ℝ) < 1)
    (entropic : FiniteHalfSpaceEntropicInput i E)
    (decay : ∀ q : unitInterval, (criticalPoint d : ℝ) / 2 ≤ (q : ℝ) →
      (q : ℝ) < (criticalPoint d : ℝ) → WeightedPositiveHeightPioneerDecay q i C c)
    (arm : ∀ (q : unitInterval) (k n R : ℕ), 1 ≤ n → 2 * k ≤ n → k ≤ R →
      (criticalPoint d : ℝ) / 2 ≤ (q : ℝ) → (q : ℝ) < (criticalPoint d : ℝ) →
      finiteHalfSpaceArmProbability i q k n R ≤ A * ((k + 1 : ℝ) / (n : ℝ) ^ 3)) :
    ∃ K : ℝ, 0 < K ∧ ∀ (p : unitInterval) (k n : ℕ), 1 ≤ n → 2 * k ≤ n →
      (criticalPoint d : ℝ) < (p : ℝ) →
      (p : ℝ) ≤ (criticalPoint d : ℝ) + ((n : ℝ) ^ 2)⁻¹ →
      (percolation d p).real (halfSpaceArmEvent i k n) ≤ K * ((k + 1 : ℝ) / (n : ℝ) ^ 3) := by
  exact halfSpace_entropic_transfer_all_scales i hE hA
    (by positivity : 0 < ((4 * C / (criticalPoint d : ℝ) ^ 2) *
      (4 * C / (criticalPoint d : ℝ) ^ 2 + 2 * C / ((criticalPoint d : ℝ) * c)))) entropic
    (halfSpaceLowerTransferPrerequisites_of_arm_and_pioneers i hC hc hpc decay arm) hpc hpc1

end NearCritical
