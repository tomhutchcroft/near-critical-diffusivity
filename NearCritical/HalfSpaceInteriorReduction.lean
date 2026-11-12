module

public import NearCritical.HalfSpacePioneerReduction

/-! New minimum-height/pioneer reductions for source prop.onearm_half_plus
Step 2. All sums remain extended nonnegative, including infinite values. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Set MeasureTheory
open scoped Classical ENNReal

private lemma tsum_finset_sum_ennreal {U J : Type*} (s : Finset J)
    (f : J → U → ℝ≥0∞) :
    (∑' u, ∑ j ∈ s, f j u) = ∑ j ∈ s, ∑' u, f j u := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert j s hj ih => simp only [Finset.sum_insert hj, ENNReal.tsum_add, ih]

/-- Regroup a minimum-vertex sum into its finite interval of integer heights. -/
lemma tsum_height_interval {d : ℕ} (i : Fin d) (a b : ℤ) (f : Vertex d → ℝ≥0∞) :
    (∑' u, if a ≤ u i ∧ u i ≤ b then f u else 0) =
      ∑ j ∈ Finset.Icc a b, ∑' u, if u i = j then f u else 0 := by
  rw [← tsum_finset_sum_ennreal]
  apply tsum_congr
  intro u
  simp [eq_comm]

/-- Translate a minimum-prefix connection to the origin, with its actual domain. -/
lemma halfSpace_minimum_prefix_probability {d : ℕ} (p : unitInterval)
    (i : Fin d) (j : ℤ) (x v : Vertex d) :
    percolation d p (connectionToSetEvent {z | j ≤ z i} x {x + v}) =
      percolation d p (connectionToSetEvent {z | j - x i ≤ z i} 0 {v}) := by
  have h := connectionToSet_probability_translation p (-x) x {z | j ≤ z i} {x + v}
  rw [translate_halfSpace] at h
  simpa only [Pi.neg_apply, Set.image_singleton, neg_add_cancel, neg_add_cancel_left,
    sub_eq_add_neg] using h.symm

/-- The height-j minimum-prefix mass is exactly psi(H_{x_i-j}). -/
theorem halfSpace_minimum_prefix_sum {d : ℕ} (p : unitInterval)
    (i : Fin d) (x : Vertex d) (j : ℤ) :
    (∑' u : Vertex d, if u i = j then
      percolation d p (connectionToSetEvent {z | j ≤ z i} x {u}) else 0) =
      halfSpacePioneerMass p i (x i - j) := by
  rw [← (Equiv.addLeft x).tsum_eq]
  unfold halfSpacePioneerMass
  apply tsum_congr
  intro v
  have hcond : ((Equiv.addLeft x) v) i = j ↔ v i = -(x i - j) := by
    change x i + v i = j ↔ v i = -(x i - j)
    omega
  by_cases hv : v i = -(x i - j)
  · rw [ite_eq_left (hcond.mpr hv), ite_eq_left hv]
    change percolation d p (connectionToSetEvent {z | j ≤ z i} x {x + v}) = _
    rw [halfSpace_minimum_prefix_probability]
    have he : j - x i = -(x i - j) := by omega
    rw [he]
  · simp only [ite_eq_right (mt hcond.mp hv), ite_eq_right hv]

/-- Actual Step2 arm reduction: the factor k+1 in the paper comes later from
bounding this finite sum, not from an assumed decomposition. -/
theorem halfSpace_interior_arm_le_pioneer_sum {d : ℕ} (p : unitInterval)
    (i : Fin d) (x : Vertex d) (n : ℤ) :
    percolation d p (connectionToSetEvent {z | 0 ≤ z i} x {z | n ≤ z i}) ≤
      ∑ j ∈ Finset.Icc 0 (x i),
        halfSpacePioneerMass p i (x i - j) * halfSpaceArmProbability p i (n - j) := by
  calc
    _ ≤ ∑' u : Vertex d, if 0 ≤ u i ∧ u i ≤ x i then
        percolation d p (connectionToSetEvent {z | u i ≤ z i} x {u}) *
          percolation d p (connectionToSetEvent {z | u i ≤ z i} u {z | n ≤ z i})
        else 0 := halfSpace_connection_minimum_bk p i 0 x _
    _ = ∑ j ∈ Finset.Icc 0 (x i), ∑' u : Vertex d, if u i = j then
        percolation d p (connectionToSetEvent {z | u i ≤ z i} x {u}) *
          percolation d p (connectionToSetEvent {z | u i ≤ z i} u {z | n ≤ z i})
        else 0 := tsum_height_interval i 0 (x i) _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      calc
        _ = (∑' u : Vertex d, if u i = j then
            percolation d p (connectionToSetEvent {z | j ≤ z i} x {u}) else 0) *
            halfSpaceArmProbability p i (n - j) := by
          rw [← ENNReal.tsum_mul_right]
          apply tsum_congr
          intro u
          by_cases hu : u i = j
          · rw [ite_eq_left hu, ite_eq_left hu]
            rw [halfSpace_suffix_probability p i (u i) n u rfl]
            simp only [hu, halfSpaceArmProbability]
          · simp only [ite_eq_right hu, zero_mul]
        _ = _ := by rw [halfSpace_minimum_prefix_sum]

/-- Domain-checked half-space cluster sum. For a starting vertex inside the
half-space this is its actual expected cluster size; outside it is zero.
This sums endpoint connection probabilities, rather than pioneer masses. -/
def halfSpaceSusceptibility {d : ℕ} (p : unitInterval) (i : Fin d)
    (x : Vertex d) : ℝ≥0∞ :=
  ∑' y : Vertex d, percolation d p (connectionToSetEvent {z | 0 ≤ z i} x {y})

/-- Translate a boundary-origin cluster in its own half-space to height zero.
All endpoints are summed, with domain membership checked by the actual event. -/
lemma halfSpace_boundary_susceptibility_shift {d : ℕ} (p : unitInterval)
    (i : Fin d) (u : Vertex d) :
    (∑' y : Vertex d, percolation d p
      (connectionToSetEvent {z | u i ≤ z i} u {y})) =
      halfSpaceSusceptibility p i 0 := by
  rw [← (Equiv.addLeft u).tsum_eq]
  unfold halfSpaceSusceptibility
  apply tsum_congr
  intro v
  change percolation d p (connectionToSetEvent {z | u i ≤ z i} u {u + v}) = _
  rw [halfSpace_minimum_prefix_probability]
  simp only [sub_self]

/-- The corrected interior-cluster bound needed in source Step3: the interior
susceptibility is controlled by the finite pioneer sum times the BOUNDARY
susceptibility. It is derived by summing actual minimum-height BK estimates. -/
theorem halfSpace_interior_susceptibility_le_pioneer_sum {d : ℕ} (p : unitInterval)
    (i : Fin d) (x : Vertex d) :
    halfSpaceSusceptibility p i x ≤
      ∑ j ∈ Finset.Icc 0 (x i),
        halfSpacePioneerMass p i (x i - j) * halfSpaceSusceptibility p i 0 := by
  calc
    _ ≤ ∑' y : Vertex d, ∑' u : Vertex d,
        if 0 ≤ u i ∧ u i ≤ x i then
          percolation d p (connectionToSetEvent {z | u i ≤ z i} x {u}) *
            percolation d p (connectionToSetEvent {z | u i ≤ z i} u {y})
        else 0 := ENNReal.tsum_le_tsum (fun y ↦ halfSpace_connection_minimum_bk p i 0 x {y})
    _ = ∑' u : Vertex d, ∑' y : Vertex d,
        if 0 ≤ u i ∧ u i ≤ x i then
          percolation d p (connectionToSetEvent {z | u i ≤ z i} x {u}) *
            percolation d p (connectionToSetEvent {z | u i ≤ z i} u {y})
        else 0 := ENNReal.tsum_comm
    _ = ∑' u : Vertex d, if 0 ≤ u i ∧ u i ≤ x i then
        percolation d p (connectionToSetEvent {z | u i ≤ z i} x {u}) *
          halfSpaceSusceptibility p i 0 else 0 := by
      apply tsum_congr
      intro u
      by_cases hu : 0 ≤ u i ∧ u i ≤ x i
      · simp only [ite_eq_left hu]
        rw [ENNReal.tsum_mul_left, halfSpace_boundary_susceptibility_shift]
      · simp only [ite_eq_right hu, tsum_zero]
    _ = ∑ j ∈ Finset.Icc 0 (x i), ∑' u : Vertex d, if u i = j then
        percolation d p (connectionToSetEvent {z | u i ≤ z i} x {u}) *
          halfSpaceSusceptibility p i 0 else 0 := tsum_height_interval i 0 (x i) _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      calc
        _ = (∑' u : Vertex d, if u i = j then
            percolation d p (connectionToSetEvent {z | j ≤ z i} x {u}) else 0) *
            halfSpaceSusceptibility p i 0 := by
          rw [← ENNReal.tsum_mul_right]
          apply tsum_congr
          intro u
          by_cases hu : u i = j
          · rw [ite_eq_left hu, ite_eq_left hu]
            simp only [hu]
          · simp only [ite_eq_right hu, zero_mul]
        _ = _ := by rw [halfSpace_minimum_prefix_sum]

end NearCritical
