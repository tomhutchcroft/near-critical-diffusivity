module

public import NearCritical.ExternalFiniteConnectionComparison
public import NearCritical.HalfSpaceEntropicTransfer

/-! Literal finite-halfspace specialization of the imported exploration/entropy
comparison. Critical-window uniform constants remain
separate; all probabilities and cluster sums use the existing project events. -/
@[expose] public section
noncomputable section
namespace NearCritical.External
open MeasureTheory
open scoped Classical BigOperators

/-- The finite vertex domain of the literal cutoff half-space event. -/
def halfSpaceExposureDomain {d : ℕ} (i : Fin d) (R : ℕ) : Finset (Vertex d) :=
  (latticeSupCube d R).filter (fun x => 0 ≤ x i)

theorem halfSpaceExposureDomain_coe {d : ℕ} (i : Fin d) (R : ℕ) :
    (halfSpaceExposureDomain i R : Set (Vertex d)) =
      halfSpaceArmDomain i ∩ (latticeSupCube d R : Set (Vertex d)) := by
  ext x
  simp [halfSpaceExposureDomain, halfSpaceArmDomain, and_comm]

/-- The source base lies in the finite exploration domain at admissible cutoffs. -/
theorem halfSpaceArmBase_mem_exposureDomain {d : ℕ} (i : Fin d)
    (k R : ℕ) (hR : k ≤ R) : halfSpaceArmBase i k ∈ halfSpaceExposureDomain i R := by
  apply Finset.mem_filter.mpr
  constructor
  · apply mem_latticeSupCube.mpr
    intro j
    by_cases hj : j = i
    · subst j
      simpa [halfSpaceArmBase] using (show (k : ℤ) ≤ (R : ℤ) by exact_mod_cast hR)
    · simp [halfSpaceArmBase, hj]
  · simp [halfSpaceArmBase]

/-- Summing over the half-cube or the full counting cube gives the literal
same cluster sum: singleton targets outside the half-space have empty events. -/
theorem halfSpaceExposure_cluster_sum {d : ℕ} (i : Fin d) (q : unitInterval)
    (k R : ℕ) :
    (∑ y ∈ halfSpaceExposureDomain i R, (percolation d q).real
      (connectionToSetEvent (halfSpaceExposureDomain i R : Set (Vertex d))
        (halfSpaceArmBase i k) {y})) = finiteHalfSpaceClusterSum i q k R := by
  rw [halfSpaceExposureDomain_coe]
  unfold finiteHalfSpaceClusterSum
  unfold halfSpaceExposureDomain
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro y _
  by_cases hy : 0 ≤ y i
  · simp [hy, finiteHalfSpaceClusterSum]
  · have hempty : connectionToSetEvent
        (halfSpaceArmDomain i ∩ (latticeSupCube d R : Set (Vertex d)))
        (halfSpaceArmBase i k) {y} = ∅ := by
      ext ω
      constructor
      · rintro ⟨_, z, hz, hzD, _⟩
        have hzy : z = y := hz
        subst z
        exact (hy hzD.1).elim
      · intro h
        exact h.elim
    simp [hy, hempty]

/-- Actual cutoff half-space comparison with the explicit Bernoulli denominator,
for every target height and every cutoff containing the source base. -/
theorem finiteHalfSpace_entropic_budget {d : ℕ} (i : Fin d) (q p : unitInterval)
    (hq : (q : ℝ) ∈ Set.Ioo (0 : ℝ) 1) (hp : (p : ℝ) ∈ Set.Ioo (0 : ℝ) 1)
    (k n R : ℕ) (hR : k ≤ R) :
    |finiteHalfSpaceArmProbability i q k n R - finiteHalfSpaceArmProbability i p k n R| ≤
      3 * Real.sqrt (max (finiteHalfSpaceArmProbability i q k n R)
        (finiteHalfSpaceArmProbability i p k n R) *
        ((((q : ℝ) - (p : ℝ))^2 / ((p : ℝ) * (1-(p : ℝ)))) *
          ((2*d : ℕ) * finiteHalfSpaceClusterSum i q k R))) := by
  have h := finite_connection_entropic_budget q p hq hp (halfSpaceExposureDomain i R)
    (halfSpaceArmBase i k) (halfSpaceArmBase_mem_exposureDomain i k R hR)
    (halfSpaceArmTarget i n)
  dsimp only at h
  rw [halfSpaceExposure_cluster_sum] at h
  simpa only [halfSpaceExposureDomain_coe, finiteHalfSpaceArmProbability,
    finiteHalfSpaceArmEvent] using h

end NearCritical.External
