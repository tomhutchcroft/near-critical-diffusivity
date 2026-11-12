module

public import NearCritical.FiniteBlockResampling

/-! Actual incident-cluster replacement for prop.num_spanning_new Step 2.
The fixed-fiber identity below retains arbitrary revealed graph information. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory ProbabilityTheory
open scoped Classical

/-- Refresh all internal bonds touching the actual component, using a second
configuration. All other coordinates retain their original values. -/
def clusterResample {d : ℕ} (U : Finset (Vertex d)) (root : Vertex d)
    (ω ζ : Configuration d) : Configuration d :=
  resampleBonds (clusterRevealBonds U (finiteBoxCluster ω U root)) ω ζ

/-- The adaptive bond mask is measurable, proved by its finite component partition. -/
lemma measurableSet_clusterResample_mask {d : ℕ} (U : Finset (Vertex d))
    (root : Vertex d) (hroot : root ∈ U) (e : Bond d) :
    MeasurableSet {ω : Configuration d |
      e ∈ clusterRevealBonds U (finiteBoxCluster ω U root)} := by
  have he : {ω : Configuration d | e ∈ clusterRevealBonds U (finiteBoxCluster ω U root)} =
      ⋃ C : ↥U.powerset, {ω : Configuration d |
        finiteBoxCluster ω U root = C.val ∧ e ∈ clusterRevealBonds U C.val} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · intro h
      exact ⟨⟨finiteBoxCluster ω U root,
        Finset.mem_powerset.mpr (finiteBoxCluster_subset ω U root)⟩, rfl, h⟩
    · rintro ⟨C, hc, h⟩
      simpa [hc] using h
  rw [he]
  apply MeasurableSet.iUnion
  intro C
  by_cases h : e ∈ clusterRevealBonds U C.val
  · simpa [h] using measurableSet_clusterReveal_event U C.val root hroot
  · simp [h]

lemma measurable_clusterResample {d : ℕ} (U : Finset (Vertex d))
    (root : Vertex d) (hroot : root ∈ U) :
    Measurable (fun z : Configuration d × Configuration d => clusterResample U root z.1 z.2) := by
  apply measurable_pi_iff.mpr
  intro e
  exact Measurable.ite ((measurableSet_clusterResample_mask U root hroot e).preimage measurable_fst)
    ((measurable_pi_apply e).comp measurable_snd) ((measurable_pi_apply e).comp measurable_fst)

lemma clusterResample_of_cluster_eq {d : ℕ} (U C : Finset (Vertex d))
    (root : Vertex d) (ω ζ : Configuration d) (hC : finiteBoxCluster ω U root = C) :
    clusterResample U root ω ζ = resampleBonds (clusterRevealBonds U C) ω ζ := by
  simp [clusterResample, hC]

/-- On an actual component fiber, refreshing its incident bonds preserves
all finite-coordinate expectations and factors against every observable of
its original revealed graph. No replacement-law premise is assumed. -/
theorem clusterResample_fiber_factorization {d : ℕ} (p : unitInterval)
    (U C : Finset (Vertex d)) (root : Vertex d) (hroot : root ∈ U)
    (G : Finset (Bond d)) (F : (clusterRevealBonds U C → Bool) → ℝ)
    (H : (G → Bool) → ℝ) :
    (∫ ω : Configuration d,
      ({η | finiteBoxCluster η U root = C} : Set (Configuration d)).indicator
        (fun η => F ((clusterRevealBonds U C).restrict η)) ω *
        (∫ ζ, H (G.restrict (clusterResample U root ω ζ)) ∂percolation d p)
      ∂percolation d p) =
    (∫ ω : Configuration d,
      ({η | finiteBoxCluster η U root = C} : Set (Configuration d)).indicator
        (fun η => F ((clusterRevealBonds U C).restrict η)) ω ∂percolation d p) *
      (∫ ω : Configuration d, H (G.restrict ω) ∂percolation d p) := by
  let S := clusterRevealBonds U C
  have hd : Disjoint S (G \ S : Finset (Bond d)) := by
    apply Finset.disjoint_left.mpr
    intro e he hdiff
    exact (Finset.mem_sdiff.mp hdiff).2 he
  have hf := clusterReveal_fresh_factorization p U C root hroot (G \ S) hd F
    (resampleAverage p G S H)
  rw [integral_resampleAverage] at hf
  rw [← hf]
  apply integral_congr_ae
  filter_upwards [] with ω
  by_cases hC : finiteBoxCluster ω U root = C
  · simp only [Set.mem_ofPred_eq, hC, Set.indicator_of_mem]
    simp_rw [clusterResample_of_cluster_eq U C root ω _ hC]
    rw [integral_resampleBonds]
  · simp [hC]

theorem clusterResample_fixed_fiber_factorization {d : ℕ} (p : unitInterval)
    (U C : Finset (Vertex d)) (root : Vertex d) (hroot : root ∈ U)
    (G : Finset (Bond d)) (F : (clusterRevealBonds U C → Bool) → ℝ)
    (H : (G → Bool) → ℝ) :
    (∫ ω : Configuration d,
      ({η | finiteBoxCluster η U root = C} : Set (Configuration d)).indicator
        (fun η => F ((clusterRevealBonds U C).restrict η)) ω *
        (∫ ζ, H (G.restrict (resampleBonds (clusterRevealBonds U C) ω ζ)) ∂percolation d p)
      ∂percolation d p) =
    (∫ ω : Configuration d,
      ({η | finiteBoxCluster η U root = C} : Set (Configuration d)).indicator
        (fun η => F ((clusterRevealBonds U C).restrict η)) ω ∂percolation d p) *
      (∫ ω : Configuration d, H (G.restrict ω) ∂percolation d p) := by
  let S := clusterRevealBonds U C
  have hd : Disjoint S (G \ S : Finset (Bond d)) := by
    apply Finset.disjoint_left.mpr
    intro e he hdiff
    exact (Finset.mem_sdiff.mp hdiff).2 he
  have hf := clusterReveal_fresh_factorization p U C root hroot (G \ S) hd F
    (resampleAverage p G S H)
  rw [integral_resampleAverage] at hf
  simpa only [integral_resampleBonds] using hf

/-- Arbitrary weight of the revealed component and all its incident bond bits. -/
def clusterRevealWeight {d : ℕ} (U : Finset (Vertex d)) (root : Vertex d)
    (F : ∀ C : Finset (Vertex d), (clusterRevealBonds U C → Bool) → ℝ)
    (ω : Configuration d) : ℝ :=
  F (finiteBoxCluster ω U root)
    ((clusterRevealBonds U (finiteBoxCluster ω U root)).restrict ω)

private def fiberWeight {d : ℕ} (U C : Finset (Vertex d)) (root : Vertex d)
    (F : (clusterRevealBonds U C → Bool) → ℝ) (ω : Configuration d) : ℝ :=
  ({η | finiteBoxCluster η U root = C} : Set (Configuration d)).indicator
    (fun η => F ((clusterRevealBonds U C).restrict η)) ω

private lemma fiberWeight_local {d : ℕ} (U C : Finset (Vertex d))
    (root : Vertex d) (hroot : root ∈ U)
    (F : (clusterRevealBonds U C → Bool) → ℝ) (ω : Configuration d) :
    fiberWeight U C root F ω =
      (clusterRevealLocalEvent U C root).indicator F ((clusterRevealBonds U C).restrict ω) := by
  have he := clusterRevealLocalEvent_iff U C root hroot ω
  by_cases hc : finiteBoxCluster ω U root = C
  · have ha := he.mp hc
    simp [fiberWeight, hc, ha]
  · have ha : (clusterRevealBonds U C).restrict ω ∉ clusterRevealLocalEvent U C root :=
      fun h => hc (he.mpr h)
    simp [fiberWeight, hc, ha]

private lemma integrable_fiberWeight {d : ℕ} (p : unitInterval)
    (U C : Finset (Vertex d)) (root : Vertex d) (hroot : root ∈ U)
    (F : (clusterRevealBonds U C → Bool) → ℝ) :
    Integrable (fiberWeight U C root F) (percolation d p) := by
  have hi := percolation_cylinder_integrable d p (clusterRevealBonds U C)
    ((clusterRevealLocalEvent U C root).indicator F)
  exact hi.congr (ae_of_all _ (fun ω => (fiberWeight_local U C root hroot F ω).symm))

private lemma integrable_fiber_kernel {d : ℕ} (p : unitInterval)
    (U C : Finset (Vertex d)) (root : Vertex d) (hroot : root ∈ U)
    (G : Finset (Bond d)) (F : (clusterRevealBonds U C → Bool) → ℝ)
    (H : (G → Bool) → ℝ) :
    Integrable (fun ω => fiberWeight U C root F ω *
      (∫ ζ, H (G.restrict (resampleBonds (clusterRevealBonds U C) ω ζ))
        ∂percolation d p)) (percolation d p) := by
  simp_rw [integral_resampleBonds, fiberWeight_local U C root hroot F]
  exact integrable_two_block_product p _ _ _ _

private lemma revealWeight_sum {d : ℕ} (U : Finset (Vertex d)) (root : Vertex d)
    (F : ∀ C : Finset (Vertex d), (clusterRevealBonds U C → Bool) → ℝ)
    (ω : Configuration d) :
    (∑ C ∈ U.powerset, fiberWeight U C root (F C) ω) = clusterRevealWeight U root F ω := by
  rw [Finset.sum_eq_single (finiteBoxCluster ω U root)]
  · simp [fiberWeight, clusterRevealWeight]
  · intro C _ hC
    simp [fiberWeight, Ne.symm hC]
  · intro hC
    exact (hC (Finset.mem_powerset.mpr (finiteBoxCluster_subset ω U root))).elim

/-- The actual adaptive replacement preserves all finite cylinder expectations,
independently of every finite revealed-cluster observable. This is an iterated
expectation under two independent Bernoulli fields; no conditional division is used. -/
theorem clusterResample_weighted_factorization {d : ℕ} (p : unitInterval)
    (U : Finset (Vertex d)) (root : Vertex d) (hroot : root ∈ U)
    (G : Finset (Bond d))
    (F : ∀ C : Finset (Vertex d), (clusterRevealBonds U C → Bool) → ℝ)
    (H : (G → Bool) → ℝ) :
    (∫ ω, clusterRevealWeight U root F ω *
      (∫ ζ, H (G.restrict (clusterResample U root ω ζ)) ∂percolation d p)
      ∂percolation d p) =
    (∫ ω, clusterRevealWeight U root F ω ∂percolation d p) *
      (∫ ω, H (G.restrict ω) ∂percolation d p) := by
  have hp : ∀ ω : Configuration d,
      clusterRevealWeight U root F ω *
        (∫ ζ, H (G.restrict (clusterResample U root ω ζ)) ∂percolation d p) =
      ∑ C ∈ U.powerset, fiberWeight U C root (F C) ω *
        (∫ ζ, H (G.restrict (resampleBonds (clusterRevealBonds U C) ω ζ))
          ∂percolation d p) := by
    intro ω
    rw [← revealWeight_sum U root F ω, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro C _
    by_cases hc : finiteBoxCluster ω U root = C
    · simp_rw [clusterResample_of_cluster_eq U C root ω _ hc]
    · simp [fiberWeight, hc]
  simp_rw [hp]
  rw [integral_finsetSum _ (fun C _ => integrable_fiber_kernel p U C root hroot G (F C) H)]
  simp_rw [fiberWeight, clusterResample_fixed_fiber_factorization p U _ root hroot G]
  rw [← Finset.sum_mul]
  congr 1
  change (∑ C ∈ U.powerset, ∫ ω, fiberWeight U C root (F C) ω ∂percolation d p) = _
  rw [← integral_finsetSum _ (fun C _ => integrable_fiberWeight p U C root hroot (F C))]
  apply integral_congr_ae
  filter_upwards [] with ω
  exact revealWeight_sum U root F ω

/-- Actual adaptive replacement has the original Bernoulli expectation on every
finite set of coordinates. -/
theorem clusterResample_cylinder_expectation {d : ℕ} (p : unitInterval)
    (U : Finset (Vertex d)) (root : Vertex d) (hroot : root ∈ U)
    (G : Finset (Bond d)) (H : (G → Bool) → ℝ) :
    (∫ ω, ∫ ζ, H (G.restrict (clusterResample U root ω ζ))
      ∂percolation d p ∂percolation d p) =
      ∫ ω, H (G.restrict ω) ∂percolation d p := by
  simpa [clusterRevealWeight] using
    clusterResample_weighted_factorization p U root hroot G (fun _ _ => 1) H

end NearCritical
