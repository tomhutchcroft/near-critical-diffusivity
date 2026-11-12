module

public import NearCritical.ClusterDecoupling

/-! Actual rooted cluster-count moments for prop.num_spanning_new Step2.
Pair estimates consume the actual source decoupling proof, not a covariance input. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory ProbabilityTheory
open scoped Classical

def rootedPropertyIndicator {d : ℕ} (U : Finset (Vertex d))
    (P : SimpleGraph (Vertex d) → Finset (Vertex d) → Prop)
    (r : Vertex d) (ω : Configuration d) : ℝ :=
  if rootedClusterProperty U r P ω then 1 else 0

/-- Rooted count N, deliberately different from the number of distinct components. -/
def rootedPropertyCount {d : ℕ} (U Z : Finset (Vertex d))
    (P : SimpleGraph (Vertex d) → Finset (Vertex d) → Prop) (ω : Configuration d) : ℝ :=
  ∑ r ∈ Z, rootedPropertyIndicator U P r ω

def localRootedPropertyCount {d : ℕ} (U Z : Finset (Vertex d))
    (P : SimpleGraph (Vertex d) → Finset (Vertex d) → Prop)
    (ξ : internalBondSet U → Bool) : ℝ :=
  ∑ r ∈ Z, if localRootedClusterProperty U r P ξ then (1:ℝ) else 0

lemma rootedPropertyCount_cylinder {d : ℕ} (U Z : Finset (Vertex d)) (hZU : Z ⊆ U)
    (P : SimpleGraph (Vertex d) → Finset (Vertex d) → Prop) (ω : Configuration d) :
    rootedPropertyCount U Z P ω =
      localRootedPropertyCount U Z P ((internalBondSet U).restrict ω) := by
  apply Finset.sum_congr rfl
  intro r hr
  simp only [rootedPropertyIndicator, rootedClusterProperty_cylinder U r (hZU hr) P ω]

/-- All actual count moments are integrable, from finite-coordinate support. -/
lemma integrable_rootedPropertyCount_observable {d : ℕ} (p : unitInterval)
    (U Z : Finset (Vertex d)) (hZU : Z ⊆ U)
    (P : SimpleGraph (Vertex d) → Finset (Vertex d) → Prop) (f : ℝ → ℝ) :
    Integrable (fun ω => f (rootedPropertyCount U Z P ω)) (percolation d p) := by
  have hi := percolation_cylinder_integrable d p (internalBondSet U)
    (fun ξ => f (localRootedPropertyCount U Z P ξ))
  apply hi.congr
  filter_upwards [] with ω
  exact congrArg f (rootedPropertyCount_cylinder U Z hZU P ω).symm

lemma integrable_rootedPropertyIndicator {d : ℕ} (p : unitInterval)
    (U : Finset (Vertex d)) (r : Vertex d) (hr : r ∈ U)
    (P : SimpleGraph (Vertex d) → Finset (Vertex d) → Prop) :
    Integrable (rootedPropertyIndicator U P r) (percolation d p) := by
  convert! (integrable_const (μ := percolation d p) (1:ℝ)).indicator
    (measurableSet_rootedClusterProperty U r hr P) using 1

private lemma integral_rootedPropertyIndicator {d : ℕ} (p : unitInterval)
    (U : Finset (Vertex d)) (r : Vertex d) (hr : r ∈ U)
    (P : SimpleGraph (Vertex d) → Finset (Vertex d) → Prop) :
    (∫ ω, rootedPropertyIndicator U P r ω ∂percolation d p) =
      (percolation d p).real {ω | rootedClusterProperty U r P ω} := by
  convert! integral_indicator_one (μ := percolation d p)
    (measurableSet_rootedClusterProperty U r hr P) using 1

/-- Exact actual first moment; no expected-count hypothesis. -/
theorem integral_rootedPropertyCount {d : ℕ} (p : unitInterval)
    (U Z : Finset (Vertex d)) (hZU : Z ⊆ U)
    (P : SimpleGraph (Vertex d) → Finset (Vertex d) → Prop) :
    (∫ ω, rootedPropertyCount U Z P ω ∂percolation d p) =
      ∑ r ∈ Z, (percolation d p).real {ω | rootedClusterProperty U r P ω} := by
  simp only [rootedPropertyCount]
  rw [integral_finsetSum Z (fun r hr => integrable_rootedPropertyIndicator p U r (hZU hr) P)]
  apply Finset.sum_congr rfl
  intro r hr
  exact integral_rootedPropertyIndicator p U r (hZU hr) P

/-- Split an actual pair according to whether the roots lie in one component.
The connected case is dominated by the genuine unrestricted connection event. -/
lemma rootedProperty_pair_pointwise {d : ℕ} (U : Finset (Vertex d))
    (P : SimpleGraph (Vertex d) → Finset (Vertex d) → Prop)
    (r s : Vertex d) (ω : Configuration d) :
    rootedPropertyIndicator U P r ω * rootedPropertyIndicator U P s ω ≤
      (if ω ∈ connectionEvent r s then (1:ℝ) else 0) +
      (if rootedClusterProperty U r P ω then (1:ℝ) else 0) *
        (if rootedClusterProperty U s P ω ∧ s ∉ finiteBoxCluster ω U r then (1:ℝ) else 0) := by
  by_cases hp : rootedClusterProperty U r P ω
  · by_cases hq : rootedClusterProperty U s P ω
    · by_cases hn : s ∈ finiteBoxCluster ω U r
      · have hc : ω ∈ connectionEvent r s :=
          ((mem_finiteBoxCluster ω U r s).mp hn).2.mono
            (show restrictedGraph ω (U : Set (Vertex d)) ≤ openGraph ω from fun _ _ h => h.1)
        simp [rootedPropertyIndicator, hp, hq, hn, hc]
      · by_cases hc : ω ∈ connectionEvent r s <;>
          norm_num [rootedPropertyIndicator, hp, hq, hn, hc]
    · by_cases hc : ω ∈ connectionEvent r s <;>
        simp [rootedPropertyIndicator, hp, hq, hc]
  · by_cases hc : ω ∈ connectionEvent r s <;>
      simp [rootedPropertyIndicator, hp, hc]

private lemma integrable_property_pair {d : ℕ} (p : unitInterval)
    (U : Finset (Vertex d)) (r s : Vertex d) (hr : r ∈ U) (hs : s ∈ U)
    (P : SimpleGraph (Vertex d) → Finset (Vertex d) → Prop) :
    Integrable (fun ω => rootedPropertyIndicator U P r ω * rootedPropertyIndicator U P s ω)
      (percolation d p) := by
  have hi := percolation_cylinder_integrable d p (internalBondSet U)
    (fun ξ => (if localRootedClusterProperty U r P ξ then (1:ℝ) else 0) *
      (if localRootedClusterProperty U s P ξ then (1:ℝ) else 0))
  apply hi.congr
  filter_upwards [] with ω
  simp only [rootedPropertyIndicator, ← rootedClusterProperty_cylinder U r hr P ω,
    ← rootedClusterProperty_cylinder U s hs P ω]

private lemma integrable_property_nonconnection {d : ℕ} (p : unitInterval)
    (U : Finset (Vertex d)) (r s : Vertex d) (hr : r ∈ U) (hs : s ∈ U)
    (P : SimpleGraph (Vertex d) → Finset (Vertex d) → Prop) :
    Integrable (fun ω => (if rootedClusterProperty U r P ω then (1:ℝ) else 0) *
      (if rootedClusterProperty U s P ω ∧ s ∉ finiteBoxCluster ω U r then (1:ℝ) else 0))
      (percolation d p) := by
  have hi := percolation_cylinder_integrable d p (internalBondSet U)
    (fun ξ => (if localRootedClusterProperty U r P ξ then (1:ℝ) else 0) *
      (if localRootedClusterProperty U s P ξ ∧
        localRootedClusterProperty U r (fun _ C => s ∉ C) ξ then (1:ℝ) else 0))
  apply hi.congr
  filter_upwards [] with ω
  have hmem : rootedClusterProperty U r (fun _ C => s ∉ C) ω ↔
      s ∉ finiteBoxCluster ω U r := Iff.rfl
  simp only [← rootedClusterProperty_cylinder U r hr P ω,
    ← rootedClusterProperty_cylinder U s hs P ω,
    ← rootedClusterProperty_cylinder U r hr (fun _ C => s ∉ C) ω, hmem]

/-- Actual pair moment bound for the rooted count. The nonconnection part
consumes the actual source decoupling proof, with no pair/covariance premise. -/
theorem integral_rootedProperty_pair_le {d : ℕ} (p : unitInterval)
    (U : Finset (Vertex d)) (r s : Vertex d) (hr : r ∈ U) (hs : s ∈ U)
    (P : SimpleGraph (Vertex d) → Finset (Vertex d) → Prop) :
    (∫ ω, rootedPropertyIndicator U P r ω * rootedPropertyIndicator U P s ω
      ∂percolation d p) ≤
    (percolation d p).real {ω | rootedClusterProperty U r P ω} *
      (percolation d p).real {ω | rootedClusterProperty U s P ω} +
    (percolation d p).real (connectionEvent r s) +
    (∫ ω, rootedPropertyIndicator U P r ω *
      (∑ u ∈ finiteBoxCluster ω U r, (percolation d p).real (connectionEvent s u))
      ∂percolation d p) := by
  have hc : Integrable (fun ω : Configuration d =>
      if ω ∈ connectionEvent r s then (1:ℝ) else 0) (percolation d p) := by
    convert! (integrable_const (μ := percolation d p) (1:ℝ)).indicator
      (measurableSet_connectionEvent r s) using 1
  have hn := integrable_property_nonconnection p U r s hr hs P
  have h := integral_mono (integrable_property_pair p U r s hr hs P) (hc.add hn)
    (rootedProperty_pair_pointwise U P r s)
  replace h := h.trans_eq (integral_add hc hn)
  have he : (∫ ω : Configuration d,
      (if ω ∈ connectionEvent r s then (1:ℝ) else 0) ∂percolation d p) =
      (percolation d p).real (connectionEvent r s) := by
    convert! integral_indicator_one (μ := percolation d p) (measurableSet_connectionEvent r s) using 1
  rw [he] at h
  have hd := cluster_property_source_decoupling p U r s hr hs P P
  dsimp only [rootedPropertyIndicator] at h ⊢
  linarith

/-- Actual single-root event probability. -/
def rootedPropertyMean {d : ℕ} (p : unitInterval) (U : Finset (Vertex d))
    (P : SimpleGraph (Vertex d) → Finset (Vertex d) → Prop) (r : Vertex d) : ℝ :=
  (percolation d p).real {ω | rootedClusterProperty U r P ω}

/-- The actual source ordered-pair error: connection plus the computed
first-cluster-weighted two-point sum. This is not an assumed estimate. -/
def rootedPropertyPairError {d : ℕ} (p : unitInterval) (U : Finset (Vertex d))
    (P : SimpleGraph (Vertex d) → Finset (Vertex d) → Prop) (r s : Vertex d) : ℝ :=
  (percolation d p).real (connectionEvent r s) +
    ∫ ω, rootedPropertyIndicator U P r ω *
      (∑ u ∈ finiteBoxCluster ω U r, (percolation d p).real (connectionEvent s u))
      ∂percolation d p

private lemma integral_count_sq_eq_pairs {d : ℕ} (p : unitInterval)
    (U Z : Finset (Vertex d)) (hZU : Z ⊆ U)
    (P : SimpleGraph (Vertex d) → Finset (Vertex d) → Prop) :
    (∫ ω, (rootedPropertyCount U Z P ω)^2 ∂percolation d p) =
      ∑ r ∈ Z, ∑ s ∈ Z,
        ∫ ω, rootedPropertyIndicator U P r ω * rootedPropertyIndicator U P s ω
          ∂percolation d p := by
  have hp (ω : Configuration d) : (rootedPropertyCount U Z P ω)^2 =
      ∑ r ∈ Z, ∑ s ∈ Z,
        rootedPropertyIndicator U P r ω * rootedPropertyIndicator U P s ω := by
    simp only [rootedPropertyCount, pow_two, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
  simp_rw [hp]
  rw [integral_finsetSum Z (fun r hr => integrable_finsetSum Z
    (fun s hs => integrable_property_pair p U r s (hZU hr) (hZU hs) P))]
  apply Finset.sum_congr rfl
  intro r hr
  rw [integral_finsetSum Z (fun s hs => integrable_property_pair p U r s (hZU hr) (hZU hs) P)]

private lemma integral_pair_diagonal_split {d : ℕ} (p : unitInterval)
    (U : Finset (Vertex d)) (r s : Vertex d) (hr : r ∈ U) (hs : s ∈ U)
    (P : SimpleGraph (Vertex d) → Finset (Vertex d) → Prop) :
    (∫ ω, rootedPropertyIndicator U P r ω * rootedPropertyIndicator U P s ω
      ∂percolation d p) ≤
      rootedPropertyMean p U P r * rootedPropertyMean p U P s +
      (if r = s then rootedPropertyMean p U P r else 0) +
      (if r = s then 0 else rootedPropertyPairError p U P r s) := by
  by_cases he : r = s
  · subst s
    have hi : (∫ ω, rootedPropertyIndicator U P r ω * rootedPropertyIndicator U P r ω
        ∂percolation d p) = rootedPropertyMean p U P r := by
      calc
        _ = ∫ ω, rootedPropertyIndicator U P r ω ∂percolation d p := by
          apply integral_congr_ae
          filter_upwards [] with ω
          simp only [rootedPropertyIndicator]
          split_ifs <;> norm_num
        _ = _ := integral_rootedPropertyIndicator p U r hr P
    rw [hi]
    have hdiag : rootedPropertyMean p U P r ≤
        rootedPropertyMean p U P r * rootedPropertyMean p U P r + rootedPropertyMean p U P r := by
      nlinarith [mul_self_nonneg (rootedPropertyMean p U P r)]
    simpa using hdiag
  · have h := integral_rootedProperty_pair_le p U r s hr hs P
    simpa only [rootedPropertyMean, rootedPropertyPairError, ite_eq_right he, add_zero,
      zero_add, add_assoc] using h

/-- Actual source count second-moment bound. Its diagonal contribution is
E[N], not the number of possible roots. Off-diagonal errors are the computed
connection/random-cluster errors, derived without a covariance hypothesis. -/
theorem integral_rootedPropertyCount_sq_le {d : ℕ} (p : unitInterval)
    (U Z : Finset (Vertex d)) (hZU : Z ⊆ U)
    (P : SimpleGraph (Vertex d) → Finset (Vertex d) → Prop) :
    (∫ ω, (rootedPropertyCount U Z P ω)^2 ∂percolation d p) ≤
      (∫ ω, rootedPropertyCount U Z P ω ∂percolation d p)^2 +
      (∫ ω, rootedPropertyCount U Z P ω ∂percolation d p) +
      ∑ r ∈ Z, ∑ s ∈ Z, if r = s then 0 else rootedPropertyPairError p U P r s := by
  rw [integral_count_sq_eq_pairs p U Z hZU P]
  have hb : (∑ r ∈ Z, ∑ s ∈ Z,
      ∫ ω, rootedPropertyIndicator U P r ω * rootedPropertyIndicator U P s ω
        ∂percolation d p) ≤
      ∑ r ∈ Z, ∑ s ∈ Z,
        (rootedPropertyMean p U P r * rootedPropertyMean p U P s +
        (if r = s then rootedPropertyMean p U P r else 0) +
        (if r = s then 0 else rootedPropertyPairError p U P r s)) := by
    apply Finset.sum_le_sum
    intro r hr
    apply Finset.sum_le_sum
    intro s hs
    exact integral_pair_diagonal_split p U r s (hZU hr) (hZU hs) P
  have hprod : (∑ r ∈ Z, ∑ s ∈ Z,
      rootedPropertyMean p U P r * rootedPropertyMean p U P s) =
      (∑ r ∈ Z, rootedPropertyMean p U P r)^2 := by
    rw [pow_two, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro r _hr
    rw [Finset.mul_sum]
  have hdiag : (∑ r ∈ Z, ∑ s ∈ Z,
      if r = s then rootedPropertyMean p U P r else 0) =
      ∑ r ∈ Z, rootedPropertyMean p U P r := by
    apply Finset.sum_congr rfl
    intro r hr
    simp [hr]
  simp_rw [Finset.sum_add_distrib] at hb
  rw [hprod, hdiag] at hb
  simpa only [integral_rootedPropertyCount p U Z hZU P, rootedPropertyMean] using hb

end NearCritical
