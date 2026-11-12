module

public import NearCritical.ClusterCollision

/-! Actual nonmonotone cluster-property observables in the new spanning-count
decoupling argument. Their finite support is proved, not a premise. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory ProbabilityTheory
open scoped Classical

/-- Any property of the actual component and its whole induced graph is
invariant under changes outside the internal cube bonds. -/
lemma rootedClusterProperty_iff_of_internal_agree {d : ℕ}
    (U : Finset (Vertex d)) (root : Vertex d) (hr : root ∈ U)
    (P : SimpleGraph (Vertex d) → Finset (Vertex d) → Prop)
    (ω η : Configuration d) (ha : ∀ e ∈ internalBondSet U, ω e = η e) :
    rootedClusterProperty U root P ω ↔ rootedClusterProperty U root P η := by
  have hs : ∀ e ∈ clusterRevealBonds U (finiteBoxCluster ω U root), ω e = η e := by
    intro e he
    exact ha e (Finset.mem_filter.mp he).1
  have hc := finiteBoxCluster_eq_of_reveal_agree U (finiteBoxCluster ω U root) root hr rfl hs
  have hg := restrictedGraph_cluster_reveal_eq U (finiteBoxCluster ω U root)
    (finiteBoxCluster_subset ω U root) ω η hs
  simp only [rootedClusterProperty, hc, hg]

def localRootedClusterProperty {d : ℕ} (U : Finset (Vertex d)) (root : Vertex d)
    (P : SimpleGraph (Vertex d) → Finset (Vertex d) → Prop)
    (ξ : internalBondSet U → Bool) : Prop :=
  rootedClusterProperty U root P
    (extendConfiguration (internalBondSet U) (fun _ => false) ξ)

lemma rootedClusterProperty_cylinder {d : ℕ} (U : Finset (Vertex d))
    (root : Vertex d) (hr : root ∈ U)
    (P : SimpleGraph (Vertex d) → Finset (Vertex d) → Prop) (ω : Configuration d) :
    rootedClusterProperty U root P ω ↔
      localRootedClusterProperty U root P ((internalBondSet U).restrict ω) := by
  apply rootedClusterProperty_iff_of_internal_agree U root hr P
  intro e he
  simp [extendConfiguration, he, Finset.restrict]

theorem measurableSet_rootedClusterProperty {d : ℕ} (U : Finset (Vertex d))
    (root : Vertex d) (hr : root ∈ U)
    (P : SimpleGraph (Vertex d) → Finset (Vertex d) → Prop) :
    MeasurableSet {ω | rootedClusterProperty U root P ω} := by
  have he : {ω | rootedClusterProperty U root P ω} =
      (internalBondSet U).restrict ⁻¹' {ξ | localRootedClusterProperty U root P ξ} := by
    ext ω
    exact rootedClusterProperty_cylinder U root hr P ω
  rw [he]
  exact (Set.toFinite _).measurableSet.preimage (Finset.measurable_restrict _)

/-- The source's actual second-cluster indicator factors from ANY observable
of the originally revealed first cluster. Neither measurability nor the
replacement-law factorization is supplied as a hypothesis. -/
theorem clusterResample_property_expectation {d : ℕ} (p : unitInterval)
    (U : Finset (Vertex d)) (r s : Vertex d) (hr : r ∈ U) (hs : s ∈ U)
    (F : ∀ C : Finset (Vertex d), (clusterRevealBonds U C → Bool) → ℝ)
    (P : SimpleGraph (Vertex d) → Finset (Vertex d) → Prop) :
    (∫ ω, clusterRevealWeight U r F ω *
      (∫ ζ, (if rootedClusterProperty U s P (clusterResample U r ω ζ) then (1:ℝ) else 0)
        ∂percolation d p) ∂percolation d p) =
    (∫ ω, clusterRevealWeight U r F ω ∂percolation d p) *
      (percolation d p).real {ω | rootedClusterProperty U s P ω} := by
  let H : (internalBondSet U → Bool) → ℝ :=
    fun ξ => if localRootedClusterProperty U s P ξ then 1 else 0
  have hpoint (ω : Configuration d) : H ((internalBondSet U).restrict ω) =
      (if rootedClusterProperty U s P ω then (1:ℝ) else 0) := by
    simp only [H, ← rootedClusterProperty_cylinder U s hs P ω]
  have h := clusterResample_weighted_factorization p U r hr (internalBondSet U) F H
  simp_rw [hpoint] at h
  have hi : (∫ ω : Configuration d,
      (if rootedClusterProperty U s P ω then (1:ℝ) else 0) ∂percolation d p) =
      (percolation d p).real {ω | rootedClusterProperty U s P ω} := by
    convert! integral_indicator_one (μ := percolation d p)
      (measurableSet_rootedClusterProperty U s hs P) using 1
  rwa [hi] at h

/-- The actual first-cluster indicator expressed using only its label and
revealed incident bits. Background outside the mask is closed arbitrarily. -/
def revealedClusterPropertyWeight {d : ℕ} (U C : Finset (Vertex d))
    (P : SimpleGraph (Vertex d) → Finset (Vertex d) → Prop)
    (ξ : clusterRevealBonds U C → Bool) : ℝ :=
  if P (restrictedGraph
      (extendConfiguration (clusterRevealBonds U C) (fun _ => false) ξ)
      (C : Set (Vertex d))) C then 1 else 0

lemma clusterRevealWeight_property {d : ℕ} (U : Finset (Vertex d))
    (root : Vertex d) (P : SimpleGraph (Vertex d) → Finset (Vertex d) → Prop)
    (ω : Configuration d) :
    clusterRevealWeight U root (fun C => revealedClusterPropertyWeight U C P) ω =
      (if rootedClusterProperty U root P ω then (1:ℝ) else 0) := by
  have hg := restrictedGraph_cluster_reveal_eq U (finiteBoxCluster ω U root)
    (finiteBoxCluster_subset ω U root) ω
    (extendConfiguration (clusterRevealBonds U (finiteBoxCluster ω U root))
      (fun _ => false) ((clusterRevealBonds U (finiteBoxCluster ω U root)).restrict ω))
    (by intro e he; simp [extendConfiguration, he, Finset.restrict])
  simp only [clusterRevealWeight, revealedClusterPropertyWeight, rootedClusterProperty, ← hg]
  split_ifs with h <;> simp_all

/-- The actual original first-cluster event and actual replaced second-cluster
event factor exactly, including arbitrary nonmonotone intrinsic-graph tests. -/
theorem clusterResample_two_property_expectation {d : ℕ} (p : unitInterval)
    (U : Finset (Vertex d)) (r s : Vertex d) (hr : r ∈ U) (hs : s ∈ U)
    (P Q : SimpleGraph (Vertex d) → Finset (Vertex d) → Prop) :
    (∫ ω, (if rootedClusterProperty U r P ω then (1:ℝ) else 0) *
      (∫ ζ, (if rootedClusterProperty U s Q (clusterResample U r ω ζ) then (1:ℝ) else 0)
        ∂percolation d p) ∂percolation d p) =
    (percolation d p).real {ω | rootedClusterProperty U r P ω} *
      (percolation d p).real {ω | rootedClusterProperty U s Q ω} := by
  have h := clusterResample_property_expectation p U r s hr hs
    (fun C => revealedClusterPropertyWeight U C P) Q
  simp_rw [clusterRevealWeight_property] at h
  have hi : (∫ ω : Configuration d,
      (if rootedClusterProperty U r P ω then (1:ℝ) else 0) ∂percolation d p) =
      (percolation d p).real {ω | rootedClusterProperty U r P ω} := by
    convert! integral_indicator_one (μ := percolation d p)
      (measurableSet_rootedClusterProperty U r hr P) using 1
  rwa [hi] at h

/-- The source collision indicator is bounded by the sum of actual restricted
connection indicators to vertices of the original revealed component. -/
lemma clusterResample_collision_indicator_le_sum {d : ℕ}
    (U : Finset (Vertex d)) (r s : Vertex d) (ω ζ : Configuration d) :
    (if ¬Disjoint (finiteBoxCluster (clusterResample U r ω ζ) U s)
        (finiteBoxCluster ω U r) then (1:ℝ) else 0) ≤
      ∑ u ∈ finiteBoxCluster ω U r,
        if (restrictedGraph (clusterResample U r ω ζ) (U : Set (Vertex d))).Reachable s u
          then (1:ℝ) else 0 := by
  have hnonneg : ∀ u : Vertex d,
      0 ≤ (if (restrictedGraph (clusterResample U r ω ζ) (U : Set (Vertex d))).Reachable s u
          then (1:ℝ) else 0) := by
    intro u
    split_ifs <;> norm_num
  by_cases hc : ¬Disjoint (finiteBoxCluster (clusterResample U r ω ζ) U s)
      (finiteBoxCluster ω U r)
  · obtain ⟨u, hu, hreach⟩ := (clusterResample_collision_iff U r s ω ζ).mp hc
    have hsum := Finset.single_le_sum (fun v _ => hnonneg v) hu
    simpa [hc, hreach] using hsum
  · simp [hc]

/-- Integrability in the fresh field follows from its actual finite replacement
mask, even for an arbitrary observable of the resulting configuration. -/
lemma integrable_resample_observable {d : ℕ} (p : unitInterval)
    (S : Finset (Bond d)) (ω : Configuration d) (f : Configuration d → ℝ) :
    Integrable (fun ζ => f (resampleBonds S ω ζ)) (percolation d p) :=
  percolation_cylinder_integrable d p S (fun ξ => f (extendConfiguration S ω ξ))

/-- Actual pointwise conditional source comparison after averaging the fresh
field. The error is a finite sum of genuine replacement connection expectations,
not an assumed collision-probability bound. -/
theorem clusterResample_conditional_comparison {d : ℕ} (p : unitInterval)
    (U : Finset (Vertex d)) (r s : Vertex d) (hs : s ∈ U) (ω : Configuration d)
    (P : SimpleGraph (Vertex d) → Finset (Vertex d) → Prop) :
    (if rootedClusterProperty U s P ω ∧ s ∉ finiteBoxCluster ω U r then (1:ℝ) else 0) ≤
      (∫ ζ, (if rootedClusterProperty U s P (clusterResample U r ω ζ) then (1:ℝ) else 0)
        ∂percolation d p) +
      ∑ u ∈ finiteBoxCluster ω U r,
        ∫ ζ, (if (restrictedGraph (clusterResample U r ω ζ) (U : Set (Vertex d))).Reachable s u
          then (1:ℝ) else 0) ∂percolation d p := by
  let S := clusterRevealBonds U (finiteBoxCluster ω U r)
  have hi : Integrable (fun ζ =>
      (if rootedClusterProperty U s P (clusterResample U r ω ζ) then (1:ℝ) else 0))
      (percolation d p) := by
    convert! integrable_resample_observable p S ω
      (fun η => if rootedClusterProperty U s P η then (1 : ℝ) else 0) using 1 <;>
      simp only [clusterResample, S]
  have hj (u : Vertex d) : Integrable (fun ζ =>
      (if (restrictedGraph (clusterResample U r ω ζ) (U : Set (Vertex d))).Reachable s u
        then (1:ℝ) else 0)) (percolation d p) := by
    convert! integrable_resample_observable p S ω
      (fun η => if (restrictedGraph η (U : Set (Vertex d))).Reachable s u then (1 : ℝ) else 0) using 1 <;>
      simp only [clusterResample, S]
  have hb (ζ : Configuration d) := (clusterResample_indicator_le U r s hs ω ζ P).trans
    (add_le_add le_rfl (clusterResample_collision_indicator_le_sum U r s ω ζ))
  have h := integral_mono (integrable_const _) (hi.add
    (integrable_finsetSum _ (fun u _ => hj u))) hb
  have h' := h.trans_eq (integral_add hi (integrable_finsetSum _ (fun u _ => hj u)))
  rw [integral_finsetSum _ (fun u _ => hj u)] at h'
  simpa using h'

private lemma component_eq_of_internal_agree {d : ℕ} (U : Finset (Vertex d))
    (root : Vertex d) (hr : root ∈ U) (ω η : Configuration d)
    (ha : ∀ e ∈ internalBondSet U, ω e = η e) :
    finiteBoxCluster η U root = finiteBoxCluster ω U root := by
  apply finiteBoxCluster_eq_of_reveal_agree U (finiteBoxCluster ω U root) root hr rfl
  intro e he
  exact ha e (Finset.mem_filter.mp he).1

/-- Changing the original field outside the cube changes no internal coordinate
of the actual adaptive replacement. The random mask equality is derived. -/
lemma clusterResample_internal_agree {d : ℕ} (U : Finset (Vertex d))
    (r : Vertex d) (hr : r ∈ U) (ω η ζ : Configuration d)
    (ha : ∀ e ∈ internalBondSet U, ω e = η e) :
    ∀ e ∈ internalBondSet U, clusterResample U r ω ζ e = clusterResample U r η ζ e := by
  have hc := component_eq_of_internal_agree U r hr ω η ha
  intro e he
  simp only [clusterResample, hc, resampleBonds, extendConfiguration, Finset.restrict]
  split_ifs
  · rfl
  · exact ha e he

private lemma integrable_internal_invariant {d : ℕ} (p : unitInterval)
    (U : Finset (Vertex d)) (f : Configuration d → ℝ)
    (hf : ∀ ω η, (∀ e ∈ internalBondSet U, ω e = η e) → f ω = f η) :
    Integrable f (percolation d p) := by
  let g : (internalBondSet U → Bool) → ℝ :=
    fun ξ => f (extendConfiguration (internalBondSet U) (fun _ => false) ξ)
  have hi := percolation_cylinder_integrable d p (internalBondSet U) g
  apply hi.congr
  filter_upwards [] with ω
  exact (hf ω _ (by intro e he; simp [extendConfiguration, he, Finset.restrict])).symm

/-- Original-field integrability for the actual source product. Averaging over
the fresh field does not destroy finite support in the original field. -/
theorem integrable_clusterResample_property_product {d : ℕ} (p : unitInterval)
    (U : Finset (Vertex d)) (r s : Vertex d) (hr : r ∈ U) (hs : s ∈ U)
    (P Q : SimpleGraph (Vertex d) → Finset (Vertex d) → Prop) :
    Integrable (fun ω => (if rootedClusterProperty U r P ω then (1:ℝ) else 0) *
      (∫ ζ, (if rootedClusterProperty U s Q (clusterResample U r ω ζ) then (1:ℝ) else 0)
        ∂percolation d p)) (percolation d p) := by
  apply integrable_internal_invariant p U
  intro ω η ha
  have hp := rootedClusterProperty_iff_of_internal_agree U r hr P ω η ha
  have hk : (∫ ζ, (if rootedClusterProperty U s Q (clusterResample U r ω ζ)
        then (1:ℝ) else 0) ∂percolation d p) =
      (∫ ζ, (if rootedClusterProperty U s Q (clusterResample U r η ζ)
        then (1:ℝ) else 0) ∂percolation d p) := by
    apply integral_congr_ae
    filter_upwards [] with ζ
    have hq := rootedClusterProperty_iff_of_internal_agree U s hs Q
      (clusterResample U r ω ζ) (clusterResample U r η ζ)
      (clusterResample_internal_agree U r hr ω η ζ ha)
    simp only [hq]
  simp only [hp, hk]

/-- Actual termwise connection factorization, retaining the event that u
belongs to the originally revealed first component in its weight. -/
theorem clusterResample_member_expectation {d : ℕ} (p : unitInterval)
    (U : Finset (Vertex d)) (r s : Vertex d) (hr : r ∈ U) (hs : s ∈ U)
    (P : SimpleGraph (Vertex d) → Finset (Vertex d) → Prop) (u : Vertex d) :
    (∫ ω, (if rootedClusterProperty U r P ω then (1:ℝ) else 0) *
      (if u ∈ finiteBoxCluster ω U r then (1:ℝ) else 0) *
      (∫ ζ, (if u ∈ finiteBoxCluster (clusterResample U r ω ζ) U s then (1:ℝ) else 0)
        ∂percolation d p) ∂percolation d p) =
    (∫ ω, (if rootedClusterProperty U r P ω then (1:ℝ) else 0) *
      (if u ∈ finiteBoxCluster ω U r then (1:ℝ) else 0) ∂percolation d p) *
      (percolation d p).real {η | u ∈ finiteBoxCluster η U s} := by
  let F : ∀ C : Finset (Vertex d), (clusterRevealBonds U C → Bool) → ℝ :=
    fun C ξ => revealedClusterPropertyWeight U C P ξ * (if u ∈ C then 1 else 0)
  have hw (ω : Configuration d) : clusterRevealWeight U r F ω =
      (if rootedClusterProperty U r P ω then (1:ℝ) else 0) *
        (if u ∈ finiteBoxCluster ω U r then (1:ℝ) else 0) := by
    change clusterRevealWeight U r (fun C => revealedClusterPropertyWeight U C P) ω *
      (if u ∈ finiteBoxCluster ω U r then (1:ℝ) else 0) = _
    rw [clusterRevealWeight_property]
  have h := clusterResample_property_expectation p U r s hr hs F (fun _ C => u ∈ C)
  simp_rw [hw] at h
  have hmem (η : Configuration d) : rootedClusterProperty U s (fun _ C => u ∈ C) η ↔
      u ∈ finiteBoxCluster η U s := Iff.rfl
  simp_rw [hmem] at h
  exact h

/-- The same termwise identity for the literal restricted two-point event. -/
theorem clusterResample_connection_expectation {d : ℕ} (p : unitInterval)
    (U : Finset (Vertex d)) (r s : Vertex d) (hr : r ∈ U) (hs : s ∈ U)
    (P : SimpleGraph (Vertex d) → Finset (Vertex d) → Prop)
    (u : Vertex d) (hu : u ∈ U) :
    (∫ ω, (if rootedClusterProperty U r P ω then (1:ℝ) else 0) *
      (if u ∈ finiteBoxCluster ω U r then (1:ℝ) else 0) *
      (∫ ζ, (if (restrictedGraph (clusterResample U r ω ζ) (U : Set (Vertex d))).Reachable s u
        then (1:ℝ) else 0) ∂percolation d p) ∂percolation d p) =
    (∫ ω, (if rootedClusterProperty U r P ω then (1:ℝ) else 0) *
      (if u ∈ finiteBoxCluster ω U r then (1:ℝ) else 0) ∂percolation d p) *
      (percolation d p).real {η | (restrictedGraph η (U : Set (Vertex d))).Reachable s u} := by
  simpa only [mem_finiteBoxCluster, hu, true_and] using
    clusterResample_member_expectation p U r s hr hs P u

private lemma member_kernel_invariant {d : ℕ} (p : unitInterval)
    (U : Finset (Vertex d)) (r s : Vertex d) (hr : r ∈ U) (hs : s ∈ U)
    (u : Vertex d) (ω η : Configuration d)
    (ha : ∀ e ∈ internalBondSet U, ω e = η e) :
    (∫ ζ, (if u ∈ finiteBoxCluster (clusterResample U r ω ζ) U s then (1:ℝ) else 0)
      ∂percolation d p) =
    (∫ ζ, (if u ∈ finiteBoxCluster (clusterResample U r η ζ) U s then (1:ℝ) else 0)
      ∂percolation d p) := by
  apply integral_congr_ae
  filter_upwards [] with ζ
  have hc := component_eq_of_internal_agree U s hs
    (clusterResample U r ω ζ) (clusterResample U r η ζ)
    (clusterResample_internal_agree U r hr ω η ζ ha)
  simp only [hc]

private lemma integrable_member_product {d : ℕ} (p : unitInterval)
    (U : Finset (Vertex d)) (r s : Vertex d) (hr : r ∈ U) (hs : s ∈ U)
    (P : SimpleGraph (Vertex d) → Finset (Vertex d) → Prop) (u : Vertex d) :
    Integrable (fun ω => (if rootedClusterProperty U r P ω then (1:ℝ) else 0) *
      (if u ∈ finiteBoxCluster ω U r then (1:ℝ) else 0) *
      (∫ ζ, (if u ∈ finiteBoxCluster (clusterResample U r ω ζ) U s then (1:ℝ) else 0)
        ∂percolation d p)) (percolation d p) := by
  apply integrable_internal_invariant p U
  intro ω η ha
  have hp := rootedClusterProperty_iff_of_internal_agree U r hr P ω η ha
  have hc := component_eq_of_internal_agree U r hr ω η ha
  have hk := member_kernel_invariant p U r s hr hs u ω η ha
  simp only [hp, hc, hk]

private lemma cluster_weighted_sum_eq {d : ℕ} (U : Finset (Vertex d))
    (r : Vertex d) (ω : Configuration d) (a : ℝ) (f : Vertex d → ℝ) :
    a * (∑ u ∈ finiteBoxCluster ω U r, f u) =
      ∑ u ∈ U, a * (if u ∈ finiteBoxCluster ω U r then (1:ℝ) else 0) * f u := by
  calc
    _ = ∑ u ∈ finiteBoxCluster ω U r, a * f u := Finset.mul_sum _ _ _
    _ = ∑ u ∈ finiteBoxCluster ω U r,
        a * (if u ∈ finiteBoxCluster ω U r then (1:ℝ) else 0) * f u := by
      apply Finset.sum_congr rfl
      intro u hu
      simp [hu]
    _ = _ := Finset.sum_subset (finiteBoxCluster_subset ω U r) (by
      intro u _hu hn
      simp [hn])

/-- Exact reduction of the source random-cluster collision-error sum after
averaging both fields. All sums are over actual finite components, and all
finite-sum/integral exchanges have derived integrability. -/
theorem clusterResample_member_error_expectation {d : ℕ} (p : unitInterval)
    (U : Finset (Vertex d)) (r s : Vertex d) (hr : r ∈ U) (hs : s ∈ U)
    (P : SimpleGraph (Vertex d) → Finset (Vertex d) → Prop) :
    (∫ ω, (if rootedClusterProperty U r P ω then (1:ℝ) else 0) *
      (∑ u ∈ finiteBoxCluster ω U r,
        ∫ ζ, (if u ∈ finiteBoxCluster (clusterResample U r ω ζ) U s then (1:ℝ) else 0)
          ∂percolation d p) ∂percolation d p) =
    ∑ u ∈ U,
      (∫ ω, (if rootedClusterProperty U r P ω then (1:ℝ) else 0) *
        (if u ∈ finiteBoxCluster ω U r then (1:ℝ) else 0) ∂percolation d p) *
        (percolation d p).real {η | u ∈ finiteBoxCluster η U s} := by
  simp_rw [cluster_weighted_sum_eq]
  rw [integral_finsetSum _ (fun u _ => integrable_member_product p U r s hr hs P u)]
  apply Finset.sum_congr rfl
  intro u _hu
  exact clusterResample_member_expectation p U r s hr hs P u

private lemma connection_member_error_sum_eq {d : ℕ} (p : unitInterval)
    (U : Finset (Vertex d)) (r s : Vertex d) (ω : Configuration d) :
    (∑ u ∈ finiteBoxCluster ω U r,
      ∫ ζ, (if (restrictedGraph (clusterResample U r ω ζ) (U : Set (Vertex d))).Reachable s u
        then (1:ℝ) else 0) ∂percolation d p) =
    (∑ u ∈ finiteBoxCluster ω U r,
      ∫ ζ, (if u ∈ finiteBoxCluster (clusterResample U r ω ζ) U s then (1:ℝ) else 0)
        ∂percolation d p) := by
  apply Finset.sum_congr rfl
  intro u hu
  have huU := finiteBoxCluster_subset ω U r hu
  apply integral_congr_ae
  filter_upwards [] with ζ
  simp only [mem_finiteBoxCluster, huU, true_and]

/-- The source replacement collision error reduces to actual restricted
connection probabilities, with the random first-component membership retained. -/
theorem clusterResample_connection_error_expectation {d : ℕ} (p : unitInterval)
    (U : Finset (Vertex d)) (r s : Vertex d) (hr : r ∈ U) (hs : s ∈ U)
    (P : SimpleGraph (Vertex d) → Finset (Vertex d) → Prop) :
    (∫ ω, (if rootedClusterProperty U r P ω then (1:ℝ) else 0) *
      (∑ u ∈ finiteBoxCluster ω U r,
        ∫ ζ, (if (restrictedGraph (clusterResample U r ω ζ) (U : Set (Vertex d))).Reachable s u
          then (1:ℝ) else 0) ∂percolation d p) ∂percolation d p) =
    ∑ u ∈ U,
      (∫ ω, (if rootedClusterProperty U r P ω then (1:ℝ) else 0) *
        (if u ∈ finiteBoxCluster ω U r then (1:ℝ) else 0) ∂percolation d p) *
        (percolation d p).real {η | (restrictedGraph η (U : Set (Vertex d))).Reachable s u} := by
  simp_rw [connection_member_error_sum_eq]
  rw [clusterResample_member_error_expectation p U r s hr hs P]
  apply Finset.sum_congr rfl
  intro u hu
  simp only [mem_finiteBoxCluster, hu, true_and]

/-- Actual source nonconnection covariance bound. Every conditional freshness,
component comparison, indicator factorization and integrability input has been
proved above; no desired covariance estimate is a premise. The finite error
uses restricted two-point probabilities and is stronger than the global one. -/
theorem cluster_property_nonconnection_bound {d : ℕ} (p : unitInterval)
    (U : Finset (Vertex d)) (r s : Vertex d) (hr : r ∈ U) (hs : s ∈ U)
    (P Q : SimpleGraph (Vertex d) → Finset (Vertex d) → Prop) :
    (∫ ω, (if rootedClusterProperty U r P ω then (1:ℝ) else 0) *
      (if rootedClusterProperty U s Q ω ∧ s ∉ finiteBoxCluster ω U r then (1:ℝ) else 0)
      ∂percolation d p) ≤
    (percolation d p).real {ω | rootedClusterProperty U r P ω} *
      (percolation d p).real {ω | rootedClusterProperty U s Q ω} +
    ∑ u ∈ U,
      (∫ ω, (if rootedClusterProperty U r P ω then (1:ℝ) else 0) *
        (if u ∈ finiteBoxCluster ω U r then (1:ℝ) else 0) ∂percolation d p) *
        (percolation d p).real {η | (restrictedGraph η (U : Set (Vertex d))).Reachable s u} := by
  have hL : Integrable (fun ω => (if rootedClusterProperty U r P ω then (1:ℝ) else 0) *
      (if rootedClusterProperty U s Q ω ∧ s ∉ finiteBoxCluster ω U r then (1:ℝ) else 0))
      (percolation d p) := by
    apply integrable_internal_invariant p U
    intro ω η ha
    have hp := rootedClusterProperty_iff_of_internal_agree U r hr P ω η ha
    have hq := rootedClusterProperty_iff_of_internal_agree U s hs Q ω η ha
    have hc := component_eq_of_internal_agree U r hr ω η ha
    simp only [hp, hq, hc]
  have hR := integrable_clusterResample_property_product p U r s hr hs P Q
  have he (ω : Configuration d) :
      (if rootedClusterProperty U r P ω then (1:ℝ) else 0) *
      (∑ u ∈ finiteBoxCluster ω U r,
        ∫ ζ, (if (restrictedGraph (clusterResample U r ω ζ) (U : Set (Vertex d))).Reachable s u
          then (1:ℝ) else 0) ∂percolation d p) =
      ∑ u ∈ U, (if rootedClusterProperty U r P ω then (1:ℝ) else 0) *
        (if u ∈ finiteBoxCluster ω U r then (1:ℝ) else 0) *
        (∫ ζ, (if u ∈ finiteBoxCluster (clusterResample U r ω ζ) U s then (1:ℝ) else 0)
          ∂percolation d p) := by
    rw [connection_member_error_sum_eq]
    exact cluster_weighted_sum_eq U r ω _ _
  have hE : Integrable (fun ω => (if rootedClusterProperty U r P ω then (1:ℝ) else 0) *
      (∑ u ∈ finiteBoxCluster ω U r,
        ∫ ζ, (if (restrictedGraph (clusterResample U r ω ζ) (U : Set (Vertex d))).Reachable s u
          then (1:ℝ) else 0) ∂percolation d p)) (percolation d p) := by
    have hi := integrable_finsetSum U (fun u _ => integrable_member_product p U r s hr hs P u)
    exact hi.congr (ae_of_all _ (fun ω => (he ω).symm))
  have hb (ω : Configuration d) := mul_le_mul_of_nonneg_left
    (clusterResample_conditional_comparison p U r s hs ω Q)
    (show 0 ≤ (if rootedClusterProperty U r P ω then (1:ℝ) else 0) by split_ifs <;> norm_num)
  simp_rw [mul_add] at hb
  have h := integral_mono hL (hR.add hE) hb
  have hsplit := integral_add hR hE
  have h' := h.trans_eq hsplit
  rw [clusterResample_two_property_expectation p U r s hr hs P Q,
    clusterResample_connection_error_expectation p U r s hr hs P] at h'
  exact h'

/-- Enlarging restricted connections to unrestricted connections gives the
paper's ordinary two-point error, still with exact original-cluster weights. -/
theorem cluster_property_nonconnection_global_bound {d : ℕ} (p : unitInterval)
    (U : Finset (Vertex d)) (r s : Vertex d) (hr : r ∈ U) (hs : s ∈ U)
    (P Q : SimpleGraph (Vertex d) → Finset (Vertex d) → Prop) :
    (∫ ω, (if rootedClusterProperty U r P ω then (1:ℝ) else 0) *
      (if rootedClusterProperty U s Q ω ∧ s ∉ finiteBoxCluster ω U r then (1:ℝ) else 0)
      ∂percolation d p) ≤
    (percolation d p).real {ω | rootedClusterProperty U r P ω} *
      (percolation d p).real {ω | rootedClusterProperty U s Q ω} +
    ∑ u ∈ U,
      (∫ ω, (if rootedClusterProperty U r P ω then (1:ℝ) else 0) *
        (if u ∈ finiteBoxCluster ω U r then (1:ℝ) else 0) ∂percolation d p) *
        (percolation d p).real (connectionEvent s u) := by
  apply (cluster_property_nonconnection_bound p U r s hr hs P Q).trans
  apply add_le_add le_rfl
  apply Finset.sum_le_sum
  intro u _hu
  apply mul_le_mul_of_nonneg_left
  · refine measureReal_mono ?_ (measure_ne_top _ _)
    intro η hη
    exact hη.mono (show restrictedGraph η (U : Set (Vertex d)) ≤ openGraph η from
      fun _ _ h => h.1)
  · apply integral_nonneg
    intro ω
    apply mul_nonneg <;> split_ifs <;> norm_num

/-- Literal source prop.num_spanning_new Step2 decoupling inequality. Both
actual cluster indicators and the random-cluster two-point error are computed
in the project's Bernoulli law; no conditional-independence or covariance
estimate is a premise. -/
theorem cluster_property_source_decoupling {d : ℕ} (p : unitInterval)
    (U : Finset (Vertex d)) (r s : Vertex d) (hr : r ∈ U) (hs : s ∈ U)
    (P Q : SimpleGraph (Vertex d) → Finset (Vertex d) → Prop) :
    (∫ ω, (if rootedClusterProperty U r P ω then (1:ℝ) else 0) *
      (if rootedClusterProperty U s Q ω ∧ s ∉ finiteBoxCluster ω U r then (1:ℝ) else 0)
      ∂percolation d p) ≤
    (percolation d p).real {ω | rootedClusterProperty U r P ω} *
      (percolation d p).real {ω | rootedClusterProperty U s Q ω} +
    (∫ ω, (if rootedClusterProperty U r P ω then (1:ℝ) else 0) *
      (∑ u ∈ finiteBoxCluster ω U r, (percolation d p).real (connectionEvent s u))
      ∂percolation d p) := by
  have hi (u : Vertex d) : Integrable (fun ω =>
      (if rootedClusterProperty U r P ω then (1:ℝ) else 0) *
      (if u ∈ finiteBoxCluster ω U r then (1:ℝ) else 0) *
      (percolation d p).real (connectionEvent s u)) (percolation d p) := by
    apply integrable_internal_invariant p U
    intro ω η ha
    have hp := rootedClusterProperty_iff_of_internal_agree U r hr P ω η ha
    have hc := component_eq_of_internal_agree U r hr ω η ha
    simp only [hp, hc]
  have he : (∫ ω, (if rootedClusterProperty U r P ω then (1:ℝ) else 0) *
      (∑ u ∈ finiteBoxCluster ω U r, (percolation d p).real (connectionEvent s u))
      ∂percolation d p) =
      ∑ u ∈ U,
        (∫ ω, (if rootedClusterProperty U r P ω then (1:ℝ) else 0) *
          (if u ∈ finiteBoxCluster ω U r then (1:ℝ) else 0) ∂percolation d p) *
          (percolation d p).real (connectionEvent s u) := by
    simp_rw [cluster_weighted_sum_eq]
    rw [integral_finsetSum U (fun u _ => hi u)]
    apply Finset.sum_congr rfl
    intro u _hu
    rw [integral_mul_const]
  rw [he]
  exact cluster_property_nonconnection_global_bound p U r s hr hs P Q

end NearCritical
