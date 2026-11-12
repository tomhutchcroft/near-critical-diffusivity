module

public import NearCritical.FiniteClusterFamily
public import NearCritical.BulkDomain
public import NearCritical.NestFreshTube
public import NearCritical.CylinderDisjointOccurrence

/-! Actual cluster reveal support for NEW prop.num_spanning_new Step2.
The cluster event is proved to depend only on cube bonds incident to that
cluster, allowing product-law freshness on the untouched finite block. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory
open scoped Classical

/-- Both endpoints in U and at least one in the revealed component C. Includes
closed crossing bonds, not only internal open edges of C or issued bonds. -/
def clusterRevealBonds {d : ℕ} (U C : Finset (Vertex d)) : Finset (Bond d) :=
  (internalBondSet U).filter fun e => e.1 ∈ C ∨ bondTip e ∈ C

lemma mem_clusterRevealBonds {d : ℕ} (U C : Finset (Vertex d)) (e : Bond d) :
    e ∈ clusterRevealBonds U C ↔ e.1 ∈ U ∧ bondTip e ∈ U ∧ (e.1 ∈ C ∨ bondTip e ∈ C) := by
  simp [clusterRevealBonds, mem_internalBondSet, and_assoc]

/-- Agreement on incident cube bonds preserves adjacency from a vertex in C. -/
lemma openAdj_of_clusterReveal_agree {d : ℕ} (U C : Finset (Vertex d))
    {ω η : Configuration d} (hagree : ∀ e ∈ clusterRevealBonds U C, ω e = η e)
    {x y : Vertex d} (hxC : x ∈ C) (hxU : x ∈ U) (hyU : y ∈ U)
    (hxy : (openGraph ω).Adj x y) : (openGraph η).Adj x y := by
  obtain ⟨e, he, hends | hends⟩ := hxy
  · obtain ⟨rfl, rfl⟩ := hends
    have hs := (mem_clusterRevealBonds U C e).mpr ⟨hxU, hyU, Or.inl hxC⟩
    exact ⟨e, (hagree e hs).symm.trans he, Or.inl ⟨rfl,rfl⟩⟩
  · obtain ⟨rfl, rfl⟩ := hends
    have hs := (mem_clusterRevealBonds U C e).mpr ⟨hyU, hxU, Or.inr hxC⟩
    exact ⟨e, (hagree e hs).symm.trans he, Or.inr ⟨rfl,rfl⟩⟩

/-- Arbitrary outside changes preserve the actual component, including its
closed edge boundary. No increasingness/cluster-property hypothesis is used. -/
theorem finiteBoxCluster_eq_of_reveal_agree {d : ℕ} (U C : Finset (Vertex d))
    (root : Vertex d) (hroot : root ∈ U) {ω η : Configuration d}
    (hC : finiteBoxCluster ω U root = C)
    (hagree : ∀ e ∈ clusterRevealBonds U C, ω e = η e) :
    finiteBoxCluster η U root = C := by
  have hCU : C ⊆ U := by rw [←hC]; exact finiteBoxCluster_subset ω U root
  have hrC : root ∈ C := by rw [←hC]; exact root_mem_finiteBoxCluster ω U hroot
  have hclosed {x y : Vertex d} (hx : x ∈ C)
      (hxy : (restrictedGraph η (U : Set (Vertex d))).Adj x y) : y ∈ C := by
    have hadj := openAdj_of_clusterReveal_agree U C
      (fun e he => (hagree e he).symm) hx hxy.2.1 hxy.2.2 hxy.1
    have hrx : (restrictedGraph ω (U : Set (Vertex d))).Reachable root x :=
      ((mem_finiteBoxCluster ω U root x).mp (by rwa [hC])).2
    rw [←hC]
    exact (mem_finiteBoxCluster ω U root y).mpr ⟨hxy.2.2, hrx.trans
      (SimpleGraph.Adj.reachable ⟨hadj, hxy.2.1, hxy.2.2⟩)⟩
  have hstay {x y : Vertex d} (hxy : (restrictedGraph η (U : Set (Vertex d))).Reachable x y) :
      x ∈ C → y ∈ C := by
    obtain ⟨w⟩ := hxy
    induction w with
    | nil => exact id
    | cons hadj w ih => exact fun hx => ih (hclosed hx hadj)
  apply Finset.Subset.antisymm
  · intro y hy
    exact hstay ((mem_finiteBoxCluster η U root y).mp hy).2 hrC
  · intro y hy
    have hle : restrictedGraph ω (C : Set (Vertex d)) ≤ restrictedGraph η (U : Set (Vertex d)) := by
      rintro x z ⟨hxz, hx, hz⟩
      exact ⟨openAdj_of_clusterReveal_agree U C hagree hx (hCU hx) (hCU hz) hxz, hCU hx, hCU hz⟩
    have hr : (restrictedGraph ω (C : Set (Vertex d))).Reachable root y := by
      rw [←hC]
      exact finiteBoxCluster_induced_reachable ω U root
        (root_mem_finiteBoxCluster ω U hroot) (by rwa [hC])
    exact (mem_finiteBoxCluster η U root y).mpr ⟨hCU hy, hr.mono hle⟩

theorem finiteBoxCluster_eq_iff_reveal_agree {d : ℕ} (U C : Finset (Vertex d))
    (root : Vertex d) (hroot : root ∈ U) (ω η : Configuration d)
    (hagree : ∀ e ∈ clusterRevealBonds U C, ω e = η e) :
    finiteBoxCluster ω U root = C ↔ finiteBoxCluster η U root = C :=
  ⟨fun h => finiteBoxCluster_eq_of_reveal_agree U C root hroot h hagree,
    fun h => finiteBoxCluster_eq_of_reveal_agree U C root hroot h (fun e he => (hagree e he).symm)⟩

/-- Evaluate the actual component event after closing every bond outside the
fixed revealed mask. Outside values are irrelevant by the theorem above. -/
def clusterRevealLocalEvent {d : ℕ} (U C : Finset (Vertex d)) (root : Vertex d) :
    Set (clusterRevealBonds U C → Bool) :=
  {ξ | finiteBoxCluster (extendConfiguration (clusterRevealBonds U C) (fun _ => false) ξ) U root = C}

lemma clusterRevealLocalEvent_iff {d : ℕ} (U C : Finset (Vertex d))
    (root : Vertex d) (hroot : root ∈ U) (ω : Configuration d) :
    finiteBoxCluster ω U root = C ↔
      (clusterRevealBonds U C).restrict ω ∈ clusterRevealLocalEvent U C root := by
  apply finiteBoxCluster_eq_iff_reveal_agree U C root hroot
  intro e he
  simp [extendConfiguration, he, Finset.restrict]

/-- Actual component equality is a proved finite cylinder on the REVEALED
incident mask, not an assumed event-independence conclusion. -/
theorem clusterReveal_event_cylinder {d : ℕ} (U C : Finset (Vertex d))
    (root : Vertex d) (hroot : root ∈ U) :
    {ω | finiteBoxCluster ω U root = C} =
      (clusterRevealBonds U C).restrict ⁻¹' clusterRevealLocalEvent U C root := by
  ext ω
  exact clusterRevealLocalEvent_iff U C root hroot ω

lemma measurableSet_clusterReveal_event {d : ℕ} (U C : Finset (Vertex d))
    (root : Vertex d) (hroot : root ∈ U) :
    MeasurableSet {ω | finiteBoxCluster ω U root = C} := by
  rw [clusterReveal_event_cylinder U C root hroot]
  exact (Set.toFinite (clusterRevealLocalEvent U C root)).measurableSet.preimage
    (Finset.measurable_restrict _)

/-- The finite cube bonds with NO endpoint in the revealed cluster. -/
def clusterUnrevealedBonds {d : ℕ} (U C : Finset (Vertex d)) : Finset (Bond d) :=
  internalBondSet U \ clusterRevealBonds U C

lemma clusterReveal_unrevealed_disjoint {d : ℕ} (U C : Finset (Vertex d)) :
    Disjoint (clusterRevealBonds U C) (clusterUnrevealedBonds U C) := by
  apply Finset.disjoint_left.mpr
  intro e he hT
  exact (Finset.mem_sdiff.mp hT).2 he

lemma clusterRevealBonds_eq_explored {d : ℕ} (U C : Finset (Vertex d)) :
    (clusterRevealBonds U C : Set (Bond d)) = exploredBondSet (U : Set (Vertex d)) (C : Set (Vertex d)) := by
  ext e
  rw [Finset.mem_coe, mem_clusterRevealBonds, mem_exploredBondSet]
  rfl

lemma clusterUnrevealedBonds_eq_internal_diff {d : ℕ} (U C : Finset (Vertex d)) :
    clusterUnrevealedBonds U C = internalBondSet (U \ C) := by
  ext e
  simp only [clusterUnrevealedBonds, Finset.mem_sdiff, mem_internalBondSet, mem_clusterRevealBonds]
  tauto

/-- Entire induced open-graph data on C are retained by the reveal mask. -/
lemma restrictedGraph_cluster_reveal_eq {d : ℕ} (U C : Finset (Vertex d)) (hCU : C ⊆ U)
    (ω η : Configuration d) (hagree : ∀ e ∈ clusterRevealBonds U C, ω e = η e) :
    restrictedGraph ω (C : Set (Vertex d)) = restrictedGraph η (C : Set (Vertex d)) := by
  apply le_antisymm
  · rintro x y ⟨hxy, hx, hy⟩
    exact ⟨openAdj_of_clusterReveal_agree U C hagree hx (hCU hx) (hCU hy) hxy, hx, hy⟩
  · rintro x y ⟨hxy, hx, hy⟩
    exact ⟨openAdj_of_clusterReveal_agree U C (fun e he => (hagree e he).symm)
      hx (hCU hx) (hCU hy) hxy, hx, hy⟩

/-- A property of the actual component's internal graph AND vertex set. -/
def clusterGraphPropertyEvent {d : ℕ} (U C : Finset (Vertex d)) (root : Vertex d)
    (P : SimpleGraph (Vertex d) → Finset (Vertex d) → Prop) : Set (Configuration d) :=
  {ω | finiteBoxCluster ω U root = C ∧ P (restrictedGraph ω (C : Set (Vertex d))) C}

def clusterGraphPropertyLocalEvent {d : ℕ} (U C : Finset (Vertex d)) (root : Vertex d)
    (P : SimpleGraph (Vertex d) → Finset (Vertex d) → Prop) : Set (clusterRevealBonds U C → Bool) :=
  {ξ | extendConfiguration (clusterRevealBonds U C) (fun _ => false) ξ ∈
    clusterGraphPropertyEvent U C root P}

/-- Nonmonotone component properties, including internal-distance tests, have
PROVED reveal support. No measurability or locality premise about P is needed. -/
theorem clusterGraphProperty_event_cylinder {d : ℕ} (U C : Finset (Vertex d)) (hCU : C ⊆ U)
    (root : Vertex d) (hroot : root ∈ U)
    (P : SimpleGraph (Vertex d) → Finset (Vertex d) → Prop) :
    clusterGraphPropertyEvent U C root P =
      (clusterRevealBonds U C).restrict ⁻¹' clusterGraphPropertyLocalEvent U C root P := by
  ext ω
  let η := extendConfiguration (clusterRevealBonds U C) (fun _ => false)
    ((clusterRevealBonds U C).restrict ω)
  have hagree : ∀ e ∈ clusterRevealBonds U C, ω e = η e := by
    intro e he
    simp [η, extendConfiguration, he, Finset.restrict]
  have hcluster := finiteBoxCluster_eq_iff_reveal_agree U C root hroot ω η hagree
  have hgraph := restrictedGraph_cluster_reveal_eq U C hCU ω η hagree
  change (finiteBoxCluster ω U root = C ∧ P (restrictedGraph ω (C : Set (Vertex d))) C) ↔
    (finiteBoxCluster η U root = C ∧ P (restrictedGraph η (C : Set (Vertex d))) C)
  apply and_congr hcluster
  rw [hgraph]

lemma measurableSet_clusterGraphProperty_event {d : ℕ} (U C : Finset (Vertex d)) (hCU : C ⊆ U)
    (root : Vertex d) (hroot : root ∈ U)
    (P : SimpleGraph (Vertex d) → Finset (Vertex d) → Prop) :
    MeasurableSet (clusterGraphPropertyEvent U C root P) := by
  rw [clusterGraphProperty_event_cylinder U C hCU root hroot P]
  exact (Set.toFinite (clusterGraphPropertyLocalEvent U C root P)).measurableSet.preimage
    (Finset.measurable_restrict _)

private theorem revealCylinder_fresh_factorization {d : ℕ} (p : unitInterval)
    (S T : Finset (Bond d)) (hd : Disjoint S T) (E : Set (Configuration d))
    (A : Set (S → Bool)) (hE : E = S.restrict ⁻¹' A)
    (F : (S → Bool) → ℝ) (H : (T → Bool) → ℝ) :
    (∫ ω : Configuration d, E.indicator (fun η => F (S.restrict η)) ω * H (T.restrict ω)
      ∂percolation d p) =
    (∫ ω : Configuration d, E.indicator (fun η => F (S.restrict η)) ω ∂percolation d p) *
      (∫ ω : Configuration d, H (T.restrict ω) ∂percolation d p) := by
  have hI (ω : Configuration d) : E.indicator (fun η => F (S.restrict η)) ω =
      A.indicator F (S.restrict ω) := by
    have hm : ω ∈ E ↔ S.restrict ω ∈ A := Set.ext_iff.mp hE ω
    by_cases hω : ω ∈ E
    · have hA := hm.mp hω
      simp [hω, hA]
    · have hA : S.restrict ω ∉ A := fun h => hω (hm.mpr h)
      simp [hω, hA]
  let g := E.indicator (fun η => F (S.restrict η))
  have hg : g = fun ω => A.indicator F (S.restrict ω) := funext hI
  change (∫ ω, g ω * H (T.restrict ω) ∂percolation d p) =
    (∫ ω, g ω ∂percolation d p) * (∫ ω, H (T.restrict ω) ∂percolation d p)
  simp only [hg]
  rw [percolation_disjoint_block_integral p S T hd
    (fun z => A.indicator F z.1 * H z.2)]
  simp_rw [integral_const_mul]
  rw [integral_mul_const]
  rw [integral_finite_bernoulli, integral_finite_bernoulli,
    ← percolation_cylinder_expectation d p S (A.indicator F),
    ← percolation_cylinder_expectation d p T H]

/-- The fixed-cluster spatial Markov identity, retaining ANY observable of the
whole revealed open-graph data. Source properties such as intrinsic diameter
are not silently treated as properties of vertex sets alone. -/
theorem clusterReveal_fresh_factorization {d : ℕ} (p : unitInterval)
    (U C : Finset (Vertex d)) (root : Vertex d) (hroot : root ∈ U)
    (T : Finset (Bond d)) (hd : Disjoint (clusterRevealBonds U C) T)
    (F : (clusterRevealBonds U C → Bool) → ℝ) (H : (T → Bool) → ℝ) :
    (∫ ω : Configuration d,
      ({η | finiteBoxCluster η U root = C} : Set (Configuration d)).indicator
        (fun η => F ((clusterRevealBonds U C).restrict η)) ω * H (T.restrict ω)
      ∂percolation d p) =
    (∫ ω : Configuration d,
      ({η | finiteBoxCluster η U root = C} : Set (Configuration d)).indicator
        (fun η => F ((clusterRevealBonds U C).restrict η)) ω ∂percolation d p) *
      (∫ ω : Configuration d, H (T.restrict ω) ∂percolation d p) :=
  revealCylinder_fresh_factorization p (clusterRevealBonds U C) T hd _ _
    (clusterReveal_event_cylinder U C root hroot) F H

/-- No abstract disjointness premise: the untouched cube block is proved to be
exactly the internal bonds of U minus C. -/
theorem clusterReveal_unrevealed_factorization {d : ℕ} (p : unitInterval)
    (U C : Finset (Vertex d)) (root : Vertex d) (hroot : root ∈ U)
    (F : (clusterRevealBonds U C → Bool) → ℝ)
    (H : (clusterUnrevealedBonds U C → Bool) → ℝ) :
    (∫ ω : Configuration d,
      ({η | finiteBoxCluster η U root = C} : Set (Configuration d)).indicator
        (fun η => F ((clusterRevealBonds U C).restrict η)) ω *
        H ((clusterUnrevealedBonds U C).restrict ω) ∂percolation d p) =
    (∫ ω : Configuration d,
      ({η | finiteBoxCluster η U root = C} : Set (Configuration d)).indicator
        (fun η => F ((clusterRevealBonds U C).restrict η)) ω ∂percolation d p) *
      (∫ ω : Configuration d, H ((clusterUnrevealedBonds U C).restrict ω) ∂percolation d p) :=
  clusterReveal_fresh_factorization p U C root hroot _ (clusterReveal_unrevealed_disjoint U C) F H

/-- Event-probability specialization, valid even if the cluster event has zero
probability. No conditional division or positivity premise is hidden. -/
theorem clusterReveal_event_fresh_integral {d : ℕ} (p : unitInterval)
    (U C : Finset (Vertex d)) (root : Vertex d) (hroot : root ∈ U)
    (H : (clusterUnrevealedBonds U C → Bool) → ℝ) :
    (∫ ω : Configuration d,
      ({η | finiteBoxCluster η U root = C} : Set (Configuration d)).indicator (fun _ => (1:ℝ)) ω *
        H ((clusterUnrevealedBonds U C).restrict ω) ∂percolation d p) =
    (percolation d p).real {ω | finiteBoxCluster ω U root = C} *
      (∫ ω : Configuration d, H ((clusterUnrevealedBonds U C).restrict ω) ∂percolation d p) := by
  have h := clusterReveal_unrevealed_factorization p U C root hroot (fun _ => (1:ℝ)) H
  have hOne : (∫ ω : Configuration d,
      ({η | finiteBoxCluster η U root = C} : Set (Configuration d)).indicator
        (fun _ => (1:ℝ)) ω ∂percolation d p) =
      (percolation d p).real {ω | finiteBoxCluster ω U root = C} := by
    exact integral_indicator_one (measurableSet_clusterReveal_event U C root hroot)
  rwa [hOne] at h

/-- Actual nonmonotone source cluster-property events factor against the untouched
cube block. Internal graph data are part of the event; no independent-copy or
covariance conclusion is supplied as a hypothesis. -/
theorem clusterGraphProperty_fresh_integral {d : ℕ} (p : unitInterval)
    (U C : Finset (Vertex d)) (hCU : C ⊆ U) (root : Vertex d) (hroot : root ∈ U)
    (P : SimpleGraph (Vertex d) → Finset (Vertex d) → Prop)
    (H : (clusterUnrevealedBonds U C → Bool) → ℝ) :
    (∫ ω : Configuration d, (clusterGraphPropertyEvent U C root P).indicator
        (fun _ => (1:ℝ)) ω * H ((clusterUnrevealedBonds U C).restrict ω) ∂percolation d p) =
    (percolation d p).real (clusterGraphPropertyEvent U C root P) *
      (∫ ω : Configuration d, H ((clusterUnrevealedBonds U C).restrict ω) ∂percolation d p) := by
  have h := revealCylinder_fresh_factorization p (clusterRevealBonds U C)
    (clusterUnrevealedBonds U C) (clusterReveal_unrevealed_disjoint U C)
    (clusterGraphPropertyEvent U C root P) (clusterGraphPropertyLocalEvent U C root P)
    (clusterGraphProperty_event_cylinder U C hCU root hroot P) (fun _ => (1:ℝ)) H
  have hOne : (∫ ω : Configuration d, (clusterGraphPropertyEvent U C root P).indicator
      (fun _ => (1:ℝ)) ω ∂percolation d p) =
      (percolation d p).real (clusterGraphPropertyEvent U C root P) :=
    integral_indicator_one (measurableSet_clusterGraphProperty_event U C hCU root hroot P)
  rwa [hOne] at h

end NearCritical
