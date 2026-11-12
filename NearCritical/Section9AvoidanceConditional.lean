module
public import NearCritical.Section9AvoidanceFiberInvariance
public import NearCritical.Section9ClosedFiberLaw
public import NearCritical.Section9AvoidanceProbability

/-! The actual fresh-copy versus cluster-conditioned avoidance comparison. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory
open scoped Classical BigOperators

/-- The fresh suffix-avoidance probability is no greater than its probability
on an actual left-cluster fiber, in undivided form (zero fibers included).
The external-entry guard is retained explicitly. -/
theorem section9_avoidance_fresh_to_left_fiber {d : ℕ} (p : unitInterval)
    (L R D Q₁ F₁ Q₃ F₃ C B V : Finset (Vertex d))
    (root : Vertex d) (hr : root ∈ L) (hRQ₁ : Disjoint R Q₁)
    (hDR : D ⊆ R) {v : Vertex d} (hv : v ∈ D \ C)
    (hExterior : ∀ b ∈ sprinklingAvailableBonds R Q₃ F₃,
      (b.1 ∈ C → bondTip b ∉ L → b.1 ∈ V) ∧
      (bondTip b ∈ C → b.1 ∉ L → bondTip b ∈ V)) :
    let E : Set (Configuration d) := {ω | sprinklingUnexploredCluster ω L Q₁ F₁ root = C}
    let A := section9AvoidanceEvent (D \ C) R Q₃ F₃ B V v
    (percolation d p).real E * (percolation d p).real A ≤
      (percolation d p).real (E ∩ A) := by
  intro E A
  let S := sprinklingClusterFiberMask L Q₁ F₁ C
  let close := fun ω : Configuration d => resampleBonds S ω (fun _ => false)
  let K : Set (Configuration d) := close ⁻¹' A
  let G := sprinklingAvailableBonds (D \ C) Q₃ F₃ ∪ sprinklingAvailableBonds R Q₃ F₃
  let f : (G → Bool) → ℝ := fun ξ =>
    if extendConfiguration G (fun _ => false) ξ ∈ A then 1 else 0
  have hA : MeasurableSet A :=
    (measurableSet_sprinklingUnexploredCluster_hits (D \ C) Q₃ F₃ B v).inter
      (measurableSet_sprinklingUnexploredCluster_hits R Q₃ F₃ V v).compl
  have hE : MeasurableSet E := by
    have hm := section9_two_cluster_fiber_cylinder L ∅ Q₁ F₁ ∅ ∅ C ∅ (root,root)
    have hempty (ω : Configuration d) : sprinklingUnexploredCluster ω ∅ ∅ ∅ root = ∅ := by
      simp [sprinklingUnexploredCluster]
    have heq : E = section9TwoClusterFiberEvent L ∅ Q₁ F₁ ∅ ∅ C ∅ (root,root) := by
      ext ω
      simp [E,section9TwoClusterFiberEvent,hempty]
    rw [heq,hm]
    exact (Set.toFinite _).measurableSet.preimage (Finset.measurable_restrict _)
  have hclose : Measurable close := by
    apply measurable_pi_iff.mpr
    intro b
    by_cases hb : b ∈ S
    · simp only [close,resampleBonds,extendConfiguration,dif_pos hb]
      exact measurable_const
    · simpa only [close,resampleBonds,extendConfiguration,dif_neg hb] using measurable_pi_apply b
  have hK : MeasurableSet K := hA.preimage hclose
  have hrepr (ω : Configuration d) : f (G.restrict ω) = A.indicator (fun _ => (1 : ℝ)) ω := by
    let θ := extendConfiguration G (fun _ => false) (G.restrict ω)
    have hbits : ∀ b ∈ G, θ b = ω b := by
      intro b hb
      simp [θ,extendConfiguration,hb]
    have h₁ := sprinklingUnexploredCluster_eq_of_available_agree (D \ C) Q₃ F₃ θ ω
      (fun b hb => hbits b (Finset.mem_union_left _ hb)) v
    have h₂ := sprinklingUnexploredCluster_eq_of_available_agree R Q₃ F₃ θ ω
      (fun b hb => hbits b (Finset.mem_union_right _ hb)) v
    have hm : θ ∈ A ↔ ω ∈ A := by
      simp only [A,section9AvoidanceEvent,Set.mem_setOf_eq,h₁,h₂]
    change (if θ ∈ A then (1 : ℝ) else 0) = A.indicator (fun _ => (1 : ℝ)) ω
    simp only [Set.indicator_apply,hm]
  have hf := section9_closed_single_cluster_observable_factorization p L Q₁ F₁ C root G f
  change (∫ ω, E.indicator (fun _ => (1 : ℝ)) ω * f (G.restrict (close ω)) ∂percolation d p) =
    (percolation d p).real E * (∫ ω, f (G.restrict (close ω)) ∂percolation d p) at hf
  simp_rw [hrepr] at hf
  have hprod (ω : Configuration d) :
      E.indicator (fun _ => (1 : ℝ)) ω * A.indicator (fun _ => (1 : ℝ)) (close ω) =
        (E ∩ A).indicator (fun _ => (1 : ℝ)) ω := by
    by_cases he : ω ∈ E
    · have hm := section9_avoidance_iff_resample_left_fiber_mask_false ω
        L R D Q₁ F₁ Q₃ F₃ C B V root hr he hRQ₁ hDR hv hExterior
      change (ω ∈ A ↔ close ω ∈ A) at hm
      by_cases ha : ω ∈ A
      · simp [he,ha,hm.mp ha]
      · have hn : close ω ∉ A := fun h => ha (hm.mpr h)
        simp [he,ha,hn]
    · simp [he]
  have hkind (ω : Configuration d) :
      A.indicator (fun _ => (1 : ℝ)) (close ω) = K.indicator (fun _ => (1 : ℝ)) ω := rfl
  simp_rw [hprod,hkind] at hf
  have hiE : (∫ ω, (E ∩ A).indicator (fun _ => (1 : ℝ)) ω ∂percolation d p) =
      (percolation d p).real (E ∩ A) := by
    simpa only [Set.indicator_apply,Pi.one_apply] using integral_indicator_one (μ := percolation d p) (hE.inter hA)
  have hiK : (∫ ω, K.indicator (fun _ => (1 : ℝ)) ω ∂percolation d p) =
      (percolation d p).real K := by
    simpa only [Set.indicator_apply,Pi.one_apply] using integral_indicator_one (μ := percolation d p) hK
  rw [hiE,hiK] at hf
  have hsub : A ⊆ K := fun ω hω =>
    section9_avoidance_implies_resample_left_fiber_mask_false ω L R D Q₁ F₁ Q₃ F₃ C B V v hω
  exact (mul_le_mul_of_nonneg_left (measureReal_mono hsub (measure_ne_top _ _))
    measureReal_nonneg).trans_eq hf.symm

/-- Fresh-copy last exit followed by the actual original-fiber comparison.
The right-hand terms are genuine joint probabilities with the revealed left
cluster; no conditional probability comparison is inserted as an assumption. -/
theorem section9_avoidance_fresh_to_left_fiber_candidate_bound {d : ℕ}
    (reimer : FiniteBernoulliBKRInput) (p : unitInterval)
    (L R Q₁ F₁ Q₃ F₃ C B V : Finset (Vertex d))
    (root : Vertex d) (hr : root ∈ L) (hRQ₁ : Disjoint R Q₁)
    {z : Vertex d} (hzR : z ∈ R) (hzC : z ∈ C) (hBC : Disjoint B C)
    (hExterior : ∀ b ∈ sprinklingAvailableBonds R Q₃ F₃,
      (b.1 ∈ C → bondTip b ∉ L → b.1 ∈ V) ∧
      (bondTip b ∈ C → b.1 ∉ L → bondTip b ∈ V)) :
    let E : Set (Configuration d) := {ω | sprinklingUnexploredCluster ω L Q₁ F₁ root = C}
    (percolation d p).real E *
      (percolation d p).real (section9AvoidanceEvent R R Q₃ F₃ B V z) ≤
      ∑ t ∈ section9AvoidanceLastExitCandidates R C Q₃ F₃,
        (p : ℝ)*(percolation d p).real
          {ω | t.1.1 ∈ sprinklingUnexploredCluster ω R Q₃ F₃ z} *
        (percolation d p).real (E ∩ section9AvoidanceEvent (R \ C) R Q₃ F₃ B V t.1.2) := by
  intro E
  have hf := section9_avoidance_probability_le_candidate_products reimer p
    R R C Q₃ F₃ B V hzR hzC (Finset.Subset.refl R) hBC
  calc
    _ ≤ (percolation d p).real E *
        (∑ t ∈ section9AvoidanceLastExitCandidates R C Q₃ F₃,
          (p : ℝ)*(percolation d p).real
            {ω | t.1.1 ∈ sprinklingUnexploredCluster ω R Q₃ F₃ z} *
          (percolation d p).real (section9AvoidanceEvent (R \ C) R Q₃ F₃ B V t.1.2)) :=
      mul_le_mul_of_nonneg_left hf measureReal_nonneg
    _ = ∑ t ∈ section9AvoidanceLastExitCandidates R C Q₃ F₃,
        ((p : ℝ)*(percolation d p).real
          {ω | t.1.1 ∈ sprinklingUnexploredCluster ω R Q₃ F₃ z}) *
        ((percolation d p).real E *
          (percolation d p).real (section9AvoidanceEvent (R \ C) R Q₃ F₃ B V t.1.2)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t _
      ring
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro t ht
      have hm := Finset.mem_filter.mp ht
      have hvR : t.1.2 ∈ R := (Finset.mem_product.mp (Finset.mem_product.mp hm.1).1).2
      have hv : t.1.2 ∈ R \ C := Finset.mem_sdiff.mpr ⟨hvR,hm.2.2.1⟩
      exact mul_le_mul_of_nonneg_left
        (section9_avoidance_fresh_to_left_fiber p L R R Q₁ F₁ Q₃ F₃ C B V
          root hr hRQ₁ (Finset.Subset.refl R) hv hExterior)
        (mul_nonneg p.property.1 measureReal_nonneg)

end NearCritical
