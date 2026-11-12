module
public import NearCritical.Section9AvoidanceSourceComparison
public import NearCritical.Section9FreshEvent

/-! Actual source avoidance comparison under the outer heart-reveal law. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory
open scoped Classical BigOperators

private theorem avoidance_available_sdiff_subset {d : ℕ}
    (R C Q F : Finset (Vertex d)) :
    sprinklingAvailableBonds (R \ C) Q F ⊆ sprinklingAvailableBonds R Q F := by
  intro b hb
  obtain ⟨hbInternal,hbNot⟩ := Finset.mem_sdiff.mp hb
  obtain ⟨hbase,htip⟩ := (mem_internalBondSet (R \ C) b).mp hbInternal
  exact Finset.mem_sdiff.mpr ⟨(mem_internalBondSet R b).mpr
    ⟨(Finset.mem_sdiff.mp hbase).1,(Finset.mem_sdiff.mp htip).1⟩,hbNot⟩

private theorem avoidance_measurable_of_finite_locality {d : ℕ}
    (s : Finset (Bond d)) (A : Set (Configuration d))
    (hlocal : ∀ ω θ : Configuration d, (∀ b ∈ s, ω b = θ b) → (ω ∈ A ↔ θ ∈ A)) :
    MeasurableSet A := by
  let A₀ : Set ((b : s) → Bool) := {ξ | extendConfiguration s (fun _ => false) ξ ∈ A}
  have heq : A = s.restrict ⁻¹' A₀ := by
    ext ω
    apply hlocal ω (extendConfiguration s (fun _ => false) (s.restrict ω))
    intro b hb
    simp [extendConfiguration,hb]
  rw [heq]
  exact (Set.toFinite A₀).measurableSet.preimage (Finset.measurable_restrict s)

/-- The actual source fresh-copy upper bound under the outer heart law.
Only the left-cluster fiber and its joint suffix probabilities are conditioned;
the fresh-copy and prefix factors retain their ordinary percolation laws.
All freshness, source exit-face and disjointness conditions are discharged. -/
theorem section9_source_avoidance_heart_fiber_candidate_bound {d : ℕ}
    (reimer : FiniteBernoulliBKRInput) (p : unitInterval)
    (i : Fin d) (n : ℕ) (hn : 0 < n)
    (H₁ H₃ F₁ F₃ C B : Finset (Vertex d)) (root : Vertex d)
    (hH₁ : H₁ ⊆ section9FiniteEndCube i n 0)
    (hH₃ : H₃ ⊆ section9FiniteEndCube i n (2*(n : ℝ)))
    (hpos : percolation d p (section9RevealEvent
      (section9FiniteEndCube i n 0) H₁ (section9FiniteEndCube i n (2*(n : ℝ))) H₃ F₁ F₃) ≠ 0)
    (hr : root ∈ section9FiniteTube i n (-(5 : ℝ)/8) (3/8))
    (hCL : C ⊆ section9FiniteTube i n (-(5 : ℝ)/8) (3/8))
    (hB : B ⊆ section9FiniteEndCube i n (2*(n : ℝ))) {z : Vertex d}
    (hzR : z ∈ section9FiniteTube i n (-(3 : ℝ)/8) (5/8)) (hzC : z ∈ C) :
    let L := section9FiniteTube i n (-(5 : ℝ)/8) (3/8)
    let R := section9FiniteTube i n (-(3 : ℝ)/8) (5/8)
    let Q₁ := section9FiniteEndCube i n 0
    let Q₃ := section9FiniteEndCube i n (2*(n : ℝ))
    let V := section9ExitFace i n ∩ C
    let E : Set (Configuration d) := {ω | sprinklingUnexploredCluster ω L Q₁ F₁ root = C}
    let ν := section9RevealedLaw p Q₁ H₁ Q₃ H₃ F₁ F₃
    ν.real E * (percolation d p).real (section9AvoidanceEvent R R Q₃ F₃ B V z) ≤
      ∑ t ∈ section9AvoidanceLastExitCandidates R C Q₃ F₃,
        (p : ℝ)*(percolation d p).real
          {ω | t.1.1 ∈ sprinklingUnexploredCluster ω R Q₃ F₃ z} *
        ν.real (E ∩ section9AvoidanceEvent (R \ C) R Q₃ F₃ B V t.1.2) := by
  intro L R Q₁ Q₃ V E ν
  let U := sprinklingAvailableBonds L Q₁ F₁ ∪ sprinklingAvailableBonds R Q₃ F₃
  have hfresh : Disjoint (clusterRevealBonds Q₁ F₁ ∪ clusterRevealBonds Q₃ F₃) U :=
    sprinklingAvailableBonds_disjoint_reveals L R Q₁ F₁ Q₃ F₃
      (section9FiniteLeftTube_disjoint_third i hn) (section9FiniteRightTube_disjoint_first i hn)
  have hE : ∀ ω θ : Configuration d, (∀ b ∈ U, ω b = θ b) → (ω ∈ E ↔ θ ∈ E) := by
    intro ω θ hagree
    have heq := sprinklingUnexploredCluster_eq_of_available_agree L Q₁ F₁ ω θ
      (fun b hb => hagree b (Finset.mem_union_left _ hb)) root
    simp only [E,Set.mem_setOf_eq,heq]
  have hJoint (v : Vertex d) : ∀ ω θ : Configuration d,
      (∀ b ∈ U, ω b = θ b) →
      (ω ∈ E ∩ section9AvoidanceEvent (R \ C) R Q₃ F₃ B V v ↔
       θ ∈ E ∩ section9AvoidanceEvent (R \ C) R Q₃ F₃ B V v) := by
    intro ω θ hagree
    have heqL := sprinklingUnexploredCluster_eq_of_available_agree L Q₁ F₁ ω θ
      (fun b hb => hagree b (Finset.mem_union_left _ hb)) root
    have heqR := sprinklingUnexploredCluster_eq_of_available_agree R Q₃ F₃ ω θ
      (fun b hb => hagree b (Finset.mem_union_right _ hb)) v
    have heqDC := sprinklingUnexploredCluster_eq_of_available_agree (R \ C) Q₃ F₃ ω θ
      (fun b hb => hagree b (Finset.mem_union_right _
        (avoidance_available_sdiff_subset R C Q₃ F₃ hb))) v
    simp only [Set.mem_inter_iff,E,section9AvoidanceEvent,Set.mem_setOf_eq,heqL,heqR,heqDC]
  have hEprob : ν.real E = (percolation d p).real E :=
    section9RevealedLaw_fresh_probability p Q₁ H₁ Q₃ H₃ F₁ F₃ hH₁ hH₃ hpos
      U hfresh E (avoidance_measurable_of_finite_locality U E hE) hE
  have hJointProb (v : Vertex d) :
      ν.real (E ∩ section9AvoidanceEvent (R \ C) R Q₃ F₃ B V v) =
      (percolation d p).real (E ∩ section9AvoidanceEvent (R \ C) R Q₃ F₃ B V v) :=
    section9RevealedLaw_fresh_probability p Q₁ H₁ Q₃ H₃ F₁ F₃ hH₁ hH₃ hpos
      U hfresh _ (avoidance_measurable_of_finite_locality U _ (hJoint v)) (hJoint v)
  rw [hEprob]
  simp_rw [hJointProb]
  exact section9_source_avoidance_fresh_to_left_fiber_candidate_bound reimer p
    i n hn F₁ F₃ C B root hr hCL hB hzR hzC

end NearCritical
