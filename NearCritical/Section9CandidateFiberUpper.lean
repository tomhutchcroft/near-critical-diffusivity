module
public import NearCritical.Section9OutsideClusterHitFactorization
public import NearCritical.Section9CandidateTargetBound
public import NearCritical.Section9FreshEvent

/-! Actual source candidate avoidance upper bound on the left-cluster fiber. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory
open scoped Classical

private theorem candidate_fiber_measurable_of_locality {d : ℕ}
    (U : Finset (Bond d)) (A : Set (Configuration d))
    (hlocal : ∀ ω θ : Configuration d, (∀ b ∈ U, ω b = θ b) → (ω ∈ A ↔ θ ∈ A)) :
    MeasurableSet A := by
  let A₀ : Set ((b : U) → Bool) := {ξ | extendConfiguration U (fun _ => false) ξ ∈ A}
  have heq : A = U.restrict ⁻¹' A₀ := by
    ext ω
    apply hlocal ω (extendConfiguration U (fun _ => false) (U.restrict ω))
    intro b hb
    simp [extendConfiguration,hb]
  rw [heq]
  exact (Set.toFinite A₀).measurableSet.preimage (Finset.measurable_restrict U)

/-- Actual suffix avoidance on a source last-exit candidate, jointly with
the actual left-cluster fiber, has the candidate target upper scale under
the positive outer-heart law. Dropping nonhit leaves a positive outside-C
hit, whose factorization is proved from the actual finite fiber mask. -/
theorem section9_source_candidate_fiber_avoidance_upper {d : ℕ} (hd : 2 ≤ d) {G : ℝ}
    (hG : 0 ≤ G) (green : CriticalSupGreenUpper d G)
    (i : Fin d) (n : ℕ) (hn : 16 ≤ n)
    (H₁ H₃ F₁ F₃ C B V : Finset (Vertex d)) (root : Vertex d)
    (hH₁ : H₁ ⊆ section9FiniteEndCube i n 0)
    (hH₃ : H₃ ⊆ section9FiniteEndCube i n (2*(n : ℝ)))
    (hpos : percolation d (criticalPoint d) (section9RevealEvent
      (section9FiniteEndCube i n 0) H₁ (section9FiniteEndCube i n (2*(n : ℝ))) H₃ F₁ F₃) ≠ 0)
    (hr : root ∈ section9FiniteTube i n (-(5 : ℝ)/8) (3/8))
    (hCL : C ⊆ section9FiniteTube i n (-(5 : ℝ)/8) (3/8))
    (hB : B ⊆ section8ExtensionNegativeFaceCore i n)
    (t : (Vertex d × Vertex d) × Bond d)
    (ht : t ∈ section9AvoidanceLastExitCandidates
      (section9FiniteTube i n (-(3 : ℝ)/8) (5/8)) C
      (section9FiniteEndCube i n (2*(n : ℝ))) F₃) :
    let L := section9FiniteTube i n (-(5 : ℝ)/8) (3/8)
    let R := section9FiniteTube i n (-(3 : ℝ)/8) (5/8)
    let Q₁ := section9FiniteEndCube i n 0
    let Q₃ := section9FiniteEndCube i n (2*(n : ℝ))
    let E : Set (Configuration d) := {ω | sprinklingUnexploredCluster ω L Q₁ F₁ root = C}
    let ν := section9RevealedLaw (criticalPoint d) Q₁ H₁ Q₃ H₃ F₁ F₃
    ν.real (E ∩ section9AvoidanceEvent (R \ C) R Q₃ F₃ B V t.1.2) ≤
      ν.real E * (G*(16 : ℝ)^((d : ℝ)-2)*(B.card : ℝ)*(n : ℝ)^((2 : ℝ)-(d : ℝ))) := by
  intro L R Q₁ Q₃ E ν
  let D := R \ C
  let H : Set (Configuration d) := {ω | (sprinklingUnexploredCluster ω D Q₃ F₃ t.1.2 ∩ B).Nonempty}
  let U := sprinklingAvailableBonds L Q₁ F₁ ∪ sprinklingAvailableBonds R Q₃ F₃
  have hn0 : 0 < n := by omega
  letI : IsProbabilityMeasure ν := section9RevealedLaw_isProbability (criticalPoint d)
    Q₁ H₁ Q₃ H₃ F₁ F₃ hpos
  have hfresh : Disjoint (clusterRevealBonds Q₁ F₁ ∪ clusterRevealBonds Q₃ F₃) U :=
    sprinklingAvailableBonds_disjoint_reveals L R Q₁ F₁ Q₃ F₃
      (section9FiniteLeftTube_disjoint_third i hn0) (section9FiniteRightTube_disjoint_first i hn0)
  have hDsub : sprinklingAvailableBonds D Q₃ F₃ ⊆ sprinklingAvailableBonds R Q₃ F₃ := by
    intro b hb
    obtain ⟨hbD,hbNot⟩ := Finset.mem_sdiff.mp hb
    obtain ⟨hbase,htip⟩ := (mem_internalBondSet D b).mp hbD
    exact Finset.mem_sdiff.mpr ⟨(mem_internalBondSet R b).mpr
      ⟨(Finset.mem_sdiff.mp hbase).1,(Finset.mem_sdiff.mp htip).1⟩,hbNot⟩
  have hElocal : ∀ ω θ : Configuration d, (∀ b ∈ U, ω b = θ b) → (ω ∈ E ↔ θ ∈ E) := by
    intro ω θ hagree
    have heq := sprinklingUnexploredCluster_eq_of_available_agree L Q₁ F₁ ω θ
      (fun b hb => hagree b (Finset.mem_union_left _ hb)) root
    simp only [E,Set.mem_setOf_eq,heq]
  have hHlocal : ∀ ω θ : Configuration d, (∀ b ∈ U, ω b = θ b) → (ω ∈ H ↔ θ ∈ H) := by
    intro ω θ hagree
    have heq := sprinklingUnexploredCluster_eq_of_available_agree D Q₃ F₃ ω θ
      (fun b hb => hagree b (Finset.mem_union_right _ (hDsub hb))) t.1.2
    simp only [H,Set.mem_setOf_eq,heq]
  have hEmeas : MeasurableSet E := candidate_fiber_measurable_of_locality U E hElocal
  have hHmeas : MeasurableSet H := measurableSet_sprinklingUnexploredCluster_hits D Q₃ F₃ B t.1.2
  have hEprob : ν.real E = (percolation d (criticalPoint d)).real E :=
    section9RevealedLaw_fresh_probability (criticalPoint d) Q₁ H₁ Q₃ H₃ F₁ F₃ hH₁ hH₃ hpos
      U hfresh E hEmeas hElocal
  have hJointProb : ν.real (E ∩ H) = (percolation d (criticalPoint d)).real (E ∩ H) := by
    apply section9RevealedLaw_fresh_probability (criticalPoint d) Q₁ H₁ Q₃ H₃ F₁ F₃
      hH₁ hH₃ hpos U hfresh (E ∩ H) (hEmeas.inter hHmeas)
    intro ω θ hagree
    exact and_congr (hElocal ω θ hagree) (hHlocal ω θ hagree)
  have hfactor : (percolation d (criticalPoint d)).real (E ∩ H) =
      (percolation d (criticalPoint d)).real E * (percolation d (criticalPoint d)).real H :=
    section9_outside_cluster_hit_factorization (criticalPoint d) L Q₁ F₁ C D Q₃ F₃ B root t.1.2
      Finset.sdiff_disjoint
  have hHupper : (percolation d (criticalPoint d)).real H ≤
      G*(16 : ℝ)^((d : ℝ)-2)*(B.card : ℝ)*(n : ℝ)^((2 : ℝ)-(d : ℝ)) :=
    section9_source_candidate_deleted_hit_probability_le hd hG green i n hn C F₃ B hCL hB t ht
  have hdrop : E ∩ section9AvoidanceEvent (R \ C) R Q₃ F₃ B V t.1.2 ⊆ E ∩ H := by
    rintro ω ⟨he,hhit,hnon⟩
    exact ⟨he,hhit⟩
  calc
    _ ≤ ν.real (E ∩ H) := measureReal_mono hdrop (measure_ne_top _ _)
    _ = (percolation d (criticalPoint d)).real (E ∩ H) := hJointProb
    _ = (percolation d (criticalPoint d)).real E * (percolation d (criticalPoint d)).real H := hfactor
    _ ≤ (percolation d (criticalPoint d)).real E *
        (G*(16 : ℝ)^((d : ℝ)-2)*(B.card : ℝ)*(n : ℝ)^((2 : ℝ)-(d : ℝ))) :=
      mul_le_mul_of_nonneg_left hHupper measureReal_nonneg
    _ = _ := by rw [← hEprob]

end NearCritical
