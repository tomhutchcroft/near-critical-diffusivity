module
public import NearCritical.Section9GoodCandidateGeometry
public import NearCritical.Section9ExitFace
public import NearCritical.Section9ClusterPartition

/-! Actual unique-left cluster and suffix avoidance yield canonical pivots. -/
@[expose] public section
noncomputable section
namespace NearCritical
open scoped Classical

/-- On the actual left-cluster fiber with unique W1 intersection, a good
last exit and actual suffix avoidance give a canonical source pivotal pair.
The right full component is disjoint from C because any hit would first
reach the forbidden exit face. No pivotal/counting/probability premise is used. -/
theorem section9_unique_left_good_exit_pivotal_bridge {d : ℕ} (ω : Configuration d)
    (i : Fin d) (n : ℕ) (hn : 0 < n) (F₁ F₃ C W₁ B : Finset (Vertex d)) (x : Vertex d)
    (hxL : x ∈ section9FiniteTube i n (-(5 : ℝ)/8) (3/8))
    (hC : sprinklingUnexploredCluster ω (section9FiniteTube i n (-(5 : ℝ)/8) (3/8))
      (section9FiniteEndCube i n 0) F₁ x = C)
    (hUnique : C ∩ W₁ = {x})
    (t : (Vertex d × Vertex d) × Bond d)
    (htGood : t ∈ section9AvoidanceGoodLastExitCandidates
      (section9FiniteTube i n (-(3 : ℝ)/8) (5/8)) C
      (section9FiniteEndCube i n (2*(n : ℝ))) F₃ (section9ExitFace i n ∩ C))
    (hSuffix : ω ∈ section9AvoidanceEvent
      ((section9FiniteTube i n (-(3 : ℝ)/8) (5/8)) \ C)
      (section9FiniteTube i n (-(3 : ℝ)/8) (5/8))
      (section9FiniteEndCube i n (2*(n : ℝ))) F₃ B (section9ExitFace i n ∩ C) t.1.2) :
    let L := section9FiniteTube i n (-(5 : ℝ)/8) (3/8)
    let R := section9FiniteTube i n (-(3 : ℝ)/8) (5/8)
    let Q₁ := section9FiniteEndCube i n 0
    let Q₃ := section9FiniteEndCube i n (2*(n : ℝ))
    t.1 ∈ sprinklingPivotalPairs ω (orientedLatticePairs (section9FiniteMiddle i n))
      L R Q₁ F₁ Q₃ F₃ {x} B ∧
      sprinklingUnexploredCluster ω L Q₁ F₁ t.1.1 ∩ W₁ = {x} := by
  intro L R Q₁ Q₃
  have hCL : C ⊆ L := by
    rw [← hC]
    exact sprinklingUnexploredCluster_subset ω L Q₁ F₁ x
  have hCanonical := section9_good_last_exit_candidate_mem_oriented_middle i n C F₃ hCL t htGood
  obtain ⟨htJ,_⟩ := Finset.mem_filter.mp htGood
  have hm := Finset.mem_filter.mp htJ
  have hR := Finset.mem_product.mp (Finset.mem_product.mp hm.1).1
  have huC := hm.2.1
  have hvNotC := hm.2.2.1
  have huActual : t.1.1 ∈ sprinklingUnexploredCluster ω L Q₁ F₁ x := by
    rw [hC]
    exact huC
  have hxu := ((mem_sprinklingUnexploredCluster ω L Q₁ F₁ x t.1.1).mp huActual).2
  have hLeft : sprinklingUnexploredCluster ω L Q₁ F₁ t.1.1 = C :=
    (sprinklingUnexploredCluster_eq_of_reachable ω L Q₁ F₁ hxu).symm.trans hC
  have hxC : x ∈ C := by
    rw [← hC]
    exact root_mem_sprinklingUnexploredCluster ω L Q₁ F₁ hxL
  have hLeftHit : (sprinklingUnexploredCluster ω L Q₁ F₁ t.1.1 ∩ {x}).Nonempty := by
    rw [hLeft]
    exact ⟨x,Finset.mem_inter.mpr ⟨hxC,Finset.mem_singleton_self x⟩⟩
  obtain ⟨hSuffixHit,hNonhit⟩ := hSuffix
  have hRightHit : (sprinklingUnexploredCluster ω R Q₃ F₃ t.1.2 ∩ B).Nonempty := by
    obtain ⟨y,hy⟩ := hSuffixHit
    obtain ⟨hyCluster,hyB⟩ := Finset.mem_inter.mp hy
    obtain ⟨hyDC,hreach⟩ := (mem_sprinklingUnexploredCluster ω (R \ C) Q₃ F₃ t.1.2 y).mp hyCluster
    have hle : sprinklingUnexploredGraph ω (R \ C) Q₃ F₃ ≤ sprinklingUnexploredGraph ω R Q₃ F₃ :=
      fun _ _ h => ⟨h.1,(Finset.mem_sdiff.mp h.2.1).1,(Finset.mem_sdiff.mp h.2.2.1).1,h.2.2.2⟩
    exact ⟨y,Finset.mem_inter.mpr
      ⟨(mem_sprinklingUnexploredCluster ω R Q₃ F₃ t.1.2 y).mpr
        ⟨(Finset.mem_sdiff.mp hyDC).1,hreach.mono hle⟩,hyB⟩⟩
  have hRightDisjoint : Disjoint C (sprinklingUnexploredCluster ω R Q₃ F₃ t.1.2) := by
    apply Finset.disjoint_left.mpr
    intro y hyC hyRight
    have hyActual : y ∈ sprinklingUnexploredCluster ω L Q₁ F₁ x := by
      rw [hC]
      exact hyC
    have hvOutside : t.1.2 ∉ sprinklingUnexploredCluster ω L Q₁ F₁ x := by
      rw [hC]
      exact hvNotC
    have hreach := ((mem_sprinklingUnexploredCluster ω R Q₃ F₃ t.1.2 y).mp hyRight).2
    obtain ⟨v,hvExit,hvReach⟩ := section9_rightPath_hits_cluster_exit i hn F₁ F₃ x
      hvOutside hyActual hreach
    have hvR : v ∈ R := by
      obtain ⟨w⟩ := hvReach
      exact microscopicWalk_support w hR.2 v w.end_mem_support
    have hvV : v ∈ section9ExitFace i n ∩ C := by
      simpa only [hC] using hvExit
    apply hNonhit
    exact ⟨v,Finset.mem_inter.mpr
      ⟨(mem_sprinklingUnexploredCluster ω R Q₃ F₃ t.1.2 v).mpr ⟨hvR,hvReach⟩,hvV⟩⟩
  have hadj : (openGraph (fun _ : Bond d => true)).Adj t.1.1 t.1.2 :=
    ((mem_orientedLatticePairs (section9FiniteMiddle i n) t.1.1 t.1.2).mp hCanonical).2.2
  have hpiv : sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ {x} B t.1 := by
    refine ⟨hadj,hCL huC,hR.2,hLeftHit,hRightHit,?_⟩
    rw [hLeft]
    exact hRightDisjoint
  refine ⟨Finset.mem_filter.mpr ⟨hCanonical,hpiv⟩,?_⟩
  rw [hLeft,hUnique]

end NearCritical
