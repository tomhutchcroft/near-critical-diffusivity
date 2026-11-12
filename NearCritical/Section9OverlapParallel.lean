module
public import NearCritical.Section9OverlapMatching
public import NearCritical.Section9CoalescenceConnection
public import NearCritical.Section9RestrictedTripodProbability
public import NearCritical.Section9ConditionedMarkedTree

/-! Source Case II: both original same-side components coincide. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory
open scoped Classical BigOperators

/-- The common left and common right components supply disjoint finite
certificates for both joint connections, with both target families retained. -/
theorem section9_parallel_overlap_occurrence {d : ℕ} (ω : Configuration d)
    (L R Q₁ F₁ Q₃ F₃ A B : Finset (Vertex d)) (e f : Vertex d × Vertex d)
    (h : ω ∈ section9OverlapPatternEvent .parallel L R Q₁ F₁ Q₃ F₃ A B e f) :
    DisjointOccurrence
      (connectionToSetEvent (L : Set (Vertex d)) e.1 {f.1} ∩
       connectionToSetEvent (L : Set (Vertex d)) e.1 (A : Set (Vertex d)))
      (connectionToSetEvent (R : Set (Vertex d)) e.2 {f.2} ∩
       connectionToSetEvent (R : Set (Vertex d)) e.2 (B : Set (Vertex d))) ω := by
  obtain ⟨he,hf,hLL,_hLR,_hRL,hRR⟩ := h
  have hEqL := sprinklingUnexploredCluster_eq_of_inter_nonempty ω L Q₁ F₁ e.1 f.1 hLL
  have hEqR := sprinklingUnexploredCluster_eq_of_inter_nonempty ω R Q₃ F₃ e.2 f.2 hRR
  have hrootL := root_mem_sprinklingUnexploredCluster ω L Q₁ F₁ hf.2.1
  have hrootR := root_mem_sprinklingUnexploredCluster ω R Q₃ F₃ hf.2.2.1
  rw [← hEqL] at hrootL
  rw [← hEqR] at hrootR
  have hefL := ((mem_sprinklingUnexploredCluster ω L Q₁ F₁ e.1 f.1).mp hrootL).2
  have hefR := ((mem_sprinklingUnexploredCluster ω R Q₃ F₃ e.2 f.2).mp hrootR).2
  obtain ⟨x,hx⟩ := he.2.2.2.1
  obtain ⟨hxC,hxA⟩ := Finset.mem_inter.mp hx
  obtain ⟨y,hy⟩ := he.2.2.2.2.1
  obtain ⟨hyC,hyB⟩ := Finset.mem_inter.mp hy
  obtain ⟨S,hSo,hSb,hSf⟩ := sprinklingComponent_connection_certificate ω L Q₁ F₁ he.2.1 hefL
  obtain ⟨U,hUo,hUb,hUf⟩ := sprinklingComponent_connection_certificate ω L Q₁ F₁ he.2.1
    ((mem_sprinklingUnexploredCluster ω L Q₁ F₁ e.1 x).mp hxC).2
  obtain ⟨V,hVo,hVb,hVf⟩ := sprinklingComponent_connection_certificate ω R Q₃ F₃ he.2.2.1 hefR
  obtain ⟨W,hWo,hWb,hWf⟩ := sprinklingComponent_connection_certificate ω R Q₃ F₃ he.2.2.1
    ((mem_sprinklingUnexploredCluster ω R Q₃ F₃ e.2 y).mp hyC).2
  have hLeft : ∀ b ∈ S ∪ U, b.1 ∈ sprinklingUnexploredCluster ω L Q₁ F₁ e.1 := by
    intro b hb
    exact (Finset.mem_union.mp hb).elim (hSb b) (hUb b)
  have hRight : ∀ b ∈ V ∪ W, b.1 ∈ sprinklingUnexploredCluster ω R Q₃ F₃ e.2 := by
    intro b hb
    exact (Finset.mem_union.mp hb).elim (hVb b) (hWb b)
  have hdis := disjoint_bond_certificates_of_disjoint_bases he.2.2.2.2.2 hLeft hRight
  refine ⟨(↑(S ∪ U) : Set (Bond d)),(↑(V ∪ W) : Set (Bond d)),
    (S ∪ U).finite_toSet,(V ∪ W).finite_toSet,
    Set.disjoint_left.mpr (Finset.disjoint_left.mp hdis),?_,?_⟩
  · intro θ hθ
    refine ⟨hSf θ (fun b hb => (hθ b (Finset.mem_union_left U hb)).trans (hSo b hb)),?_⟩
    apply connectionToSetEvent_mono (Set.Subset.refl _) (Set.singleton_subset_iff.mpr hxA) e.1
    exact hUf θ (fun b hb => (hθ b (Finset.mem_union_right S hb)).trans (hUo b hb))
  · intro θ hθ
    refine ⟨hVf θ (fun b hb => (hθ b (Finset.mem_union_left W hb)).trans (hVo b hb)),?_⟩
    apply connectionToSetEvent_mono (Set.Subset.refl _) (Set.singleton_subset_iff.mpr hyB) e.2
    exact hWf θ (fun b hb => (hθ b (Finset.mem_union_right V hb)).trans (hWo b hb))

/-- Actual BK and two restricted tripod bounds give the finite product of
left and right tree sums for the parallel original-overlap event. -/
theorem section9_parallel_overlap_tree_bound {d : ℕ} (p : unitInterval)
    (L R Q₁ F₁ Q₃ F₃ A B : Finset (Vertex d)) (e f : Vertex d × Vertex d) :
    let PL := fun a b => (percolation d p).real
      (connectionToSetEvent (L : Set (Vertex d)) a {b})
    let PR := fun a b => (percolation d p).real
      (connectionToSetEvent (R : Set (Vertex d)) a {b})
    (percolation d p).real (section9OverlapPatternEvent .parallel L R Q₁ F₁ Q₃ F₃ A B e f) ≤
      (∑ x ∈ A, ∑ u ∈ L, PL e.1 u * (PL u f.1 * PL x u)) *
      (∑ y ∈ B, ∑ v ∈ R, PR e.2 v * (PR v f.2 * PR y v)) := by
  intro PL PR
  let J := connectionToSetEvent (L : Set (Vertex d)) e.1 {f.1} ∩
    connectionToSetEvent (L : Set (Vertex d)) e.1 (A : Set (Vertex d))
  let K := connectionToSetEvent (R : Set (Vertex d)) e.2 {f.2} ∩
    connectionToSetEvent (R : Set (Vertex d)) e.2 (B : Set (Vertex d))
  have hJ : BK.Increasing J := by
    intro ω η h hω
    exact ⟨connectionToSetEvent_increasing _ _ _ h hω.1,
      connectionToSetEvent_increasing _ _ _ h hω.2⟩
  have hK : BK.Increasing K := by
    intro ω η h hω
    exact ⟨connectionToSetEvent_increasing _ _ _ h hω.1,
      connectionToSetEvent_increasing _ _ _ h hω.2⟩
  refine (measureReal_mono (fun ω h => section9_parallel_overlap_occurrence ω L R Q₁ F₁ Q₃ F₃ A B e f h)
    (measure_ne_top _ _)).trans ?_
  exact (percolation_bk d p J K hJ hK).trans
    (mul_le_mul (restricted_joint_connection_probability_le p L A e.1 f.1)
      (restricted_joint_connection_probability_le p R B e.2 f.2) measureReal_nonneg
      (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
        mul_nonneg measureReal_nonneg (mul_nonneg measureReal_nonneg measureReal_nonneg)))

private theorem parallel_event_local {d : ℕ}
    (L R Q₁ F₁ Q₃ F₃ A B : Finset (Vertex d)) (e f : Vertex d × Vertex d)
    (ω η : Configuration d)
    (h : ∀ b ∈ sprinklingAvailableBonds L Q₁ F₁ ∪ sprinklingAvailableBonds R Q₃ F₃, ω b = η b) :
    (ω ∈ section9OverlapPatternEvent .parallel L R Q₁ F₁ Q₃ F₃ A B e f ↔
      η ∈ section9OverlapPatternEvent .parallel L R Q₁ F₁ Q₃ F₃ A B e f) := by
  have hL (v : Vertex d) := sprinklingUnexploredCluster_eq_of_available_agree L Q₁ F₁ ω η
    (fun b hb => h b (Finset.mem_union_left _ hb)) v
  have hR (v : Vertex d) := sprinklingUnexploredCluster_eq_of_available_agree R Q₃ F₃ ω η
    (fun b hb => h b (Finset.mem_union_right _ hb)) v
  have hp (a : Vertex d × Vertex d) := sprinklingPivotalPair_iff_of_available_agree
    L R Q₁ F₁ Q₃ F₃ A B ω η
    (fun b hb => h b (Finset.mem_union_left _ hb))
    (fun b hb => h b (Finset.mem_union_right _ hb)) a
  simp only [section9OverlapPatternEvent,section9OverlapPatternHolds,Set.mem_setOf_eq,hp,hL,hR]

/-- Positive heart conditioning preserves the actual parallel event on the
fresh available coordinates; no conditional tree estimate is assumed. -/
theorem section9_conditioned_parallel_overlap_tree_bound {d : ℕ} (p : unitInterval)
    (L R Q₁ H₁ F₁ Q₃ H₃ F₃ A B : Finset (Vertex d))
    (hH₁ : H₁ ⊆ Q₁) (hH₃ : H₃ ⊆ Q₃)
    (hpos : percolation d p (section9RevealEvent Q₁ H₁ Q₃ H₃ F₁ F₃) ≠ 0)
    (hLQ₃ : Disjoint L Q₃) (hRQ₁ : Disjoint R Q₁) (e f : Vertex d × Vertex d) :
    let PL := fun a b => (percolation d p).real
      (connectionToSetEvent (L : Set (Vertex d)) a {b})
    let PR := fun a b => (percolation d p).real
      (connectionToSetEvent (R : Set (Vertex d)) a {b})
    (section9RevealedLaw p Q₁ H₁ Q₃ H₃ F₁ F₃).real
      (section9OverlapPatternEvent .parallel L R Q₁ F₁ Q₃ F₃ A B e f) ≤
      (∑ x ∈ A, ∑ u ∈ L, PL e.1 u * (PL u f.1 * PL x u)) *
      (∑ y ∈ B, ∑ v ∈ R, PR e.2 v * (PR v f.2 * PR y v)) := by
  intro PL PR
  rw [section9RevealedLaw_fresh_probability p Q₁ H₁ Q₃ H₃ F₁ F₃ hH₁ hH₃ hpos
    (sprinklingAvailableBonds L Q₁ F₁ ∪ sprinklingAvailableBonds R Q₃ F₃)
    (sprinklingAvailableBonds_disjoint_reveals L R Q₁ F₁ Q₃ F₃ hLQ₃ hRQ₁)
    _ (measurableSet_section9OverlapPatternEvent .parallel L R Q₁ F₁ Q₃ F₃ A B e f)
    (parallel_event_local L R Q₁ F₁ Q₃ F₃ A B e f)]
  exact section9_parallel_overlap_tree_bound p L R Q₁ F₁ Q₃ F₃ A B e f

end NearCritical
