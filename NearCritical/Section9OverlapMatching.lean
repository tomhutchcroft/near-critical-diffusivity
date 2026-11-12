module
public import NearCritical.Section9ClusterPartition
public import NearCritical.Section9CovarianceIntegrated

/-! The nonempty component-intersection matrix of two original pivotal pairs
is a partial matching, hence has exactly six possible nonempty patterns. -/
@[expose] public section
noncomputable section
namespace NearCritical
open scoped Classical

/-- The six source overlap patterns, with row/column order left then right. -/
inductive Section9OverlapPattern where
  | singleLeft
  | parallel
  | leftRight
  | cross
  | rightLeft
  | singleRight
  deriving DecidableEq

instance instFintypeSection9OverlapPattern : Fintype Section9OverlapPattern where
  elems := {.singleLeft,.parallel,.leftRight,.cross,.rightLeft,.singleRight}
  complete := by intro k; cases k <;> simp

/-- Exact nonempty/disjoint conditions for an original overlap pattern. -/
def section9OverlapPatternHolds {d : ℕ} (k : Section9OverlapPattern)
    (ω : Configuration d) (L R Q₁ F₁ Q₃ F₃ : Finset (Vertex d))
    (e f : Vertex d × Vertex d) : Prop :=
  let EL := sprinklingUnexploredCluster ω L Q₁ F₁ e.1
  let ER := sprinklingUnexploredCluster ω R Q₃ F₃ e.2
  let FL := sprinklingUnexploredCluster ω L Q₁ F₁ f.1
  let FR := sprinklingUnexploredCluster ω R Q₃ F₃ f.2
  match k with
  | .singleLeft => (EL ∩ FL).Nonempty ∧ Disjoint EL FR ∧ Disjoint ER FL ∧ Disjoint ER FR
  | .parallel => (EL ∩ FL).Nonempty ∧ Disjoint EL FR ∧ Disjoint ER FL ∧ (ER ∩ FR).Nonempty
  | .leftRight => Disjoint EL FL ∧ (EL ∩ FR).Nonempty ∧ Disjoint ER FL ∧ Disjoint ER FR
  | .cross => Disjoint EL FL ∧ (EL ∩ FR).Nonempty ∧ (ER ∩ FL).Nonempty ∧ Disjoint ER FR
  | .rightLeft => Disjoint EL FL ∧ Disjoint EL FR ∧ (ER ∩ FL).Nonempty ∧ Disjoint ER FR
  | .singleRight => Disjoint EL FL ∧ Disjoint EL FR ∧ Disjoint ER FL ∧ (ER ∩ FR).Nonempty

/-- Pattern events retain both actual pivotal predicates. -/
def section9OverlapPatternEvent {d : ℕ} (k : Section9OverlapPattern)
    (L R Q₁ F₁ Q₃ F₃ A B : Finset (Vertex d)) (e f : Vertex d × Vertex d) :
    Set (Configuration d) :=
  {ω | sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ A B e ∧
    sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ A B f ∧
    section9OverlapPatternHolds k ω L R Q₁ F₁ Q₃ F₃ e f}

/-- A same-side meeting forces both cross entries to vanish. These are
exactly the four row/column exclusions for the two-by-two matrix. -/
theorem section9_pivotal_overlap_matching {d : ℕ} (ω : Configuration d)
    (L R Q₁ F₁ Q₃ F₃ A B : Finset (Vertex d)) (e f : Vertex d × Vertex d)
    (he : sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ A B e)
    (hf : sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ A B f) :
    (((sprinklingUnexploredCluster ω L Q₁ F₁ e.1 ∩
          sprinklingUnexploredCluster ω L Q₁ F₁ f.1).Nonempty →
      Disjoint (sprinklingUnexploredCluster ω L Q₁ F₁ e.1)
        (sprinklingUnexploredCluster ω R Q₃ F₃ f.2) ∧
      Disjoint (sprinklingUnexploredCluster ω R Q₃ F₃ e.2)
        (sprinklingUnexploredCluster ω L Q₁ F₁ f.1)) ∧
     ((sprinklingUnexploredCluster ω R Q₃ F₃ e.2 ∩
          sprinklingUnexploredCluster ω R Q₃ F₃ f.2).Nonempty →
      Disjoint (sprinklingUnexploredCluster ω L Q₁ F₁ e.1)
        (sprinklingUnexploredCluster ω R Q₃ F₃ f.2) ∧
      Disjoint (sprinklingUnexploredCluster ω R Q₃ F₃ e.2)
        (sprinklingUnexploredCluster ω L Q₁ F₁ f.1))) := by
  constructor
  · intro hLL
    have hEq := sprinklingUnexploredCluster_eq_of_inter_nonempty ω L Q₁ F₁ e.1 f.1 hLL
    constructor
    · rw [hEq]
      exact hf.2.2.2.2.2
    · rw [← hEq]
      exact he.2.2.2.2.2.symm
  · intro hRR
    have hEq := sprinklingUnexploredCluster_eq_of_inter_nonempty ω R Q₃ F₃ e.2 f.2 hRR
    constructor
    · rw [← hEq]
      exact he.2.2.2.2.2
    · rw [hEq]
      exact hf.2.2.2.2.2.symm

/-- Every original overlap has one of the six exact nonempty matching
patterns. No geometric restriction on the intersection matrix is assumed. -/
theorem section9_covariance_overlap_pattern_cover {d : ℕ}
    (L R Q₁ F₁ Q₃ F₃ A B : Finset (Vertex d)) (e f : Vertex d × Vertex d) :
    section9CovarianceOverlapEvent L R Q₁ F₁ Q₃ F₃ A B e f ⊆
      ⋃ k : Section9OverlapPattern, section9OverlapPatternEvent k L R Q₁ F₁ Q₃ F₃ A B e f := by
  intro ω hω
  obtain ⟨he,hf,hOverlap⟩ := hω
  let EL := sprinklingUnexploredCluster ω L Q₁ F₁ e.1
  let ER := sprinklingUnexploredCluster ω R Q₃ F₃ e.2
  let FL := sprinklingUnexploredCluster ω L Q₁ F₁ f.1
  let FR := sprinklingUnexploredCluster ω R Q₃ F₃ f.2
  have hmatch := section9_pivotal_overlap_matching ω L R Q₁ F₁ Q₃ F₃ A B e f he hf
  have hnonempty {S T : Finset (Vertex d)} (h : ¬ Disjoint S T) : (S ∩ T).Nonempty :=
    Finset.not_disjoint_iff_nonempty_inter.mp h
  by_cases hLL : Disjoint EL FL
  · by_cases hRR : Disjoint ER FR
    · by_cases hLR : Disjoint EL FR
      · by_cases hRL : Disjoint ER FL
        · exact (hOverlap ⟨Finset.disjoint_union_right.mpr ⟨hLL.symm,hRL.symm⟩,
            Finset.disjoint_union_right.mpr ⟨hLR.symm,hRR.symm⟩⟩).elim
        · exact Set.mem_iUnion.mpr ⟨.rightLeft,he,hf,hLL,hLR,hnonempty hRL,hRR⟩
      · by_cases hRL : Disjoint ER FL
        · exact Set.mem_iUnion.mpr ⟨.leftRight,he,hf,hLL,hnonempty hLR,hRL,hRR⟩
        · exact Set.mem_iUnion.mpr ⟨.cross,he,hf,hLL,hnonempty hLR,hnonempty hRL,hRR⟩
    · obtain ⟨hLR,hRL⟩ := hmatch.2 (hnonempty hRR)
      exact Set.mem_iUnion.mpr ⟨.singleRight,he,hf,hLL,hLR,hRL,hnonempty hRR⟩
  · obtain ⟨hLR,hRL⟩ := hmatch.1 (hnonempty hLL)
    by_cases hRR : Disjoint ER FR
    · exact Set.mem_iUnion.mpr ⟨.singleLeft,he,hf,hnonempty hLL,hLR,hRL,hRR⟩
    · exact Set.mem_iUnion.mpr ⟨.parallel,he,hf,hnonempty hLL,hLR,hRL,hnonempty hRR⟩

/-- Exact pattern conditions are measurable for the actual deleted-tube
components. Nonempty intersections are complements of disjointness. -/
theorem measurableSet_section9OverlapPatternEvent {d : ℕ} (k : Section9OverlapPattern)
    (L R Q₁ F₁ Q₃ F₃ A B : Finset (Vertex d)) (e f : Vertex d × Vertex d) :
    MeasurableSet (section9OverlapPatternEvent k L R Q₁ F₁ Q₃ F₃ A B e f) := by
  have hLL := measurableSet_sprinklingUnexploredClusters_disjoint L L Q₁ F₁ Q₁ F₁ e.1 f.1
  have hLR := measurableSet_sprinklingUnexploredClusters_disjoint L R Q₁ F₁ Q₃ F₃ e.1 f.2
  have hRL := measurableSet_sprinklingUnexploredClusters_disjoint R L Q₃ F₃ Q₁ F₁ e.2 f.1
  have hRR := measurableSet_sprinklingUnexploredClusters_disjoint R R Q₃ F₃ Q₃ F₃ e.2 f.2
  have hhit (T U Q F Q' F' : Finset (Vertex d)) (a b : Vertex d) :
      MeasurableSet {ω : Configuration d |
        (sprinklingUnexploredCluster ω T Q F a ∩ sprinklingUnexploredCluster ω U Q' F' b).Nonempty} := by
    have hEq : {ω : Configuration d |
        (sprinklingUnexploredCluster ω T Q F a ∩ sprinklingUnexploredCluster ω U Q' F' b).Nonempty} =
        {ω | Disjoint (sprinklingUnexploredCluster ω T Q F a)
          (sprinklingUnexploredCluster ω U Q' F' b)}ᶜ := by
      ext ω
      exact Finset.not_disjoint_iff_nonempty_inter.symm
    rw [hEq]
    exact (measurableSet_sprinklingUnexploredClusters_disjoint T U Q F Q' F' a b).compl
  have hHL := hhit L L Q₁ F₁ Q₁ F₁ e.1 f.1
  have hHR := hhit R R Q₃ F₃ Q₃ F₃ e.2 f.2
  have hHX := hhit L R Q₁ F₁ Q₃ F₃ e.1 f.2
  have hHY := hhit R L Q₃ F₃ Q₁ F₁ e.2 f.1
  have hp := (measurableSet_sprinklingPivotalPair L R Q₁ F₁ Q₃ F₃ A B e).inter
    (measurableSet_sprinklingPivotalPair L R Q₁ F₁ Q₃ F₃ A B f)
  cases k
  · simpa only [section9OverlapPatternEvent,section9OverlapPatternHolds,Set.inter_def,
      Set.mem_setOf_eq,and_assoc] using hp.inter (hHL.inter (hLR.inter (hRL.inter hRR)))
  · simpa only [section9OverlapPatternEvent,section9OverlapPatternHolds,Set.inter_def,
      Set.mem_setOf_eq,and_assoc] using hp.inter (hHL.inter (hLR.inter (hRL.inter hHR)))
  · simpa only [section9OverlapPatternEvent,section9OverlapPatternHolds,Set.inter_def,
      Set.mem_setOf_eq,and_assoc] using hp.inter (hLL.inter (hHX.inter (hRL.inter hRR)))
  · simpa only [section9OverlapPatternEvent,section9OverlapPatternHolds,Set.inter_def,
      Set.mem_setOf_eq,and_assoc] using hp.inter (hLL.inter (hHX.inter (hHY.inter hRR)))
  · simpa only [section9OverlapPatternEvent,section9OverlapPatternHolds,Set.inter_def,
      Set.mem_setOf_eq,and_assoc] using hp.inter (hLL.inter (hLR.inter (hHY.inter hRR)))
  · simpa only [section9OverlapPatternEvent,section9OverlapPatternHolds,Set.inter_def,
      Set.mem_setOf_eq,and_assoc] using hp.inter (hLL.inter (hLR.inter (hRL.inter hHR)))

end NearCritical
