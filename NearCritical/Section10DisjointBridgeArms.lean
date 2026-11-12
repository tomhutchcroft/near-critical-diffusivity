module

public import NearCritical.Section10DisjointBridgePivots
public import NearCritical.Section8DiagramWalkCertificates
public import NearCritical.Section9PivotalMeanUpper

/-! The four critical arms forced by two offspring hits in disjoint bridges. -/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open MeasureTheory Set
open scoped Classical

/-- The critical part of a pair of disjoint offspring hits at fixed pivots. -/
def disjointPivotEvent {d : ℕ} (L R Q₁ F₁ Q₃ F₃ A₁ A₂ B₁ B₂ : Finset (Vertex d))
    (e f : Vertex d × Vertex d) : Set (Configuration d) :=
  {ω |
    let U (g : Vertex d × Vertex d) := sprinklingUnexploredCluster ω L Q₁ F₁ g.1
    let V (g : Vertex d × Vertex d) := sprinklingUnexploredCluster ω R Q₃ F₃ g.2
    sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ A₁ B₁ e ∧
      sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ A₂ B₂ f ∧
      Disjoint (U e) (U f) ∧ Disjoint (U e) (V f) ∧
      Disjoint (V e) (U f) ∧ Disjoint (V e) (V f)}

private theorem openWalk_in_unexploredCluster {d : ℕ} {ω : Configuration d}
    (T Q F : Finset (Vertex d)) {x y : Vertex d} (hx : x ∈ T)
    (hy : y ∈ sprinklingUnexploredCluster ω T Q F x) :
    ∃ w : (openGraph ω).Walk x y, ∀ z ∈ w.support, z ∈ sprinklingUnexploredCluster ω T Q F x := by
  obtain ⟨p⟩ := ((mem_sprinklingUnexploredCluster ω T Q F x y).mp hy).2
  let w : (openGraph ω).Walk x y := p.mapLe (microscopicPieceGraph_le ω _ _)
  have hsupport : w.support = p.support := SimpleGraph.Walk.support_mapLe_eq_support _ _
  refine ⟨w, ?_⟩
  intro z hz
  have hz' : z ∈ p.support := hsupport ▸ hz
  exact (mem_sprinklingUnexploredCluster ω T Q F x z).mpr
    ⟨microscopicWalk_support p hx z hz', (p.takeUntil z hz').reachable⟩

private theorem walk_edges_disjoint_of_components {d : ℕ} {ω : Configuration d}
    {a b c z : Vertex d} (p : (openGraph ω).Walk a b) (q : (openGraph ω).Walk c z)
    {U V : Finset (Vertex d)} (hp : ∀ v ∈ p.support, v ∈ U)
    (hq : ∀ v ∈ q.support, v ∈ V) (hd : Disjoint U V) :
    p.edges.Disjoint q.edges := by
  apply List.disjoint_left.mpr
  intro e hep heq
  obtain ⟨v, w⟩ := e
  exact Finset.disjoint_left.mp hd (hp v (p.fst_mem_support_of_mem_edges hep))
    (hq v (q.fst_mem_support_of_mem_edges heq))

/-- Four pairwise disjoint walks supply finite certificates for repeated BK. -/
theorem disjointPivotEvent_subset_diagramOccurrence {d : ℕ}
    (L R Q₁ F₁ Q₃ F₃ A₁ A₂ B₁ B₂ : Finset (Vertex d)) (e f : Vertex d × Vertex d) :
    disjointPivotEvent L R Q₁ F₁ Q₃ F₃ A₁ A₂ B₁ B₂ e f ⊆ Section8.diagramOccurrence4
      (connectionToSetEvent Set.univ e.1 (A₁ : Set (Vertex d)))
      (connectionToSetEvent Set.univ e.2 (B₁ : Set (Vertex d)))
      (connectionToSetEvent Set.univ f.1 (A₂ : Set (Vertex d)))
      (connectionToSetEvent Set.univ f.2 (B₂ : Set (Vertex d))) := by
  rintro ω ⟨⟨_, heL, heR, ⟨a, ha⟩, ⟨b, hb⟩, heD⟩,
    ⟨_, hfL, hfR, ⟨c, hc⟩, ⟨z, hz⟩, hfD⟩, hLL, hLR, hRL, hRR⟩
  obtain ⟨p, hp⟩ := openWalk_in_unexploredCluster L Q₁ F₁ heL (Finset.mem_inter.mp ha).1
  obtain ⟨q, hq⟩ := openWalk_in_unexploredCluster R Q₃ F₃ heR (Finset.mem_inter.mp hb).1
  obtain ⟨r, hr⟩ := openWalk_in_unexploredCluster L Q₁ F₁ hfL (Finset.mem_inter.mp hc).1
  obtain ⟨s, hs⟩ := openWalk_in_unexploredCluster R Q₃ F₃ hfR (Finset.mem_inter.mp hz).1
  exact Section8.fourOpenWalks_diagramOccurrence p q r s Set.univ A₁ B₁ A₂ B₂
    (fun _ _ => Set.mem_univ _) (fun _ _ => Set.mem_univ _)
    (fun _ _ => Set.mem_univ _) (fun _ _ => Set.mem_univ _)
    (Finset.mem_inter.mp ha).2 (Finset.mem_inter.mp hb).2
    (Finset.mem_inter.mp hc).2 (Finset.mem_inter.mp hz).2
    (walk_edges_disjoint_of_components p q hp hq heD)
    (walk_edges_disjoint_of_components p r hp hr hLL)
    (walk_edges_disjoint_of_components p s hp hs hLR)
    (walk_edges_disjoint_of_components q r hq hr hRL)
    (walk_edges_disjoint_of_components q s hq hs hRR)
    (walk_edges_disjoint_of_components r s hr hs hfD)

/-- The ordinary two-point envelope for the critical part of a disjoint hit. -/
theorem disjointPivotEvent_probability_le {d : ℕ} (p : unitInterval)
    (L R Q₁ F₁ Q₃ F₃ A₁ A₂ B₁ B₂ : Finset (Vertex d)) (e f : Vertex d × Vertex d) :
    (percolation d p).real (disjointPivotEvent L R Q₁ F₁ Q₃ F₃ A₁ A₂ B₁ B₂ e f) ≤
      ((∑ x ∈ A₁, twoPoint d p e.1 x) * (∑ y ∈ B₁, twoPoint d p e.2 y)) *
        ((∑ x ∈ A₂, twoPoint d p f.1 x) * (∑ y ∈ B₂, twoPoint d p f.2 y)) := by
  let A := connectionToSetEvent Set.univ e.1 (A₁ : Set (Vertex d))
  let B := connectionToSetEvent Set.univ e.2 (B₁ : Set (Vertex d))
  let C := connectionToSetEvent Set.univ f.1 (A₂ : Set (Vertex d))
  let D := connectionToSetEvent Set.univ f.2 (B₂ : Set (Vertex d))
  refine (measureReal_mono (disjointPivotEvent_subset_diagramOccurrence L R Q₁ F₁ Q₃ F₃
    A₁ A₂ B₁ B₂ e f) (measure_ne_top _ _)).trans ?_
  refine (Section8.diagramOccurrence4_probability_le p A B C D
    (connectionToSetEvent_increasing _ _ _) (connectionToSetEvent_increasing _ _ _)
    (connectionToSetEvent_increasing _ _ _) (connectionToSetEvent_increasing _ _ _)).trans ?_
  calc
    _ = ((percolation d p).real A * (percolation d p).real B) *
        ((percolation d p).real C * (percolation d p).real D) := by ring
    _ ≤ _ :=
      mul_le_mul
        (mul_le_mul (connectionToSet_probability_le_twoPoint_sum p _ e.1 A₁)
          (connectionToSet_probability_le_twoPoint_sum p _ e.2 B₁) measureReal_nonneg
          (Finset.sum_nonneg (fun _ _ => twoPoint_nonneg _ _ _)))
        (mul_le_mul (connectionToSet_probability_le_twoPoint_sum p _ f.1 A₂)
          (connectionToSet_probability_le_twoPoint_sum p _ f.2 B₂) measureReal_nonneg
          (Finset.sum_nonneg (fun _ _ => twoPoint_nonneg _ _ _)))
        (mul_nonneg measureReal_nonneg measureReal_nonneg)
        (mul_nonneg (Finset.sum_nonneg (fun _ _ => twoPoint_nonneg _ _ _))
          (Finset.sum_nonneg (fun _ _ => twoPoint_nonneg _ _ _)))

end NearCritical.Section10
