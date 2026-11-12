module
public import NearCritical.Section9FreshEvent
public import NearCritical.Section9FiniteGeometry
public import NearCritical.Section9AvoidanceCertificate

/-! Actual right-tube events retain their probability under outer heart reveal. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory
open scoped Classical

private theorem right_source_available_fresh {d : ℕ} (i : Fin d) (n : ℕ) (hn : 0 < n)
    (F₁ F₃ : Finset (Vertex d)) :
    let Q₁ := section9FiniteEndCube i n 0
    let Q₃ := section9FiniteEndCube i n (2*(n : ℝ))
    let R := section9FiniteTube i n (-(3 : ℝ)/8) (5/8)
    Disjoint (clusterRevealBonds Q₁ F₁ ∪ clusterRevealBonds Q₃ F₃)
      (sprinklingAvailableBonds R Q₃ F₃) := by
  intro Q₁ Q₃ R
  apply Finset.disjoint_left.mpr
  intro b hbReveal hbAvailable
  rcases Finset.mem_union.mp hbReveal with hbFirst | hbThird
  · have hbR := (mem_internalBondSet R b).mp (Finset.mem_sdiff.mp hbAvailable).1
    have hbQ₁ := (mem_clusterRevealBonds Q₁ F₁ b).mp hbFirst
    exact Finset.disjoint_left.mp (section9FiniteRightTube_disjoint_first i hn) hbR.1 hbQ₁.1
  · exact (Finset.mem_sdiff.mp hbAvailable).2 hbThird

/-- The actual right deleted-cluster hit event has its ordinary probability
under the positive source outer-heart law. Targets and roots are arbitrary;
no connection or freshness premise is supplied. -/
theorem section9_source_right_hit_fresh_probability {d : ℕ} (p : unitInterval)
    (i : Fin d) (n : ℕ) (hn : 0 < n)
    (H₁ H₃ F₁ F₃ B : Finset (Vertex d)) (z : Vertex d)
    (hH₁ : H₁ ⊆ section9FiniteEndCube i n 0)
    (hH₃ : H₃ ⊆ section9FiniteEndCube i n (2*(n : ℝ)))
    (hpos : percolation d p (section9RevealEvent
      (section9FiniteEndCube i n 0) H₁ (section9FiniteEndCube i n (2*(n : ℝ))) H₃ F₁ F₃) ≠ 0) :
    let Q₁ := section9FiniteEndCube i n 0
    let Q₃ := section9FiniteEndCube i n (2*(n : ℝ))
    let R := section9FiniteTube i n (-(3 : ℝ)/8) (5/8)
    let ν := section9RevealedLaw p Q₁ H₁ Q₃ H₃ F₁ F₃
    ν.real {ω | (sprinklingUnexploredCluster ω R Q₃ F₃ z ∩ B).Nonempty} =
      (percolation d p).real {ω | (sprinklingUnexploredCluster ω R Q₃ F₃ z ∩ B).Nonempty} := by
  intro Q₁ Q₃ R ν
  apply section9RevealedLaw_fresh_probability p Q₁ H₁ Q₃ H₃ F₁ F₃ hH₁ hH₃ hpos
    (sprinklingAvailableBonds R Q₃ F₃) (right_source_available_fresh i n hn F₁ F₃)
  · exact measurableSet_sprinklingUnexploredCluster_hits R Q₃ F₃ B z
  · intro ω θ hagree
    have heq := sprinklingUnexploredCluster_eq_of_available_agree R Q₃ F₃ ω θ hagree z
    simp only [Set.mem_setOf_eq,heq]

/-- The actual nonmonotone right avoidance event also retains its ordinary
probability. Its positive connection and full nonhit test use the SAME right
tube and fixed explored-edge deletion, all local to the actual available mask. -/
theorem section9_source_right_avoidance_fresh_probability {d : ℕ} (p : unitInterval)
    (i : Fin d) (n : ℕ) (hn : 0 < n)
    (H₁ H₃ F₁ F₃ B V : Finset (Vertex d)) (z : Vertex d)
    (hH₁ : H₁ ⊆ section9FiniteEndCube i n 0)
    (hH₃ : H₃ ⊆ section9FiniteEndCube i n (2*(n : ℝ)))
    (hpos : percolation d p (section9RevealEvent
      (section9FiniteEndCube i n 0) H₁ (section9FiniteEndCube i n (2*(n : ℝ))) H₃ F₁ F₃) ≠ 0) :
    let Q₁ := section9FiniteEndCube i n 0
    let Q₃ := section9FiniteEndCube i n (2*(n : ℝ))
    let R := section9FiniteTube i n (-(3 : ℝ)/8) (5/8)
    let ν := section9RevealedLaw p Q₁ H₁ Q₃ H₃ F₁ F₃
    ν.real (section9AvoidanceEvent R R Q₃ F₃ B V z) =
      (percolation d p).real (section9AvoidanceEvent R R Q₃ F₃ B V z) := by
  intro Q₁ Q₃ R ν
  apply section9RevealedLaw_fresh_probability p Q₁ H₁ Q₃ H₃ F₁ F₃ hH₁ hH₃ hpos
    (sprinklingAvailableBonds R Q₃ F₃) (right_source_available_fresh i n hn F₁ F₃)
  · exact (measurableSet_sprinklingUnexploredCluster_hits R Q₃ F₃ B z).inter
      (measurableSet_sprinklingUnexploredCluster_hits R Q₃ F₃ V z).compl
  · intro ω θ hagree
    have heq := sprinklingUnexploredCluster_eq_of_available_agree R Q₃ F₃ ω θ hagree z
    simp only [section9AvoidanceEvent,Set.mem_setOf_eq,heq]

end NearCritical
