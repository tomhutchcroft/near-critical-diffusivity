module

public import NearCritical.Section9PivotalResamplingComparison
public import NearCritical.Section9PivotalSupport
public import NearCritical.Section9PivotalCount

@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory
open scoped Classical

/-- All available bonds examined when revealing one deleted-tube component,
including its closed boundary bonds. -/
def sprinklingClusterRevealBonds {d : ℕ} (ω : Configuration d)
    (T Q F : Finset (Vertex d)) (root : Vertex d) : Finset (Bond d) :=
  (sprinklingAvailableBonds T Q F).filter fun b =>
    b.1 ∈ sprinklingUnexploredCluster ω T Q F root ∨
      bondTip b ∈ sprinklingUnexploredCluster ω T Q F root

/-- Source R(e), retaining bonds examined by either tube exploration. -/
def section9TwoClusterRevealBonds {d : ℕ} (ω : Configuration d)
    (L R Q₁ F₁ Q₃ F₃ : Finset (Vertex d)) (e : Vertex d × Vertex d) : Finset (Bond d) :=
  sprinklingClusterRevealBonds ω L Q₁ F₁ e.1 ∪
    sprinklingClusterRevealBonds ω R Q₃ F₃ e.2

theorem section9TwoClusterRevealBonds_touches {d : ℕ} (ω : Configuration d)
    (L R Q₁ F₁ Q₃ F₃ : Finset (Vertex d)) (e : Vertex d × Vertex d) :
    ∀ b ∈ section9TwoClusterRevealBonds ω L R Q₁ F₁ Q₃ F₃ e,
      b.1 ∈ sprinklingUnexploredCluster ω L Q₁ F₁ e.1 ∪
        sprinklingUnexploredCluster ω R Q₃ F₃ e.2 ∨
      bondTip b ∈ sprinklingUnexploredCluster ω L Q₁ F₁ e.1 ∪
        sprinklingUnexploredCluster ω R Q₃ F₃ e.2 := by
  intro b hb
  rcases Finset.mem_union.mp hb with hL | hR
  · rcases (Finset.mem_filter.mp hL).2 with h | h
    · exact Or.inl (Finset.mem_union_left _ h)
    · exact Or.inr (Finset.mem_union_left _ h)
  · rcases (Finset.mem_filter.mp hR).2 with h | h
    · exact Or.inl (Finset.mem_union_right _ h)
    · exact Or.inr (Finset.mem_union_right _ h)

theorem measurableSet_sprinklingClusterRevealBonds_mem {d : ℕ}
    (T Q F : Finset (Vertex d)) (root : Vertex d) (b : Bond d) :
    MeasurableSet {ω | b ∈ sprinklingClusterRevealBonds ω T Q F root} := by
  have he : {ω : Configuration d | b ∈ sprinklingClusterRevealBonds ω T Q F root} =
      {ω | b ∈ sprinklingAvailableBonds T Q F} ∩
        ({ω | b.1 ∈ sprinklingUnexploredCluster ω T Q F root} ∪
          {ω | bondTip b ∈ sprinklingUnexploredCluster ω T Q F root}) := by
    ext ω
    simp [sprinklingClusterRevealBonds]
  rw [he]
  exact (MeasurableSet.const _).inter
    ((measurableSet_sprinklingUnexploredCluster_mem T Q F root b.1).union
      (measurableSet_sprinklingUnexploredCluster_mem T Q F root (bondTip b)))

theorem measurableSet_section9TwoClusterRevealBonds_mem {d : ℕ}
    (L R Q₁ F₁ Q₃ F₃ : Finset (Vertex d)) (e : Vertex d × Vertex d) (b : Bond d) :
    MeasurableSet {ω | b ∈ section9TwoClusterRevealBonds ω L R Q₁ F₁ Q₃ F₃ e} := by
  have he : {ω : Configuration d | b ∈ section9TwoClusterRevealBonds ω L R Q₁ F₁ Q₃ F₃ e} =
      {ω | b ∈ sprinklingClusterRevealBonds ω L Q₁ F₁ e.1} ∪
        {ω | b ∈ sprinklingClusterRevealBonds ω R Q₃ F₃ e.2} := by
    ext ω
    simp [section9TwoClusterRevealBonds]
  rw [he]
  exact (measurableSet_sprinklingClusterRevealBonds_mem L Q₁ F₁ e.1 b).union
    (measurableSet_sprinklingClusterRevealBonds_mem R Q₃ F₃ e.2 b)

/-- The adaptive two-cluster replacement is a measurable random configuration. -/
theorem measurable_section9TwoClusterResample {d : ℕ}
    (L R Q₁ F₁ Q₃ F₃ : Finset (Vertex d)) (e : Vertex d × Vertex d) :
    Measurable (fun z : Configuration d × Configuration d =>
      resampleBonds (section9TwoClusterRevealBonds z.1 L R Q₁ F₁ Q₃ F₃ e) z.1 z.2) := by
  apply measurable_pi_iff.mpr
  intro b
  exact Measurable.ite
    ((measurableSet_section9TwoClusterRevealBonds_mem L R Q₁ F₁ Q₃ F₃ e b).preimage measurable_fst)
    ((measurable_pi_apply b).comp measurable_snd) ((measurable_pi_apply b).comp measurable_fst)

end NearCritical
