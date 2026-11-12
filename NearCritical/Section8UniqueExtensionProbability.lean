module
public import NearCritical.Section8UniqueExtensionSurgery
public import NearCritical.FiniteSurgeryProbability
public import NearCritical.Section9FreshEvent

/-! Actual finite-energy unique-extension comparison, including the revealed law. -/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory
open scoped Classical

private theorem extension_avoidance_locality {d : ℕ}
    (T Q F B W : Finset (Vertex d)) (root : Vertex d) :
    ∀ ω θ : Configuration d,
      (∀ b ∈ sprinklingAvailableBonds T Q F, ω b = θ b) →
      (ω ∈ section9AvoidanceEvent T T Q F B W root ↔
       θ ∈ section9AvoidanceEvent T T Q F B W root) := by
  intro ω θ hagree
  have heq := sprinklingUnexploredCluster_eq_of_available_agree T Q F ω θ hagree root
  simp only [section9AvoidanceEvent,Set.mem_setOf_eq,heq]

private theorem extension_event_cylinder {d : ℕ} (T Q F B W : Finset (Vertex d))
    (root : Vertex d) :
    section9AvoidanceEvent T T Q F B W root =
      (sprinklingAvailableBonds T Q F).restrict ⁻¹'
        {ξ | extendConfiguration (sprinklingAvailableBonds T Q F) (fun _ => false) ξ ∈
          section9AvoidanceEvent T T Q F B W root} := by
  ext ω
  apply extension_avoidance_locality T Q F B W root ω
    (extendConfiguration (sprinklingAvailableBonds T Q F) (fun _ => false)
      ((sprinklingAvailableBonds T Q F).restrict ω))
  intro b hb
  simp [extendConfiguration,hb]

/-- The actual surgery gives a finite-energy comparison for the two literal
unique-extension avoidance events. The coefficient is explicit and includes
p=0 and p=1; no random connection or desired probability estimate is assumed. -/
theorem section8_unique_extension_surgery_probability {d : ℕ} (p : unitInterval)
    (T Q F I W : Finset (Vertex d)) (x x' z : Vertex d)
    (hIT : I ⊆ T) (hx : x ∈ I) (hx' : x' ∈ I) (hz : z ∉ I)
    (hIW : ∀ y ∈ I, y ∈ W → y = x)
    (hconnected : ∀ u ∈ I,
      (sprinklingUnexploredGraph (fun _ : Bond d => true) I Q F).Reachable x u) :
    (min (p : ℝ) (1-(p : ℝ)))^(sprinklingClusterFiberMask T Q F I).card *
      (percolation d p).real (section9AvoidanceEvent T T Q F {z} W x') ≤
      (percolation d p).real (section9AvoidanceEvent T T Q F {z} (W \ {x}) x) := by
  let G := sprinklingAvailableBonds T Q F
  let U := sprinklingClusterFiberMask T Q F I
  let A := section9AvoidanceEvent T T Q F {z} (W \ {x}) x
  let B := section9AvoidanceEvent T T Q F {z} W x'
  let A₀ : Set (G → Bool) := {ξ | extendConfiguration G (fun _ => false) ξ ∈ A}
  let B₀ : Set (G → Bool) := {ξ | extendConfiguration G (fun _ => false) ξ ∈ B}
  have hA : A = G.restrict ⁻¹' A₀ := extension_event_cylinder T Q F {z} (W \ {x}) x
  have hB : B = G.restrict ⁻¹' B₀ := extension_event_cylinder T Q F {z} W x'
  have hsurgery : ∀ ω : Configuration d, G.restrict ω ∈ B₀ →
      ∃ θ : Configuration d, (∀ b, b ∉ U → θ b = ω b) ∧ G.restrict θ ∈ A₀ := by
    intro ω hω
    have hshift : ω ∈ B := by rw [hB]; exact hω
    obtain ⟨θ,hoff,hθ,_⟩ := section8_unique_extension_surgery ω T Q F I W x x' z
      hIT hx hx' hz hIW hconnected hshift
    refine ⟨θ,hoff,?_⟩
    change θ ∈ G.restrict ⁻¹' A₀
    rw [← hA]
    exact hθ
  have hb := percolation_finite_surgery_probability p G U A₀ B₀ hsurgery
  rw [← hA,← hB] at hb
  exact hb

/-- The same actual finite-energy comparison holds under a positive outer
heart-reveal law. The second heart cube is disjoint from T, and freshness of
the exact available surgery graph is derived rather than assumed. -/
theorem section8_unique_extension_surgery_revealed_probability {d : ℕ} (p : unitInterval)
    (T Q F I W H Q₃ H₃ F₃ : Finset (Vertex d)) (x x' z : Vertex d)
    (hH : H ⊆ Q) (hH₃ : H₃ ⊆ Q₃)
    (hpos : percolation d p (section9RevealEvent Q H Q₃ H₃ F F₃) ≠ 0)
    (hTQ₃ : Disjoint T Q₃)
    (hIT : I ⊆ T) (hx : x ∈ I) (hx' : x' ∈ I) (hz : z ∉ I)
    (hIW : ∀ y ∈ I, y ∈ W → y = x)
    (hconnected : ∀ u ∈ I,
      (sprinklingUnexploredGraph (fun _ : Bond d => true) I Q F).Reachable x u) :
    let ν := section9RevealedLaw p Q H Q₃ H₃ F F₃
    (min (p : ℝ) (1-(p : ℝ)))^(sprinklingClusterFiberMask T Q F I).card *
      ν.real (section9AvoidanceEvent T T Q F {z} W x') ≤
      ν.real (section9AvoidanceEvent T T Q F {z} (W \ {x}) x) := by
  intro ν
  let G := sprinklingAvailableBonds T Q F
  have hfresh : Disjoint (clusterRevealBonds Q F ∪ clusterRevealBonds Q₃ F₃) G := by
    apply Finset.disjoint_left.mpr
    intro b hbReveal hbG
    rcases Finset.mem_union.mp hbReveal with hbFirst | hbThird
    · exact (Finset.mem_sdiff.mp hbG).2 hbFirst
    · have hbT := (mem_internalBondSet T b).mp (Finset.mem_sdiff.mp hbG).1
      have hbQ₃ := (mem_clusterRevealBonds Q₃ F₃ b).mp hbThird
      exact Finset.disjoint_left.mp hTQ₃ hbT.1 hbQ₃.1
  have heq (W' : Finset (Vertex d)) (root : Vertex d) :
      ν.real (section9AvoidanceEvent T T Q F {z} W' root) =
      (percolation d p).real (section9AvoidanceEvent T T Q F {z} W' root) := by
    apply section9RevealedLaw_fresh_probability p Q H Q₃ H₃ F F₃ hH hH₃ hpos G hfresh
    · exact (measurableSet_sprinklingUnexploredCluster_hits T Q F {z} root).inter
        (measurableSet_sprinklingUnexploredCluster_hits T Q F W' root).compl
    · exact extension_avoidance_locality T Q F {z} W' root
  rw [heq W x',heq (W \ {x}) x]
  exact section8_unique_extension_surgery_probability p T Q F I W x x' z
    hIT hx hx' hz hIW hconnected

end NearCritical
