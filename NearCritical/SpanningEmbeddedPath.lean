module

public import NearCritical.SpanningGeodesicTransfer
public import NearCritical.SpanningScaledEmbedding

/-! NEW lem.arm.2dspanning deterministic embedded-path assembly. A chosen
metric on lattice vertices is explicit and is NOT identified here with the
rescaled chemical metric; that instance remains a source obligation. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Set
open scoped Classical

/-- Construct the actual restricted walk from support containment. -/
def openWalkRestrictOfSupport {d : ℕ} {ω : Configuration d} (D : Set (Vertex d))
    {x y : Vertex d} (w : (openGraph ω).Walk x y) :
    (∀ z ∈ w.support, z ∈ D) → (restrictedGraph ω D).Walk x y := by
  induction w with
  | nil => intro _; exact .nil
  | @cons a b c hab w ih =>
    intro h
    have ht : ∀ z ∈ w.support, z ∈ D := by
      intro z hz
      exact h z (by simp only [SimpleGraph.Walk.support_cons, List.mem_cons]; exact Or.inr hz)
    exact .cons ⟨hab,h a (by simp),ht b w.start_mem_support⟩ (ih ht)

/-- Corresponding exact geodesic paths inside a robust limiting corridor
produce an ACTUAL source-cuboid connection, not merely close point clouds. -/
theorem embedded_geodesic_source_connection {d n : ℕ} [PseudoMetricSpace (Vertex d)]
    {T : Type*} [PseudoMetricSpace T] (hn : 1 ≤ n)
    (f : Fin d × Bool) (ω : Configuration d) {o v : Vertex d}
    (w : (openGraph ω).Walk o v) (R : Vertex d → T → Prop) (ε η : ℝ)
    (hη : 0 ≤ η) (hsmall : ε+η ≤ (1/32:ℝ))
    (hdist : ∀ x t x' t', R x t → R x' t' → |dist x x'-dist t t'| ≤ ε)
    (treeProjection : ∀ r y b : T, ∃ c : T,
      dist r c+dist c y = dist r y ∧ 2*dist b c = dist r b+dist b y-dist r y)
    (Φ : T → (Fin d → ℝ))
    (hembed : ∀ x t, R x t → dist (scaledSpanningVertex n x) (Φ t) ≤ ε)
    (hmodulus : ∀ s t : T, dist s t ≤ 3*ε/2 → dist (Φ s) (Φ t) ≤ η)
    {r y : T} (hor : R o r) (hvy : R v y)
    (hcover : ∀ a ∈ w.support, ∃ b : T, R a b)
    (hgeo : ∀ a ∈ w.support, dist o a+dist a v = dist o v)
    (hcorridor : ∀ c : T, dist r c+dist c y = dist r y →
      (-(1/4:ℝ) ≤ realSpanningHeight f (Φ c) ∧ realSpanningHeight f (Φ c) ≤ 5/2) ∧
        (∀ j, j ≠ f.1 → |Φ c j| ≤ (1/32:ℝ)))
    (htarget : |realSpanningHeight f (Φ y)-2| ≤ (1/32:ℝ))
    (htargetTransverse : ∀ j, j ≠ f.1 → |Φ y j| ≤ (1/32:ℝ)) :
    ω ∈ connectionToSetEvent (roundedSourceSpanningCuboid n f) o (roundedSourceSpanningTarget n f) := by
  have hpath : ∀ a ∈ w.support, a ∈ roundedSourceSpanningCuboid n f := by
    intro a ha
    obtain ⟨b,hab⟩ := hcover a ha
    obtain ⟨c,hc,hnear⟩ := correspondence_geodesic_embedding_near R ε η hdist treeProjection
      (scaledSpanningVertex n) Φ hembed hmodulus hor hab hvy (hgeo a ha)
    obtain ⟨hh,ht⟩ := hcorridor c hc
    exact spanning_limit_corridor_to_integer hn f a (Φ c) (hnear.trans hsmall) hh ht
  have hend : v ∈ roundedSourceSpanningTarget n f := by
    have he : dist (scaledSpanningVertex n v) (Φ y) ≤ (1/32:ℝ) :=
      (hembed v y hvy).trans (by linarith)
    exact spanning_limit_target_to_integer hn f v (Φ y) he htarget htargetTransverse
  exact ⟨hpath o w.start_mem_support,v,hend,hpath v w.end_mem_support,
    ⟨openWalkRestrictOfSupport (roundedSourceSpanningCuboid n f) w hpath⟩⟩

end NearCritical
