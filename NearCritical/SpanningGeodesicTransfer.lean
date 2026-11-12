module

public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Tactic

/-! NEW lem.arm.2dspanning: the metric step in transferring corridor paths
through a pointed correspondence. Standard real-tree projection geometry is
explicit; no scaling-limit or path-containment conclusion is a premise. -/
@[expose] public section
namespace NearCritical

/-- Three pairwise distortion errors control the limiting triangle excess of
an exact discrete geodesic point. This is the source's 3epsilon estimate. -/
theorem correspondence_geodesic_excess_le
    {X T : Type*} [PseudoMetricSpace X] [PseudoMetricSpace T]
    (R : X → T → Prop) (ε : ℝ)
    (hdist : ∀ x t x' t', R x t → R x' t' → |dist x x' - dist t t'| ≤ ε)
    {o a v : X} {r b y : T} (hor : R o r) (hab : R a b) (hvy : R v y)
    (hgeo : dist o a + dist a v = dist o v) :
    dist r b + dist b y - dist r y ≤ 3*ε := by
  have h1 := abs_le.mp (hdist o r a b hor hab)
  have h2 := abs_le.mp (hdist a b v y hab hvy)
  have h3 := abs_le.mp (hdist o r v y hor hvy)
  linarith

/-- The standard real-tree tripod projection formula converts the derived
triangle excess into the source's 3epsilon/2 distance to a limiting geodesic. -/
theorem correspondence_geodesic_near_projection
    {X T : Type*} [PseudoMetricSpace X] [PseudoMetricSpace T]
    (R : X → T → Prop) (ε : ℝ)
    (hdist : ∀ x t x' t', R x t → R x' t' → |dist x x' - dist t t'| ≤ ε)
    (treeProjection : ∀ r y b : T, ∃ c : T,
      dist r c + dist c y = dist r y ∧
        2*dist b c = dist r b + dist b y - dist r y)
    {o a v : X} {r b y : T} (hor : R o r) (hab : R a b) (hvy : R v y)
    (hgeo : dist o a + dist a v = dist o v) :
    ∃ c : T, dist r c + dist c y = dist r y ∧ dist b c ≤ 3*ε/2 := by
  obtain ⟨c,hc,hproj⟩ := treeProjection r y b
  have he := correspondence_geodesic_excess_le R ε hdist hor hab hvy hgeo
  exact ⟨c,hc,by linarith⟩

/-- Pairwise embedding agreement plus a modulus for the limiting embedding
transfers EVERY exact discrete geodesic point close to the embedded limiting
geodesic. The raw modulus is independent of the correspondence and path. -/
theorem correspondence_geodesic_embedding_near
    {X T Z : Type*} [PseudoMetricSpace X] [PseudoMetricSpace T] [PseudoMetricSpace Z]
    (R : X → T → Prop) (ε η : ℝ)
    (hdist : ∀ x t x' t', R x t → R x' t' → |dist x x' - dist t t'| ≤ ε)
    (treeProjection : ∀ r y b : T, ∃ c : T,
      dist r c + dist c y = dist r y ∧
        2*dist b c = dist r b + dist b y - dist r y)
    (F : X → Z) (Φ : T → Z)
    (hembed : ∀ x t, R x t → dist (F x) (Φ t) ≤ ε)
    (hmodulus : ∀ s t : T, dist s t ≤ 3*ε/2 → dist (Φ s) (Φ t) ≤ η)
    {o a v : X} {r b y : T} (hor : R o r) (hab : R a b) (hvy : R v y)
    (hgeo : dist o a + dist a v = dist o v) :
    ∃ c : T, dist r c + dist c y = dist r y ∧ dist (F a) (Φ c) ≤ ε+η := by
  obtain ⟨c,hc,hnear⟩ := correspondence_geodesic_near_projection R ε hdist treeProjection
    hor hab hvy hgeo
  refine ⟨c,hc,?_⟩
  exact (dist_triangle (F a) (Φ b) (Φ c)).trans
    (add_le_add (hembed a b hab) (hmodulus b c hnear))

/-- Uniform continuity of the limiting embedding supplies the raw geodesic
modulus at all sufficiently small distortion scales; no modulus is assumed. -/
theorem uniformContinuous_geodesic_modulus
    {T Z : Type*} [PseudoMetricSpace T] [PseudoMetricSpace Z]
    (Φ : T → Z) (hΦ : UniformContinuous Φ) {η : ℝ} (hη : 0 < η) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, ε ≤ ε₀ →
      ∀ s t : T, dist s t ≤ 3*ε/2 → dist (Φ s) (Φ t) ≤ η := by
  obtain ⟨δ,hδ,hmod⟩ := Metric.uniformContinuous_iff_le.mp hΦ η hη
  refine ⟨2*δ/3,by positivity,?_⟩
  intro ε hε s t hst
  apply hmod
  linarith

end NearCritical
