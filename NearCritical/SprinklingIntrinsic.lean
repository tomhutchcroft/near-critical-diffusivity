module

public import NearCritical.NestChainPath
public import Mathlib.Data.Finset.Lattice.Fold

/-! Literal finite maximum from source eq.def.rin_skl_AB. This module proves
its deterministic short-bridge consequence; it does not establish the random
pivotal set, typicality event, or its probability. Joining pairs are oriented
explicitly, since canonical positive-coordinate bond orientation need not point
from the source boundary towards the target boundary. -/
@[expose] public section
noncomputable section
namespace NearCritical

/-- Maximum finite intrinsic distance to a boundary, restricted to the root's
actual connected component. An empty intersection has radius zero. -/
def intrinsicBoundaryRadius {V : Type*} (G : SimpleGraph V) (root : V)
    (A : Finset V) : ℕ := by
  classical
  exact (A.filter fun x => G.Reachable root x).sup fun x => G.dist x root

lemma dist_le_intrinsicBoundaryRadius {V : Type*} (G : SimpleGraph V)
    (root : V) (A : Finset V) {x : V} (hx : x ∈ A) (hconn : G.Reachable root x) :
    G.dist x root ≤ intrinsicBoundaryRadius G root A := by
  classical
  unfold intrinsicBoundaryRadius
  exact Finset.le_sup (f := fun z => G.dist z root) (Finset.mem_filter.mpr ⟨hx, hconn⟩)

/-- Source intrinsic diameter: one joining edge plus the maximum over oriented
candidate pairs of the sum of the two boundary-to-endpoint radii. The supplied
side graphs are the actual deleted critical tube graphs at instantiation. -/
def sprinklingIntrinsicDiameter {d : ℕ} (G_L G_R : SimpleGraph (Vertex d))
    (A B : Finset (Vertex d)) (pivots : Finset (Vertex d × Vertex d)) : ℕ :=
  1 + pivots.sup fun e => intrinsicBoundaryRadius G_L e.1 A +
    intrinsicBoundaryRadius G_R e.2 B

lemma sprinklingIntrinsicDiameter_join_bound {d : ℕ}
    (G_L G_R : SimpleGraph (Vertex d)) (A B : Finset (Vertex d))
    (pivots : Finset (Vertex d × Vertex d)) {a b : Vertex d} (he : (a,b) ∈ pivots) :
    intrinsicBoundaryRadius G_L a A + 1 + intrinsicBoundaryRadius G_R b B ≤
      sprinklingIntrinsicDiameter G_L G_R A B pivots := by
  have h := Finset.le_sup (f := fun e : Vertex d × Vertex d =>
    intrinsicBoundaryRadius G_L e.1 A + intrinsicBoundaryRadius G_R e.2 B) he
  change intrinsicBoundaryRadius G_L a A + intrinsicBoundaryRadius G_R b B ≤ _ at h
  unfold sprinklingIntrinsicDiameter
  omega

/-- A single source diameter bound supplies the local metric bounds used by
NestChainPath. Reachability is explicit, so unreachable distances cannot become
zero through `edist.toNat`. No short bridge is an input. -/
theorem sprinkling_intrinsic_bounded_connection {d : ℕ} {ω : Configuration d}
    (D L R Q₁ F₁ Q₂ F₂ : Set (Vertex d))
    (hLD : L ⊆ D) (hRD : R ⊆ D) (hLQ : Disjoint L Q₂) (hRQ : Disjoint R Q₁)
    {G_L G_R : SimpleGraph (Vertex d)}
    (hGL : G_L ≤ microscopicPieceGraph ω L (exploredEdgeSet Q₁ F₁)ᶜ)
    (hGR : G_R ≤ microscopicPieceGraph ω R (exploredEdgeSet Q₂ F₂)ᶜ)
    (A B : Finset (Vertex d)) (pivots : Finset (Vertex d × Vertex d))
    {x a b y : Vertex d} (hxL : x ∈ L) (hbR : b ∈ R)
    (hx : x ∈ A) (hy : y ∈ B) (he : (a,b) ∈ pivots)
    (hleft : G_L.Reachable a x) (hright : G_R.Reachable b y)
    (hpivot : (openGraph ω).Adj a b) {K : ℝ}
    (hdiam : (sprinklingIntrinsicDiameter G_L G_R A B pivots : ℝ) ≤ K) :
    BoundedIntrinsicConnection (sprinklingBridgeGraph G_L G_R a b) x y K ∧
      sprinklingBridgeGraph G_L G_R a b ≤
        microscopicPieceGraph ω D (exploredEdgeSet Q₁ F₁ ∪ exploredEdgeSet Q₂ F₂)ᶜ := by
  have hl : BoundedIntrinsicConnection G_L x a (intrinsicBoundaryRadius G_L a A) := by
    refine ⟨hleft.symm, ?_⟩
    exact_mod_cast dist_le_intrinsicBoundaryRadius G_L a A hx hleft
  have hr : BoundedIntrinsicConnection G_R b y (intrinsicBoundaryRadius G_R b B) := by
    refine ⟨hright, ?_⟩
    have h := dist_le_intrinsicBoundaryRadius G_R b B hy hright
    rw [SimpleGraph.dist_comm] at h
    exact_mod_cast h
  have hbridge := sprinkling_bridge_bounded_connection D L R Q₁ F₁ Q₂ F₂
    hLD hRD hLQ hRQ hxL hbR hGL hGR hl hr hpivot
  have hsum : (intrinsicBoundaryRadius G_L a A : ℝ) + 1 +
      (intrinsicBoundaryRadius G_R b B : ℝ) ≤ K := by
    have h := sprinklingIntrinsicDiameter_join_bound G_L G_R A B pivots he
    have hR : (intrinsicBoundaryRadius G_L a A : ℝ) + 1 +
        (intrinsicBoundaryRadius G_R b B : ℝ) ≤
        (sprinklingIntrinsicDiameter G_L G_R A B pivots : ℝ) := by exact_mod_cast h
    exact hR.trans hdiam
  exact ⟨⟨hbridge.1, hbridge.2.trans hsum⟩,
    sprinklingBridgeGraph_le_deleted D L R Q₁ F₁ Q₂ F₂
      hLD hRD hLQ hRQ hGL hGR hxL hbR hleft.symm hpivot⟩

/-- Literal offspring incidence through an oriented candidate joining edge.
This records connectivity, not a bounded path. In the source the candidate
pairs are the opened pivotal bonds; that stochastic identification is separate. -/
def sprinklingOffspring {d : ℕ} {ι : Type*}
    (G_L G_R : SimpleGraph (Vertex d)) (A : Finset (Vertex d))
    (candidates : Finset ι) (boundary : ι → Finset (Vertex d))
    (pivots : Finset (Vertex d × Vertex d)) : Finset ι := by
  classical
  exact candidates.filter fun c => ∃ x ∈ A, ∃ y ∈ boundary c,
    ∃ e ∈ pivots, G_L.Reachable e.1 x ∧ G_R.Reachable e.2 y

lemma mem_sprinklingOffspring {d : ℕ} {ι : Type*}
    (G_L G_R : SimpleGraph (Vertex d)) (A : Finset (Vertex d))
    (candidates : Finset ι) (boundary : ι → Finset (Vertex d))
    (pivots : Finset (Vertex d × Vertex d)) (c : ι) :
    c ∈ sprinklingOffspring G_L G_R A candidates boundary pivots ↔
      c ∈ candidates ∧ ∃ x ∈ A, ∃ y ∈ boundary c,
        ∃ e ∈ pivots, G_L.Reachable e.1 x ∧ G_R.Reachable e.2 y := by
  classical
  simp [sprinklingOffspring]

/-- All target boundary points in the finite offspring candidate family. -/
def sprinklingTargetBoundary {d : ℕ} {ι : Type*} (candidates : Finset ι)
    (boundary : ι → Finset (Vertex d)) : Finset (Vertex d) := by
  classical
  exact candidates.biUnion boundary

lemma mem_sprinklingTargetBoundary {d : ℕ} {ι : Type*} (candidates : Finset ι)
    (boundary : ι → Finset (Vertex d)) {c : ι} {y : Vertex d}
    (hc : c ∈ candidates) (hy : y ∈ boundary c) :
    y ∈ sprinklingTargetBoundary candidates boundary := by
  classical
  exact Finset.mem_biUnion.mpr ⟨c, hc, hy⟩

/-- Membership of the next representative in the offspring set, together with
one typical source rin bound, constructs the short bridge into that cluster.
The diameter uses the union of all candidate target boundaries, exactly as in
the source sprinkling cluster. No per-child short-connection bound is assumed. -/
theorem sprinkling_offspring_short_bridge {d : ℕ} {ι : Type*} {ω : Configuration d}
    (D L R Q₁ F₁ Q₂ F₂ : Set (Vertex d))
    (hLD : L ⊆ D) (hRD : R ⊆ D) (hLQ : Disjoint L Q₂) (hRQ : Disjoint R Q₁)
    {G_L G_R : SimpleGraph (Vertex d)}
    (hGL : G_L ≤ microscopicPieceGraph ω L (exploredEdgeSet Q₁ F₁)ᶜ)
    (hGR : G_R ≤ microscopicPieceGraph ω R (exploredEdgeSet Q₂ F₂)ᶜ)
    (A : Finset (Vertex d)) (candidates : Finset ι)
    (boundary : ι → Finset (Vertex d)) (pivots : Finset (Vertex d × Vertex d))
    (hAL : ∀ x ∈ A, x ∈ L)
    (hpivots : ∀ e ∈ pivots, e.2 ∈ R ∧ (openGraph ω).Adj e.1 e.2)
    {c : ι} (hc : c ∈ sprinklingOffspring G_L G_R A candidates boundary pivots)
    {K : ℝ}
    (hdiam : (sprinklingIntrinsicDiameter G_L G_R A
      (sprinklingTargetBoundary candidates boundary) pivots : ℝ) ≤ K) :
    ∃ x ∈ A, ∃ y ∈ boundary c, ∃ a b,
      (a,b) ∈ pivots ∧
      BoundedIntrinsicConnection (sprinklingBridgeGraph G_L G_R a b) x y K ∧
      sprinklingBridgeGraph G_L G_R a b ≤
        microscopicPieceGraph ω D (exploredEdgeSet Q₁ F₁ ∪ exploredEdgeSet Q₂ F₂)ᶜ := by
  classical
  obtain ⟨hcand, x, hx, y, hy, e, he, hl, hr⟩ :=
    (mem_sprinklingOffspring G_L G_R A candidates boundary pivots c).mp hc
  have hyB := mem_sprinklingTargetBoundary candidates boundary hcand hy
  obtain ⟨hb, hopen⟩ := hpivots e he
  have h := sprinkling_intrinsic_bounded_connection D L R Q₁ F₁ Q₂ F₂
    hLD hRD hLQ hRQ hGL hGR A (sprinklingTargetBoundary candidates boundary) pivots
    (hAL x hx) hb hx hyB he hl hr hopen hdiam
  exact ⟨x, hx, y, hy, e.1, e.2, he, h⟩

end NearCritical
