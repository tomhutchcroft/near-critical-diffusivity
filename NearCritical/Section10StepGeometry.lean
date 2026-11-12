module

public import NearCritical.Section10ChainPath
public import NearCritical.Section10TypicalNestTrace
public import NearCritical.NestRepresentative
public import NearCritical.Section9SprinklingConnection

/-! One sprinkling step of `lem.nw.path` with the ACTUAL Section 9 objects.

Critical configuration `crit`, supercritical `ωor` above it. The step goes from
the typical cube at `c₁` to the one at `c₃` through the regions `L`, `R`
(the two Section 9 half tubes), with the unexplored graphs
`sprinklingUnexploredGraph crit L Q₁ F₁`, `... R Q₃ F₃` and a set of pivot pairs
open in `ωor`.

`typical_step_clause`: if `rep` is a typical cluster of the first cube, the
sprinkling cluster has intrinsic diameter at most `K`, and every cluster of the
next nest is an offspring of `rep`, then
* each next cluster is reached from a boundary point of `rep` by a bridge of
  length at most `K` inside the confined supercritical graph, and
* any two face-boundary points of `rep` are joined inside `rep` within
  `2 * diameterUpper * (2t)^2`.
These are exactly the two step hypotheses of `chainSurvives_geometry`.
-/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open scoped Classical

lemma restrictedGraph_mono_of_le {d : ℕ} {ω η : Configuration d}
    (hmono : ∀ e, ω e = true → η e = true) {S T : Set (Vertex d)} (hST : S ⊆ T) :
    restrictedGraph ω S ≤ restrictedGraph η T := by
  rintro x y ⟨⟨e, he, h⟩, hx, hy⟩
  exact ⟨⟨e, hmono e he, h⟩, hST hx, hST hy⟩

lemma microscopicPieceGraph_le_restrictedGraph {d : ℕ} (ω : Configuration d)
    (S : Set (Vertex d)) (A : Set (Sym2 (Vertex d))) :
    microscopicPieceGraph ω S A ≤ restrictedGraph ω S := by
  rintro x y ⟨hxy, hx, hy, _⟩
  exact ⟨hxy, hx, hy⟩

theorem typical_step_clause {d : ℕ} [Nontrivial (Fin d × Bool)] (a : TypicalParameters)
    (t : ℕ) (c₁ c₃ : Vertex d) {crit ωor : Configuration d}
    (hmono : ∀ e, crit e = true → ωor e = true) (Dom : Set (Vertex d))
    (L R F₁ F₃ : Finset (Vertex d))
    (hLD : (L : Set (Vertex d)) ⊆ Dom) (hRD : (R : Set (Vertex d)) ⊆ Dom)
    (hLQ : Disjoint (L : Set (Vertex d)) (typicalCube t c₃ : Set (Vertex d)))
    (hRQ : Disjoint (R : Set (Vertex d)) (typicalCube t c₁ : Set (Vertex d)))
    (hQD : (typicalCube t c₁ : Set (Vertex d)) ⊆ Dom)
    (src tgt : Finset (Vertex d) → Finset (Vertex d))
    (cand : Finset (Finset (Vertex d))) (pivots : Finset (Vertex d × Vertex d))
    (hpiv : ∀ e ∈ pivots, e.2 ∈ R ∧ (openGraph ωor).Adj e.1 e.2)
    (rep : Finset (Vertex d)) (hrep : rep ∈ typicalClusterFamily a t c₁ crit)
    (hrepQ : rep ⊆ typicalCube t c₁)
    (hsrcL : ∀ x ∈ src rep, x ∈ L)
    (hsrcbd : src rep ⊆ clusterFaceBoundary rep (typicalFace t c₁))
    (htgt : ∀ C, tgt C ⊆ clusterFaceBoundary C (typicalFace t c₃))
    {K : ℝ} (hdiam : (sprinklingIntrinsicDiameter
      (sprinklingUnexploredGraph crit L (typicalCube t c₁) F₁)
      (sprinklingUnexploredGraph crit R (typicalCube t c₃) F₃) (src rep)
      (sprinklingTargetBoundary cand tgt) pivots : ℝ) ≤ K)
    (next : Set (Finset (Vertex d)))
    (hnext : ∀ c' ∈ next, c' ∈ sprinklingOffspring
      (sprinklingUnexploredGraph crit L (typicalCube t c₁) F₁)
      (sprinklingUnexploredGraph crit R (typicalCube t c₃) F₃) (src rep) cand tgt pivots) :
    (∀ c' ∈ next, ∃ u ∈ (clusterFaceBoundary rep (typicalFace t c₁) : Set (Vertex d)),
      ∃ v ∈ (clusterFaceBoundary c' (typicalFace t c₃) : Set (Vertex d)),
      ∃ D : SimpleGraph (Vertex d), D ≤ restrictedGraph ωor Dom ∧
        BoundedIntrinsicConnection D u v K) ∧
    ∀ p ∈ (clusterFaceBoundary rep (typicalFace t c₁) : Set (Vertex d)),
      ∀ u ∈ (clusterFaceBoundary rep (typicalFace t c₁) : Set (Vertex d)),
      ∃ C : SimpleGraph (Vertex d), C ≤ restrictedGraph ωor Dom ∧
        BoundedIntrinsicConnection C p u (2 * (a.diameterUpper * (2 * (t : ℝ)) ^ 2)) := by
  constructor
  · intro c' hc'
    have hGL : sprinklingUnexploredGraph crit L (typicalCube t c₁) F₁ ≤
        microscopicPieceGraph ωor (L : Set (Vertex d))
          (exploredEdgeSet (typicalCube t c₁ : Set (Vertex d)) (F₁ : Set (Vertex d)))ᶜ :=
      sprinklingUnexploredGraph_mono hmono L (typicalCube t c₁) F₁
    have hGR : sprinklingUnexploredGraph crit R (typicalCube t c₃) F₃ ≤
        microscopicPieceGraph ωor (R : Set (Vertex d))
          (exploredEdgeSet (typicalCube t c₃ : Set (Vertex d)) (F₃ : Set (Vertex d)))ᶜ :=
      sprinklingUnexploredGraph_mono hmono R (typicalCube t c₃) F₃
    obtain ⟨x, hx, y, hy, e1, e2, _, hconn, hle⟩ :=
      sprinkling_offspring_short_bridge Dom (L : Set (Vertex d)) (R : Set (Vertex d))
        (typicalCube t c₁ : Set (Vertex d)) (F₁ : Set (Vertex d))
        (typicalCube t c₃ : Set (Vertex d)) (F₃ : Set (Vertex d)) hLD hRD hLQ hRQ hGL hGR
        (src rep) cand tgt pivots hsrcL hpiv (hnext c' hc') hdiam
    exact ⟨x, Finset.mem_coe.mpr (hsrcbd hx), y, Finset.mem_coe.mpr (htgt c' hy), _,
      hle.trans (microscopicPieceGraph_le_restrictedGraph ωor Dom _), hconn⟩
  · intro p hp u hu
    refine ⟨restrictedGraph crit (rep : Set (Vertex d)), ?_,
      typicalCluster_boundary_connection a t c₁ crit hrep (Finset.mem_coe.mp hp)
        (Finset.mem_coe.mp hu)⟩
    exact restrictedGraph_mono_of_le hmono
      (fun x hx => hQD (Finset.mem_coe.mpr (hrepQ (Finset.mem_coe.mp hx))))

end NearCritical.Section10
