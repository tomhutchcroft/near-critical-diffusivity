module

public import NearCritical.SplitCrossDirectPattern
public import NearCritical.SplitCrossDirectEdgeLower

/-! Tree layouts and the realised event (item C of the direct proof of
`SplitCrossInput`).

* `Port Node Term`: the endpoints of tree edges: the root, the three tips of a
  node, or a terminal.
* `Layout d Node Term`: ambient box `Λ`, root `x`, three arm axes, arm length
  `R`, the list of edges (pairs of ports) and a tube for each edge.
* For node positions `β` and terminal positions `y`: `Layout.pos` (position of
  a port; the tip `j` of node `v` is `rayPt (β v) (ax j) R`), `Layout.Rm`
  (removed vertices: all arms), `Layout.St` (star bonds), `Layout.Uout`
  (outside domain `Λ \ Rm`), `Layout.tedges` (the tube edges in the outside
  domain, tubes intersected with it), and

  `Layout.Real β y := patEv (Rm β) (St β) ∩ distinctLoc (Uout β) (edges)`.

* `Layout.real_prob_ge`:
  `min(p,1-p)^|touchBonds (Rm β)| · (∏ τ_e - errTotal) ≤ P[Real β y]`.
-/
@[expose] public section
noncomputable section
namespace NearCritical.SplitCrossDirect
open MeasureTheory ProbabilityTheory SimpleGraph
open scoped Classical BigOperators

variable {d : ℕ}

/-- Endpoints of tree edges. -/
inductive Port (Node Term : Type) : Type
  | root : Port Node Term
  | tip (v : Node) (j : Fin 3) : Port Node Term
  | term (s : Term) : Port Node Term

/-- A tree layout. -/
structure Layout (d : ℕ) (Node Term : Type) [Fintype Node] where
  Λ : Finset (Vertex d)
  x : Vertex d
  ax : Fin 3 → Fin d
  R : ℕ
  edges : List (Port Node Term × Port Node Term)
  tube : Port Node Term × Port Node Term → Set (Vertex d)

namespace Layout

variable {Node Term : Type} [Fintype Node] (L : Layout d Node Term)

/-- Position of a port. -/
def pos (β : Node → Vertex d) (y : Term → Vertex d) : Port Node Term → Vertex d
  | Port.root => L.x
  | Port.tip v j => rayPt (β v) (L.ax j) L.R
  | Port.term s => y s

/-- Removed vertices: all arms of all nodes. -/
def Rm (β : Node → Vertex d) : Finset (Vertex d) :=
  Finset.univ.biUnion fun v : Node =>
    Finset.univ.biUnion fun j : Fin 3 => arm (β v) (L.ax j) L.R

/-- Star bonds: all arm bonds of all nodes. -/
def St (β : Node → Vertex d) : Finset (Bond d) :=
  Finset.univ.biUnion fun v : Node =>
    Finset.univ.biUnion fun j : Fin 3 => armBonds (β v) (L.ax j) L.R

/-- The outside domain. -/
def Uout (β : Node → Vertex d) : Finset (Vertex d) := L.Λ \ L.Rm β

/-- The tube edges in the outside domain. -/
def tedges (β : Node → Vertex d) (y : Term → Vertex d)
    (hpos : ∀ e ∈ L.edges, L.pos β y e.1 ∈ L.Uout β) : List (TEdge d (L.Uout β)) :=
  L.edges.pmap (fun e he =>
    { T := L.tube e ∩ (L.Uout β : Set (Vertex d))
      hT := Set.inter_subset_right
      a := L.pos β y e.1
      b := L.pos β y e.2
      ha := he }) hpos

/-- The realised event. -/
def Real (β : Node → Vertex d) (y : Term → Vertex d)
    (hpos : ∀ e ∈ L.edges, L.pos β y e.1 ∈ L.Uout β) : Set (Configuration d) :=
  patEv (L.Rm β) (L.St β) ∩ distinctLoc (L.Uout β) ((L.tedges β y hpos).map TEdge.loc)

/-- **Probability of the realised event.** -/
theorem real_prob_ge (p : unitInterval) (β : Node → Vertex d) (y : Term → Vertex d)
    (hpos : ∀ e ∈ L.edges, L.pos β y e.1 ∈ L.Uout β) :
    (min (p : ℝ) (1 - (p : ℝ))) ^ (touchBonds (L.Rm β)).card *
        (((L.tedges β y hpos).map (fun e => e.tau p)).prod - errTotal p (L.tedges β y hpos)) ≤
      (percolation d p).real (L.Real β y hpos) := by
  have hind := pattern_indep p L.Λ (L.Rm β) (L.St β)
    (distinctLoc_dependsOn (L.Uout β) (L.tedges β y hpos))
  have hpat := patEv_prob_ge p (L.Rm β) (L.St β)
  have hdist := distinct_edges_lower p (L.tedges β y hpos)
  have hδ0 : 0 ≤ (min (p : ℝ) (1 - (p : ℝ))) ^ (touchBonds (L.Rm β)).card :=
    pow_nonneg (le_min p.2.1 (by linarith [p.2.2])) _
  unfold Real
  rw [hind]
  rcases le_or_gt (((L.tedges β y hpos).map (fun e => e.tau p)).prod -
      errTotal p (L.tedges β y hpos)) 0 with hneg | hposb
  · exact (mul_nonpos_of_nonneg_of_nonpos hδ0 hneg).trans
      (mul_nonneg measureReal_nonneg measureReal_nonneg)
  · exact mul_le_mul hpat hdist hposb.le measureReal_nonneg

end Layout

end NearCritical.SplitCrossDirect
end
