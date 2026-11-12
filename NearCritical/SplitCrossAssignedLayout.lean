module

public import NearCritical.SplitCrossConcreteRelativeOverlap
public import NearCritical.SplitCrossTubeAssignments

/-! Use the same edge ordering for the concrete layout and the independently
summed tube lists. The finite-energy factor is uniform in all placements. -/
@[expose] public section
noncomputable section

namespace NearCritical.SplitCrossDirect

open SplitTreeNode MeasureTheory
open scoped Classical BigOperators

def crossingEdgeIndices (d : ℕ) : List (CrossingEdgeIndex d) :=
  ((Finset.univ.erase (root : SplitTreeNode (4 * d))).attach.toList).map
    (fun v => ⟨v.val, (Finset.mem_erase.mp v.property).1⟩)

theorem crossingEdgeIndices_nodup (d : ℕ) : (crossingEdgeIndices d).Nodup := by
  unfold crossingEdgeIndices
  refine List.Nodup.map ?_ (Finset.nodup_toList _)
  intro u v h
  exact Subtype.ext (congrArg (fun w : CrossingEdgeIndex d => w.val) h)

theorem mem_crossingEdgeIndices {d : ℕ} (v : CrossingEdgeIndex d) : v ∈ crossingEdgeIndices d := by
  have hv : v.val ∈ Finset.univ.erase root := by simp [v.property]
  exact List.mem_map.mpr ⟨⟨v.val, hv⟩, by simp, by cases v; rfl⟩

theorem concreteCrossingLayout_edges_eq_map {d : ℕ} (hd3 : 3 ≤ d) (hL : 2 ≤ 4 * d)
    (t : ℕ) (x : Vertex d) (R : ℕ) :
    (concreteCrossingLayout hd3 hL t x R).edges =
      (crossingEdgeIndices d).map (fun v => crossingPortEdge hL v.val) := by
  simp only [concreteCrossingLayout, crossingEdgeIndices, List.map_map, Function.comp_def]

private def tubeData {d : ℕ} {U : Finset (Vertex d)} (e : TEdge d U) :
    Set (Vertex d) × Vertex d × Vertex d := (e.T, e.a, e.b)

private theorem tubeData_injective {d : ℕ} {U : Finset (Vertex d)} :
    Function.Injective (tubeData (U := U)) := by
  rintro ⟨T, hT, a, b, ha⟩ ⟨S, hS, c, e, hc⟩ h
  change (T, a, b) = (S, c, e) at h
  obtain ⟨h₁, h₂⟩ := Prod.mk.inj h
  obtain ⟨h₃, h₄⟩ := Prod.mk.inj h₂
  subst S
  subst c
  subst e
  rfl

private theorem distinctLoc_eq_of_tubeData {d : ℕ} {U V : Finset (Vertex d)}
    (hUV : U = V) (es : List (TEdge d U)) (fs : List (TEdge d V))
    (h : es.map tubeData = fs.map tubeData) :
    distinctLoc U (es.map TEdge.loc) = distinctLoc V (fs.map TEdge.loc) := by
  subst V
  rw [(List.map_injective_iff.mpr tubeData_injective) h]

private theorem tedges_tubeData {d : ℕ} {Node Term : Type} [Fintype Node]
    (L : Layout d Node Term) (β : Node → Vertex d) (y : Term → Vertex d)
    (hpos : ∀ e ∈ L.edges, L.pos β y e.1 ∈ L.Uout β) :
    (L.tedges β y hpos).map tubeData =
      L.edges.map (fun e => (L.tube e ∩ (L.Uout β : Set (Vertex d)), L.pos β y e.1, L.pos β y e.2)) := by
  unfold Layout.tedges
  rw [List.map_pmap]
  simp only [tubeData, List.pmap_eq_map]

/-- The concrete layout and a tube-choice list describe the same event
when their endpoints agree in the shared outside domain. -/
theorem concreteCrossingLayout_distinctLoc_eq {d : ℕ} (hd3 : 3 ≤ d) (hL : 2 ≤ 4 * d)
    (t : ℕ) (x : Vertex d) (R : ℕ) (b : SplitTreeNode (4 * d) → Vertex d)
    (β : CrossingBranch (4 * d) → Vertex d) (y : CrossingTerminal (4 * d) → Vertex d)
    (f : CrossingEdgeIndex d → Vertex d) :
    let L := concreteCrossingLayout hd3 hL t x R
    let P := L.pos (fun v => b v.val) (fun v => b v.val)
    let U := crossingOutside hd3 t b R 1
    ∀ (hpos : ∀ e ∈ L.edges, L.pos β y e.1 ∈ L.Uout β)
      (hstart : ∀ v : CrossingEdgeIndex d, P (crossingPortEdge hL v.val).1 ∈ U),
      L.Uout β = U →
      (∀ v : CrossingEdgeIndex d, L.pos β y (crossingPortEdge hL v.val).1 = P (crossingPortEdge hL v.val).1) →
      (∀ v : CrossingEdgeIndex d, L.pos β y (crossingPortEdge hL v.val).2 = f v) →
      distinctLoc (L.Uout β) ((L.tedges β y hpos).map TEdge.loc) =
        distinctLoc U ((crossingEdgeIndices d).map (fun v =>
          (concreteTubeChoice hd3 hL t x R b v (hstart v) (f v)).loc)) := by
  intro L P U hpos hstart hU hs hf
  let E := fun v : CrossingEdgeIndex d => concreteTubeChoice hd3 hL t x R b v (hstart v) (f v)
  have hdata : (L.tedges β y hpos).map tubeData =
      ((crossingEdgeIndices d).map E).map tubeData := by
    rw [tedges_tubeData, List.map_map]
    have he : L.edges = (crossingEdgeIndices d).map (fun v => crossingPortEdge hL v.val) :=
      concreteCrossingLayout_edges_eq_map hd3 hL t x R
    rw [he, List.map_map]
    apply List.map_congr_left
    intro v _
    let e := crossingPortEdge hL v.val
    change ((crossingEdgeRegion t (crossingPortNode e.2) : Set (Vertex d)) ∩
        (L.Uout β : Set (Vertex d)), L.pos β y e.1, L.pos β y e.2) =
      ((crossingEdgeRegion t v.val : Set (Vertex d)) ∩ (U : Set (Vertex d)), P e.1, f v)
    rw [show crossingPortNode e.2 = v.val from crossingPortNode_edge_snd hL v.val, hU, hs v, hf v]
  simpa only [List.map_map, Function.comp_def, E] using
    distinctLoc_eq_of_tubeData hU _ _ hdata

def crossingPatternFactor (d : ℕ) (R : ℕ) (p : unitInterval) : ℝ :=
  (min (p : ℝ) (1 - (p : ℝ))) ^
    ((crossingBranches (4 * d)).card * ((3 * (R + 1) + 3 * (2 * (1 - 1) + 1) ^ d) * (2 * d)))

theorem crossingPatternFactor_pos (d R : ℕ) {p : unitInterval}
    (hp : 0 < (p : ℝ)) (hp' : (p : ℝ) < 1) : 0 < crossingPatternFactor d R p :=
  pow_pos (lt_min hp (sub_pos.mpr hp')) _

theorem concreteCrossingLayout_real_ge_distinct {d : ℕ} (p : unitInterval)
    (hd3 : 3 ≤ d) (hL : 2 ≤ 4 * d) (t : ℕ) (x : Vertex d) (R : ℕ)
    (b : SplitTreeNode (4 * d) → Vertex d) (y : CrossingTerminal (4 * d) → Vertex d) :
    let L := concreteCrossingLayout hd3 hL t x R
    let β := fun v : CrossingBranch (4 * d) => b v.val
    ∀ hpos : ∀ e ∈ L.edges, L.pos β y e.1 ∈ L.Uout β,
    crossingPatternFactor d R p *
      (percolation d p).real (distinctLoc (L.Uout β) ((L.tedges β y hpos).map TEdge.loc)) ≤
      (percolation d p).real (L.Real β y hpos) := by
  intro L β hpos
  have hpat : crossingPatternFactor d R p ≤
      (percolation d p).real (patEv (L.Rm β) (L.St β)) := by
    rw [concreteCrossingLayout_patEv]
    have h := treeBranchPattern_with_outside_lower p (crossingBranches (4 * d)) b
      (branchAxes hd3) R 1 (splitEnvelope d t) Set.univ
    simpa [crossingPatternFactor, branchAxes_card] using h
  unfold Layout.Real
  have hE : DependsOn (distinctLoc (L.Uout β) ((L.tedges β y hpos).map TEdge.loc))
      (internalBondSet (L.Λ \ L.Rm β)) := distinctLoc_dependsOn _ _
  rw [pattern_indep p L.Λ (L.Rm β) (L.St β) hE]
  exact mul_le_mul_of_nonneg_right hpat measureReal_nonneg

end NearCritical.SplitCrossDirect
