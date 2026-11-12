module

public import NearCritical.SplitCrossFacePlacement
public import NearCritical.SplitCrossDirectMultiplicity
public import NearCritical.SplitCrossConcreteOvercount
public import NearCritical.SplitCrossEventsMeasurable

/-! Sum over branch and terminal placements. A fixed tuple of terminals
allows only a bounded number of realized branch placements. -/
@[expose] public section
noncomputable section

namespace NearCritical.SplitCrossDirect

open SplitTreeNode MeasureTheory
open scoped Classical BigOperators

abbrev InteriorIndex (d : ℕ) := Fin (4 * d) × Bool

def interiorNode {d : ℕ} (i : InteriorIndex d) : SplitTreeNode (4 * d) :=
  if i.2 then exteriorDummy i.1 else cubeDummy i.1

def branchPlacements {d : ℕ} (t : ℕ) (x : Vertex d) (axis : Fin d) :
    Finset (CrossingBranch (4 * d) → Vertex d) :=
  Fintype.piFinset fun v => nodeSites t x axis v.val

def interiorPlacements {d : ℕ} (t : ℕ) (x : Vertex d) (axis : Fin d) :
    Finset (InteriorIndex d → Vertex d) :=
  Fintype.piFinset fun i => nodeSites t x axis (interiorNode i)

def facePlacements {d : ℕ} (t : ℕ) (x : Vertex d) (axis : Fin d) :
    Finset (Fin (4 * d) → Vertex d) :=
  Fintype.piFinset fun k => nodeSites t x axis (face k)

def terminalPlacement {d : ℕ} (w : InteriorIndex d → Vertex d) (f : Fin (4 * d) → Vertex d)
    (v : CrossingTerminal (4 * d)) : Vertex d :=
  match v.val with
  | cubeDummy k => w (k, false)
  | exteriorDummy k => w (k, true)
  | face k => f k
  | _ => 0

private def fullPlacement {d : ℕ} (x : Vertex d) (β : CrossingBranch (4 * d) → Vertex d)
    (w : InteriorIndex d → Vertex d) (f : Fin (4 * d) → Vertex d) :
    SplitTreeNode (4 * d) → Vertex d
  | root => x
  | spine k => β ⟨spine k, rfl⟩
  | entry k => β ⟨entry k, rfl⟩
  | exterior k => β ⟨exterior k, rfl⟩
  | cubeDummy k => w (k, false)
  | exteriorDummy k => w (k, true)
  | face k => f k

private theorem fullPlacement_branch {d : ℕ} (x : Vertex d) (β : CrossingBranch (4 * d) → Vertex d)
    (w : InteriorIndex d → Vertex d) (f : Fin (4 * d) → Vertex d) (v : CrossingBranch (4 * d)) :
    fullPlacement x β w f v.val = β v := by
  obtain ⟨v, hv⟩ := v
  cases v <;> first | rfl | cases hv

private theorem fullPlacement_terminal {d : ℕ} (x : Vertex d) (β : CrossingBranch (4 * d) → Vertex d)
    (w : InteriorIndex d → Vertex d) (f : Fin (4 * d) → Vertex d) (v : CrossingTerminal (4 * d)) :
    fullPlacement x β w f v.val = terminalPlacement w f v := by
  obtain ⟨v, hv⟩ := v
  cases v <;> first | rfl | cases hv

private theorem fullPlacement_mem {d t : ℕ} {x : Vertex d} {axis : Fin d}
    {β : CrossingBranch (4 * d) → Vertex d} (hβ : β ∈ branchPlacements t x axis)
    {w : InteriorIndex d → Vertex d} (hw : w ∈ interiorPlacements t x axis)
    {f : Fin (4 * d) → Vertex d} (hf : f ∈ facePlacements t x axis)
    (v : SplitTreeNode (4 * d)) : fullPlacement x β w f v ∈ nodeSites t x axis v := by
  have hβ' := Fintype.mem_piFinset.mp hβ
  have hw' := Fintype.mem_piFinset.mp hw
  have hf' := Fintype.mem_piFinset.mp hf
  cases v with
  | root => simp [fullPlacement, nodeSites]
  | spine k => exact hβ' ⟨spine k, rfl⟩
  | entry k => exact hβ' ⟨entry k, rfl⟩
  | exterior k => exact hβ' ⟨exterior k, rfl⟩
  | cubeDummy k => exact hw' (k, false)
  | exteriorDummy k => exact hw' (k, true)
  | face k => exact hf' k

/-- The event counted for a fixed tuple of terminals. -/
def crossingTerminalEvent {d : ℕ} (t : ℕ) (x : Vertex d)
    (y : CrossingTerminal (4 * d) → Vertex d) : Set (Configuration d) :=
  Section10.crossAll t t x ∩
    ⋂ v, {θ | (restrictedGraph θ (splitEnvelope d t : Set (Vertex d))).Reachable x (y v)}

theorem measurableSet_crossingTerminalEvent {d : ℕ} (t : ℕ) (x : Vertex d)
    (y : CrossingTerminal (4 * d) → Vertex d) : MeasurableSet (crossingTerminalEvent t x y) :=
  (Section10.measurableSet_crossAll t t x).inter
    (MeasurableSet.iInter fun v =>
      measurableSet_graphReachable (fun θ => restrictedGraph θ (splitEnvelope d t : Set (Vertex d)))
        (measurableSet_restricted_adj _) x (y v))

def crossingPlacementMultiplicity (d R : ℕ) : ℕ :=
  ((2 * (2 * (R + 1)) + 1) ^ d) ^ Fintype.card (CrossingBranch (4 * d))

theorem crossingPlacementMultiplicity_pos (d R : ℕ) : 0 < crossingPlacementMultiplicity d R := by
  unfold crossingPlacementMultiplicity
  positivity

/-- Transfer the sum of realization probabilities at fixed terminals to
the corresponding counted crossing event. -/
theorem sum_branch_realEvent_le {d t : ℕ} (ht : 4096 ≤ t) (hd3 : 3 ≤ d)
    (hL : 2 ≤ 4 * d) (x : Vertex d) (hx : x ∈ centeredBox d ((t - 1) / 32)) (axis : Fin d)
    (R : ℕ) (hts : 512 * (4 * d - 1 + 1) * (R + 1) ≤ t) (htl : 2048 * (R + 1) ≤ t)
    (hgap : 2 * ((R + 1 : ℕ) : ℝ) < (spineRadius (4 * d - 1) t : ℝ))
    (w : InteriorIndex d → Vertex d) (hw : w ∈ interiorPlacements t x axis)
    (f : Fin (4 * d) → Vertex d) (hf : f ∈ facePlacements t x axis) :
    let μ := percolation d (criticalPoint d)
    let L := concreteCrossingLayout hd3 hL t x R
    let y := terminalPlacement w f
    (∑ β ∈ branchPlacements t x axis, μ.real (L.realEvent β y)) ≤
      (crossingPlacementMultiplicity d R : ℝ) * μ.real (crossingTerminalEvent t x y) := by
  intro μ L y
  have hβy (β : CrossingBranch (4 * d) → Vertex d) :
      (fun v => fullPlacement x β w f v.val) = β ∧
      (fun v => fullPlacement x β w f v.val) = y :=
    ⟨funext (fullPlacement_branch x β w f), funext (fullPlacement_terminal x β w f)⟩
  apply sum_measureReal_le_mul_of_multiplicity μ _ (fun β => L.realEvent β y) _
    (fun β _ => L.measurableSet_realEvent β y) (measurableSet_crossingTerminalEvent t x y)
  · intro β hβ θ hθ
    have he := hβy β
    rw [← he.1, ← he.2] at hθ
    obtain ⟨hpos, hreal⟩ := hθ
    obtain ⟨hall, hterm⟩ := concreteCrossingLayout_real_paths (by omega : 64 ≤ t) hd3 hL x hx axis R hts htl
      (fullPlacement x β w f) (fullPlacement_mem hβ hw hf) (hpos := hpos) hreal
    refine ⟨hall, Set.mem_iInter.mpr (fun v => ?_)⟩
    rw [← congrFun he.2 v]
    exact hterm v
  · intro θ
    have hm := concreteCrossingLayout_real_multiplicity ht hd3 hL x hx axis R hts htl hgap y θ
      (branchPlacements t x axis)
      (fun β hβ => ⟨fullPlacement x β w f, fullPlacement_mem hβ hw hf, (hβy β).1⟩)
    dsimp only at hm
    unfold crossingPlacementMultiplicity
    convert hm using 2
    ext β
    simp only [Finset.mem_filter, Layout.realEvent, Set.mem_setOf_eq]
    rfl


/-- Sum the first moment over branches and interior terminals, using the
fixed-terminal multiplicity estimate after interchanging the finite sums. -/
theorem crossing_placement_moment_lower {d t : ℕ} (ht : 4096 ≤ t) (hd3 : 3 ≤ d)
    (hL : 2 ≤ 4 * d) (x : Vertex d) (hx : x ∈ centeredBox d ((t - 1) / 32)) (axis : Fin d)
    (R : ℕ) (hts : 512 * (4 * d - 1 + 1) * (R + 1) ≤ t) (htl : 2048 * (R + 1) ≤ t)
    (hgap : 2 * ((R + 1 : ℕ) : ℝ) < (spineRadius (4 * d - 1) t : ℝ))
    (c : ℝ)
    (hpoint : ∀ (b : SplitTreeNode (4 * d) → Vertex d), (∀ v, b v ∈ nodeSites t x axis v) →
      let L := concreteCrossingLayout hd3 hL t x R
      let P := L.pos (fun v => b v.val) (fun v => b v.val)
      let Y := fun v : CrossingEdgeIndex d => crossingEdgeChoices t v.val (P (crossingPortEdge hL v.val).2)
      c ≤ ∑ f ∈ Fintype.piFinset Y, (percolation d (criticalPoint d)).real
        (L.realEvent (fun v => (faceAssignedSites b f) v.val) (fun v => (faceAssignedSites b f) v.val))) :
    let μ := percolation d (criticalPoint d)
    ((branchPlacements t x axis).card : ℝ) * ((interiorPlacements t x axis).card : ℝ) * c ≤
      (crossingPlacementMultiplicity d R : ℝ) *
        ∑ w ∈ interiorPlacements t x axis, ∑ f ∈ facePlacements t x axis,
          μ.real (crossingTerminalEvent t x (terminalPlacement w f)) := by
  intro μ
  let L := concreteCrossingLayout hd3 hL t x R
  let S := branchPlacements t x axis
  let W := interiorPlacements t x axis
  let F := facePlacements t x axis
  let f₀ (k : Fin (4 * d)) := Classical.choose (nodeSites_nonempty t x axis (face k))
  have hf₀ : f₀ ∈ F := Fintype.mem_piFinset.mpr fun k =>
    Classical.choose_spec (nodeSites_nonempty t x axis (face k))
  have hfixed (β : CrossingBranch (4 * d) → Vertex d) (hβ : β ∈ S)
      (w : InteriorIndex d → Vertex d) (hw : w ∈ W) :
      c ≤ ∑ f ∈ F, μ.real (L.realEvent β (terminalPlacement w f)) := by
    let b := fullPlacement x β w f₀
    let P := L.pos (fun v => b v.val) (fun v => b v.val)
    let z := fun v : CrossingEdgeIndex d => P (crossingPortEdge hL v.val).2
    let H := fun b' : SplitTreeNode (4 * d) → Vertex d =>
      μ.real (L.realEvent (fun v => b' v.val) (fun v => b' v.val))
    have h := hpoint b (fullPlacement_mem hβ hw hf₀)
    change c ≤ ∑ f ∈ Fintype.piFinset (fun v => crossingEdgeChoices t v.val (z v)),
      H (faceAssignedSites b f) at h
    refine h.trans_eq ((sum_crossingEdgeChoices_eq_face x axis z b H).trans ?_)
    apply Finset.sum_congr rfl
    intro f _
    have hb : replaceFaceSites b f = fullPlacement x β w f := by
      funext v
      cases v <;> rfl
    dsimp only [H]
    rw [hb, funext (fullPlacement_branch x β w f), funext (fullPlacement_terminal x β w f)]
  calc
    _ = ∑ _β ∈ S, ∑ _w ∈ W, c := by simp [nsmul_eq_mul, mul_assoc, S, W]
    _ ≤ ∑ β ∈ S, ∑ w ∈ W, ∑ f ∈ F, μ.real (L.realEvent β (terminalPlacement w f)) :=
      Finset.sum_le_sum fun β hβ => Finset.sum_le_sum fun w hw => hfixed β hβ w hw
    _ = ∑ w ∈ W, ∑ f ∈ F, ∑ β ∈ S, μ.real (L.realEvent β (terminalPlacement w f)) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro w _
      exact Finset.sum_comm
    _ ≤ _ := by
      simp only [Finset.mul_sum]
      exact Finset.sum_le_sum fun w hw => Finset.sum_le_sum fun f hf =>
        sum_branch_realEvent_le ht hd3 hL x hx axis R hts htl hgap w hw f hf

end NearCritical.SplitCrossDirect
