module

public import NearCritical.SplitCrossAssignedLayout

/-! At fixed branch and interior terminal positions, sum the realization
probability over all far terminal positions. -/
@[expose] public section
noncomputable section

namespace NearCritical.SplitCrossDirect

open SplitTreeNode MeasureTheory
open scoped Classical BigOperators

namespace Layout

variable {d : ℕ} {Node Term : Type} [Fintype Node] (L : Layout d Node Term)

def realEvent (β : Node → Vertex d) (y : Term → Vertex d) : Set (Configuration d) :=
  {ω | ∃ hpos : ∀ e ∈ L.edges, L.pos β y e.1 ∈ L.Uout β, ω ∈ L.Real β y hpos}

theorem realEvent_eq (β : Node → Vertex d) (y : Term → Vertex d)
    (hpos : ∀ e ∈ L.edges, L.pos β y e.1 ∈ L.Uout β) :
    L.realEvent β y = L.Real β y hpos := by
  ext ω
  exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨hpos, h⟩⟩

theorem measurableSet_realEvent (β : Node → Vertex d) (y : Term → Vertex d) :
    MeasurableSet (L.realEvent β y) := by
  by_cases h : ∀ e ∈ L.edges, L.pos β y e.1 ∈ L.Uout β
  · rw [L.realEvent_eq β y h]
    exact (patEv_dependsOn _ _).measurableSet.inter (distinctLoc_dependsOn _ _).measurableSet
  · have he : L.realEvent β y = ∅ := by
      ext ω
      constructor
      · rintro ⟨hpos, _⟩
        exact (h hpos).elim
      · intro hω
        exact hω.elim
    rw [he]
    exact MeasurableSet.empty

end Layout

def faceAssignedSites {d : ℕ} (b : SplitTreeNode (4 * d) → Vertex d)
    (f : CrossingEdgeIndex d → Vertex d) : SplitTreeNode (4 * d) → Vertex d
  | face k => f ⟨face k, by simp⟩
  | v => b v

private theorem faceAssignedSites_eq {d : ℕ} (b : SplitTreeNode (4 * d) → Vertex d)
    (f : CrossingEdgeIndex d → Vertex d) (v : SplitTreeNode (4 * d))
    (hv : ∀ k, v ≠ face k) : faceAssignedSites b f v = b v := by
  cases v <;> first | rfl | exact (hv _ rfl).elim

private theorem parent_ne_face {L : ℕ} (hL : 2 ≤ L) (v : SplitTreeNode L) (k : Fin L) :
    parent hL v ≠ face k := by
  cases v with
  | spine j => by_cases hj : j.val = 0 <;> simp [parent, hj]
  | root | entry _ | exterior _ | cubeDummy _ | exteriorDummy _ | face _ => simp [parent]

private theorem faceAssignedSites_branch {d : ℕ} (b : SplitTreeNode (4 * d) → Vertex d)
    (f : CrossingEdgeIndex d → Vertex d) (v : CrossingBranch (4 * d)) :
    faceAssignedSites b f v.val = b v.val := by
  apply faceAssignedSites_eq
  intro k h
  have hv := v.property
  simp [h, isCrossingBranch] at hv

private theorem concrete_assigned_real_ge {d t : ℕ} (hd3 : 3 ≤ d) (hL : 2 ≤ 4 * d)
    (ht : 4096 ≤ t) (x : Vertex d) (hx : x ∈ centeredBox d ((t - 1) / 32))
    (axis : Fin d) (R : ℕ)
    (hts : 512 * (4 * d - 1 + 1) * (R + 1) ≤ t) (htl : 2048 * (R + 1) ≤ t)
    (hgap : ((R + 1 : ℕ) : ℝ) + ((R + 1 + 1 : ℕ) : ℝ) < (spineRadius (4 * d - 1) t : ℝ))
    (b : SplitTreeNode (4 * d) → Vertex d) (hb : ∀ v, b v ∈ nodeSites t x axis v)
    (f : CrossingEdgeIndex d → Vertex d) :
    let L := concreteCrossingLayout hd3 hL t x R
    let P := L.pos (fun v => b v.val) (fun v => b v.val)
    let U := crossingOutside hd3 t b R 1
    ∀ (hstart : ∀ v : CrossingEdgeIndex d, P (crossingPortEdge hL v.val).1 ∈ U),
      (∀ v : CrossingEdgeIndex d, f v ∈ crossingEdgeChoices t v.val (P (crossingPortEdge hL v.val).2)) →
      crossingPatternFactor d R (criticalPoint d) *
        (percolation d (criticalPoint d)).real (distinctLoc U ((crossingEdgeIndices d).map
          (fun v => (concreteTubeChoice hd3 hL t x R b v (hstart v) (f v)).loc))) ≤
        (percolation d (criticalPoint d)).real
          (L.realEvent (fun v => (faceAssignedSites b f) v.val) (fun v => (faceAssignedSites b f) v.val)) := by
  intro L P U hstart hf
  let b' := faceAssignedSites b f
  let P' := L.pos (fun v => b' v.val) (fun v => b' v.val)
  have hb' (v : SplitTreeNode (4 * d)) : b' v ∈ nodeSites t x axis v := by
    cases v with
    | face k => exact hf ⟨face k, by simp⟩
    | root | spine _ | entry _ | exterior _ | cubeDummy _ | exteriorDummy _ => exact hb _
  have hpos := concreteCrossingLayout_start_mem ht hd3 hL x hx axis R hts htl hgap b' hb'
  have hU : L.Uout (fun v => b' v.val) = U := by
    have he : (fun v : CrossingBranch (4 * d) => b' v.val) = fun v => b v.val :=
      funext (faceAssignedSites_branch b f)
    rw [he]
    exact concreteCrossingLayout_Uout hd3 hL t x R b
  have hroot : b root = x := Finset.mem_singleton.mp (hb root)
  have hroot' : b' root = x := Finset.mem_singleton.mp (hb' root)
  have hsrc (v : CrossingEdgeIndex d) :
      P' (crossingPortEdge hL v.val).1 = P (crossingPortEdge hL v.val).1 := by
    change P' (crossingPortAt (parent hL v.val) (childPortSlot (childSlot v.val))) =
      P (crossingPortAt (parent hL v.val) (childPortSlot (childSlot v.val)))
    dsimp only [P', P, L]
    rw [concreteCrossingLayout_pos hd3 hL t x R b' hroot', concreteCrossingLayout_pos hd3 hL t x R b hroot]
    simp only [crossingTip, b', faceAssignedSites_eq b f _ (parent_ne_face hL _)]
  have hdest (v : CrossingEdgeIndex d) : P' (crossingPortEdge hL v.val).2 = f v := by
    change P' (crossingPortAt v.val 0) = f v
    by_cases hv : ∃ k, v.val = face k
    · obtain ⟨k, hk⟩ := hv
      have hv' : v = ⟨face k, by simp⟩ := Subtype.ext hk
      dsimp only [P', L]
      rw [concreteCrossingLayout_pos hd3 hL t x R b' hroot', hv']
      simp [crossingTip, isCrossingBranch, b', faceAssignedSites]
    · have hv' (k : Fin (4 * d)) : v.val ≠ face k := fun h => hv ⟨k, h⟩
      have hf' : f v = P (crossingPortEdge hL v.val).2 := by
        have h := hf v
        cases hc : v.val <;> simp_all [crossingEdgeChoices]
      rw [hf']
      change P' (crossingPortAt v.val 0) = P (crossingPortAt v.val 0)
      dsimp only [P', P, L]
      rw [concreteCrossingLayout_pos hd3 hL t x R b' hroot', concreteCrossingLayout_pos hd3 hL t x R b hroot]
      simp only [crossingTip, b', faceAssignedSites_eq b f _ hv']
  have hD := concreteCrossingLayout_distinctLoc_eq hd3 hL t x R b
    (fun v => b' v.val) (fun v => b' v.val) f hpos hstart hU hsrc hdest
  rw [L.realEvent_eq _ _ hpos, ← hD]
  exact concreteCrossingLayout_real_ge_distinct (criticalPoint d) hd3 hL t x R b' _ hpos

/-- The first moment over all far-face assignments at a fixed placement
of the other nodes, with half of the product surviving the overlap. -/
theorem concrete_face_assignment_moment_lower {d t : ℕ} (hd : 7 ≤ d) (hd3 : 3 ≤ d)
    (hL : 2 ≤ 4 * d) (ht : 4096 ≤ t) {G B q a : ℝ}
    (hG : 0 ≤ G) (green : CriticalSupGreenUpper d G) (hB : 0 ≤ B)
    (hBm : Section10.BoxFaceFirstMoment d B) (hq : 0 < q) (ha : 0 < a)
    (x : Vertex d) (hx : x ∈ centeredBox d ((t - 1) / 32)) (axis : Fin d) (R : ℕ)
    (hts : 512 * (4 * d - 1 + 1) * (R + 1) ≤ t) (htl : 2048 * (R + 1) ≤ t)
    (hout : ((R + 1 : ℕ) : ℝ) + ((R + 1 + 1 : ℕ) : ℝ) < (spineRadius (4 * d - 1) t : ℝ))
    (hgap : 3 * ((R + 1 : ℕ) : ℝ) ≤ (spineRadius (4 * d - 1) t : ℝ))
    (hscale : q * (t : ℝ) + 2 * ((R + 1 : ℕ) : ℝ) ≤ (spineRadius (4 * d - 1) t : ℝ))
    (hhalf : ((crossingEdgeIndices d).length : ℝ)^2 * crossingRelativeOverlap d G B q a R ≤ 1 / 2)
    (b : SplitTreeNode (4 * d) → Vertex d) (hb : ∀ v, b v ∈ nodeSites t x axis v) :
    let L := concreteCrossingLayout hd3 hL t x R
    let P := L.pos (fun v => b v.val) (fun v => b v.val)
    let U := crossingOutside hd3 t b R 1
    ∀ hpos : ∀ v : CrossingEdgeIndex d, P (crossingPortEdge hL v.val).1 ∈ U,
    let Y := fun v : CrossingEdgeIndex d => crossingEdgeChoices t v.val (P (crossingPortEdge hL v.val).2)
    let E := fun v => concreteTubeChoice hd3 hL t x R b v (hpos v)
    (∀ v, ∀ y ∈ Y v, a * (t : ℝ) ^ crossingEdgeExponent d v.val ≤ (E v y).tau (criticalPoint d)) →
    (crossingPatternFactor d R (criticalPoint d) / 2) *
      tubeChoiceProduct (criticalPoint d) Y E (crossingEdgeIndices d) ≤
      ∑ f ∈ Fintype.piFinset Y, (percolation d (criticalPoint d)).real
        (L.realEvent (fun v => (faceAssignedSites b f) v.val) (fun v => (faceAssignedSites b f) v.val)) := by
  intro L P U hpos Y E hpoint
  let l := crossingEdgeIndices d
  have hn : l.Nodup := crossingEdgeIndices_nodup d
  have hrel := concrete_summed_distinct_lower hd hd3 hL ht hG green hB hBm hq ha
    x hx axis R hgap hscale b hb l hn hpos hpoint
  change (1 - (l.length : ℝ)^2 * crossingRelativeOverlap d G B q a R) *
    tubeChoiceProduct (criticalPoint d) Y E l ≤
      sumTubeChoices Y E l (fun es =>
        (percolation d (criticalPoint d)).real (distinctLoc U (es.map TEdge.loc))) at hrel
  rw [sumTubeChoices_eq_piFinset Y E l hn mem_crossingEdgeIndices] at hrel
  let c := crossingPatternFactor d R (criticalPoint d)
  have hc : 0 ≤ c := pow_nonneg (le_min (criticalPoint d).2.1 (sub_nonneg.mpr (criticalPoint d).2.2)) _
  have hp : 0 ≤ tubeChoiceProduct (criticalPoint d) Y E l := tubeChoiceProduct_nonneg _ _ _ _
  change (c / 2) * tubeChoiceProduct (criticalPoint d) Y E l ≤ _
  calc
    _ = c * ((1 / 2) * tubeChoiceProduct (criticalPoint d) Y E l) := by ring
    _ ≤ c * ((1 - (l.length : ℝ)^2 * crossingRelativeOverlap d G B q a R) *
      tubeChoiceProduct (criticalPoint d) Y E l) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (by linarith [hhalf]) hp) hc
    _ ≤ c * ∑ f ∈ Fintype.piFinset Y, (percolation d (criticalPoint d)).real
        (distinctLoc U ((l.map (fun v => E v (f v))).map TEdge.loc)) := mul_le_mul_of_nonneg_left hrel hc
    _ ≤ _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro f hf
      have h := concrete_assigned_real_ge hd3 hL ht x hx axis R hts htl hout b hb f hpos
        (Fintype.mem_piFinset.mp hf)
      simpa only [List.map_map, Function.comp_def] using h

end NearCritical.SplitCrossDirect
