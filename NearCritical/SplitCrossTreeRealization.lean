module

public import NearCritical.SplitCrossCorridorStars
public import NearCritical.SplitCrossDirectIndep

/-! The realized event pairs the prescribed branch stars with distinct
outside clusters. Each tube connection is then joined to its two node sites. -/
@[expose] public section
noncomputable section

namespace NearCritical.SplitCrossDirect

open Section10 SplitTreeNode MeasureTheory
open scoped Classical

def crossingOutside {d : ℕ} (hd : 3 ≤ d) (t : ℕ)
    (b : SplitTreeNode (4 * d) → Vertex d) (R r : ℕ) : Finset (Vertex d) :=
  splitEnvelope d t \ treeMoatVertices (crossingBranches (4 * d)) b (branchAxes hd) R r

def crossingTip {d L : ℕ} (b : SplitTreeNode L → Vertex d) (v : SplitTreeNode L)
    (i : Fin d) (n : ℕ) : Vertex d :=
  if v ∈ crossingBranches L then starTip (b v) i n else b v

abbrev CrossingEdgeIndex (d : ℕ) := {v : SplitTreeNode (4 * d) // v ≠ root}

def crossingEdgeList {d : ℕ} {U : Finset (Vertex d)}
    (E : CrossingEdgeIndex d → TEdge d U) : List (TEdge d U) :=
  ((Finset.univ.erase (root : SplitTreeNode (4 * d))).attach.toList).map
    (fun v => E ⟨v.val, (Finset.mem_erase.mp v.property).1⟩)

theorem crossingEdge_mem_list {d : ℕ} {U : Finset (Vertex d)}
    (E : CrossingEdgeIndex d → TEdge d U) (v : CrossingEdgeIndex d) :
    E v ∈ crossingEdgeList E := by
  have hv : v.val ∈ Finset.univ.erase root := Finset.mem_erase.mpr
    ⟨v.property, Finset.mem_univ _⟩
  exact List.mem_map.mpr ⟨⟨v.val, hv⟩, by simp, by cases v; rfl⟩

def crossingRealized {d : ℕ} (hd : 3 ≤ d) (t : ℕ)
    (b : SplitTreeNode (4 * d) → Vertex d) (R r : ℕ)
    (E : CrossingEdgeIndex d → TEdge d (crossingOutside hd t b R r)) : Set (Configuration d) :=
  treeBranchPattern (crossingBranches (4 * d)) b (branchAxes hd) R r ∩
    distinctLoc (crossingOutside hd t b R r) ((crossingEdgeList E).map TEdge.loc)

private theorem reachable_crossingTip {d : ℕ} (hd : 3 ≤ d) (R r : ℕ)
    (b : SplitTreeNode (4 * d) → Vertex d)
    (hsep : ∀ v ∈ crossingBranches (4 * d), ∀ w ∈ crossingBranches (4 * d),
      v ≠ w → 2 * ((R + r + 1 : ℕ) : ℝ) < dist (b v) (b w))
    {ω : Configuration d}
    (hω : ω ∈ treeBranchPattern (crossingBranches (4 * d)) b (branchAxes hd) R r)
    (D : Set (Vertex d)) (v : SplitTreeNode (4 * d)) {i : Fin d} (hi : i ∈ branchAxes hd)
    (hD : v ∈ crossingBranches (4 * d) →
      (translateSites (b v) (centeredBox d (R + r)) : Set (Vertex d)) ⊆ D) :
    (restrictedGraph ω D).Reachable (b v) (crossingTip b v i (R + r)) := by
  by_cases hv : v ∈ crossingBranches (4 * d)
  · rw [crossingTip, if_pos hv]
    exact branchPattern_reachable
      (treeBranchPattern_local _ b _ R r hsep hω hv) D (hD hv) i hi
  · simp [crossingTip, hv]

theorem crossingRealized_subset_crossAll {d t : ℕ} (ht : 64 ≤ t) (hd : 3 ≤ d) (hL : 2 ≤ 4 * d)
    (x : Vertex d) (axis : Fin d) (hx : x ∈ centeredBox d ((t - 1) / 32))
    (b : SplitTreeNode (4 * d) → Vertex d) (hb : ∀ v, b v ∈ nodeSites t x axis v)
    (R r : ℕ) (hts : 512 * (4 * d - 1 + 1) * (R + r) ≤ t) (htl : 2048 * (R + r) ≤ t)
    (hsep : ∀ v ∈ crossingBranches (4 * d), ∀ w ∈ crossingBranches (4 * d),
      v ≠ w → 2 * ((R + r + 1 : ℕ) : ℝ) < dist (b v) (b w))
    (E : CrossingEdgeIndex d → TEdge d (crossingOutside hd t b R r))
    (hstart : ∀ v, (E v).a =
      crossingTip b (parent hL v.val) (childAxis hd (childSlot v.val)) (R + r))
    (hfinish : ∀ v, (E v).b = crossingTip b v.val (parentAxis hd) (R + r))
    (hT : ∀ v, (E v).T ⊆ (crossingEdgeRegion t v.val : Set (Vertex d))) :
    crossingRealized hd t b R r E ⊆ crossAll t t x := by
  intro ω hω
  apply crossAll_of_tree_paths ht hL ω x axis hx b hb
  intro v hv
  let j : CrossingEdgeIndex d := ⟨v, hv⟩
  let D := (crossingEdgeRegion t v : Set (Vertex d))
  have hleft : (restrictedGraph ω D).Reachable (b (parent hL v)) (E j).a := by
    rw [hstart j]
    apply reachable_crossingTip hd R r b hsep hω.1 D _ (childAxis_mem_branchAxes hd _)
    intro hp z hz
    exact branchBox_subset_outgoing_region ht hL axis v
      (branchBox_offset_subset hts htl x axis _ hp (hb _) hz)
  have hright : (restrictedGraph ω D).Reachable (b v) (E j).b := by
    rw [hfinish j]
    apply reachable_crossingTip hd R r b hsep hω.1 D _ (parentAxis_mem_branchAxes hd)
    intro hp z hz
    exact branchBox_subset_incoming_region ht axis v
      (branchBox_offset_subset hts htl x axis _ hp (hb _) hz)
  have he := hω.2.1 ((E j).loc) (List.mem_map.mpr ⟨E j, crossingEdge_mem_list E j, rfl⟩)
  change ω ∈ connectionToSetEvent (E j).T (E j).a {(E j).b} at he
  obtain ⟨_, y, hy, _, hyconn⟩ := he
  rw [Set.mem_singleton_iff.mp hy] at hyconn
  exact hleft.trans ((hyconn.mono (restrictedGraph_mono ω (hT j))).trans hright.symm)

theorem crossingRealized_probability_lower {d : ℕ} (p : unitInterval) (hd : 3 ≤ d) (t : ℕ)
    (b : SplitTreeNode (4 * d) → Vertex d) (R r : ℕ)
    (E : CrossingEdgeIndex d → TEdge d (crossingOutside hd t b R r)) :
    (min (p : ℝ) (1 - (p : ℝ))) ^
        ((crossingBranches (4 * d)).card * ((3 * (R + r) + 3 * (2 * (r - 1) + 1) ^ d) * (2 * d))) *
        (((crossingEdgeList E).map (fun e => e.tau p)).prod - errTotal p (crossingEdgeList E)) ≤
      (percolation d p).real (crossingRealized hd t b R r E) := by
  let D := distinctLoc (crossingOutside hd t b R r) ((crossingEdgeList E).map TEdge.loc)
  let c := (min (p : ℝ) (1 - (p : ℝ))) ^
        ((crossingBranches (4 * d)).card * ((3 * (R + r) + 3 * (2 * (r - 1) + 1) ^ d) * (2 * d)))
  have hc : 0 ≤ c := pow_nonneg (le_min p.2.1 (sub_nonneg.mpr p.2.2)) _
  have hdep := (distinctLoc_dependsOn (crossingOutside hd t b R r) (crossingEdgeList E)).eq_preimage
  change D = _ at hdep
  have hpat : c * (percolation d p).real D ≤
      (percolation d p).real (crossingRealized hd t b R r E) := by
    change c * (percolation d p).real D ≤
      (percolation d p).real (treeBranchPattern (crossingBranches (4 * d)) b (branchAxes hd) R r ∩ D)
    rw [hdep]
    simpa only [c, crossingOutside, branchAxes_card] using
      treeBranchPattern_with_outside_lower p (crossingBranches (4 * d)) b (branchAxes hd)
        R r (splitEnvelope d t) _
  exact (mul_le_mul_of_nonneg_left (distinct_edges_lower p (crossingEdgeList E)) hc).trans hpat

end NearCritical.SplitCrossDirect
