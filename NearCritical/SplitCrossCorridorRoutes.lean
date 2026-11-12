module

public import NearCritical.SplitCrossNodeSites
public import NearCritical.Section10SplitLowerCount

/-! A realized tree gives a path in each split corridor. The route uses the
spine, the entry and exterior branch of its own leg, and its far-face edge. -/
@[expose] public section
noncomputable section

namespace NearCritical.SplitCrossDirect

open Section10 SplitTreeNode SimpleGraph
open scoped Classical

/-- A domain containing the realized edge to a node from its parent. -/
def crossingEdgeRegion {d : ℕ} (t : ℕ) : SplitTreeNode (4 * d) → Finset (Vertex d)
  | exterior k => splitCorridor t (splitLegEquiv d k).1 (splitLegEquiv d k).2 t
  | exteriorDummy k => splitBeyond t (splitLegEquiv d k).1 (splitLegEquiv d k).2 t
  | face k => translateSites (farLegBoxCenter t (splitLegEquiv d k).1 (splitLegEquiv d k).2)
      (centeredBox d (legBoxRadius t))
  | _ => typicalCube t 0

theorem crossingEdgeRegion_subset_envelope {d t : ℕ} (ht : 64 ≤ t)
    (v : SplitTreeNode (4 * d)) :
    crossingEdgeRegion t v ⊆ splitEnvelope d t := by
  have hc : typicalCube t (0 : Vertex d) ⊆ splitEnvelope d t :=
    typicalCube_subset_splitEnvelope (by omega)
  cases v with
  | root | spine _ | entry _ | cubeDummy _ => exact hc
  | exterior k => exact Finset.union_subset hc (splitBeyond_subset_splitEnvelope t _ _)
  | exteriorDummy k => exact splitBeyond_subset_splitEnvelope t _ _
  | face k => exact (farLegBox_subset_beyond ht _ _).trans (splitBeyond_subset_splitEnvelope t _ _)

private theorem spine_reachable_in_cube {d t : ℕ} (hL : 2 ≤ 4 * d)
    (ω : Configuration d) (b : SplitTreeNode (4 * d) → Vertex d)
    (hpath : ∀ k : Fin (4 * d - 1), (restrictedGraph ω (typicalCube t (0 : Vertex d) : Set (Vertex d))).Reachable
      (b (parent hL (spine k))) (b (spine k))) (k : Fin (4 * d - 1)) :
    (restrictedGraph ω (typicalCube t (0 : Vertex d) : Set (Vertex d))).Reachable (b root) (b (spine k)) := by
  have h : ∀ n (j : Fin (4 * d - 1)), j.val = n →
      (restrictedGraph ω (typicalCube t (0 : Vertex d) : Set (Vertex d))).Reachable (b root) (b (spine j)) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro j hj
      by_cases hz : j.val = 0
      · simpa [parent, hz] using hpath j
      · let p : Fin (4 * d - 1) := ⟨j.val - 1, by have := j.isLt; omega⟩
        have hlt : p.val < n := by dsimp [p]; omega
        have hp : parent hL (spine j) = spine p := by simp [parent, hz, p]
        exact (ih p.val hlt p rfl).trans (hp ▸ hpath j)
  exact h k.val k rfl

/-- The realized parent connections, in their actual regions, imply the
paper's all-corridors event. -/
theorem crossAll_of_tree_paths {d t : ℕ} (ht : 64 ≤ t) (hL : 2 ≤ 4 * d)
    (ω : Configuration d) (x : Vertex d) (axis : Fin d)
    (hx : x ∈ centeredBox d ((t - 1) / 32))
    (b : SplitTreeNode (4 * d) → Vertex d)
    (hb : ∀ v, b v ∈ nodeSites t x axis v)
    (hpath : ∀ v, v ≠ root →
      (restrictedGraph ω (crossingEdgeRegion t v : Set (Vertex d))).Reachable
        (b (parent hL v)) (b v)) :
    ω ∈ crossAll t t x := by
  have hroot : b root = x := Finset.mem_singleton.mp (hb root)
  intro i
  let k := (splitLegEquiv d).symm i
  have hk : splitLegEquiv d k = i := (splitLegEquiv d).apply_symm_apply i
  let S := splitCorridor t (splitLegEquiv d k).1 (splitLegEquiv d k).2 t
  have hc : (typicalCube t (0 : Vertex d) : Set (Vertex d)) ⊆ (S : Set (Vertex d)) :=
    fun _ hz => Finset.mem_union_left _ hz
  have hface : (crossingEdgeRegion t (face k) : Set (Vertex d)) ⊆ (S : Set (Vertex d)) :=
    fun _ hz => Finset.mem_union_right _ (farLegBox_subset_beyond ht _ _ hz)
  have hsp (j : Fin (4 * d - 1)) :
      (restrictedGraph ω (typicalCube t (0 : Vertex d) : Set (Vertex d))).Reachable (b root) (b (spine j)) :=
    spine_reachable_in_cube hL ω b (fun j => hpath (spine j) (by simp)) j
  let j : Fin (4 * d - 1) := ⟨min k.val (4 * d - 2), by
    have := min_le_right k.val (4 * d - 2)
    omega⟩
  have he : (restrictedGraph ω (typicalCube t (0 : Vertex d) : Set (Vertex d))).Reachable
      (b (spine j)) (b (entry k)) := hpath (entry k) (by simp)
  have hG : (restrictedGraph ω (S : Set (Vertex d))).Reachable (b root) (b (face k)) :=
    (((hsp j).trans he).mono (restrictedGraph_mono ω hc)).trans
      ((hpath (exterior k) (by simp)).trans
        ((hpath (face k) (by simp)).mono (restrictedGraph_mono ω hface)))
  rw [hroot] at hG
  obtain ⟨w⟩ := hG
  have hw : ∀ z ∈ w.support, z ∈ S :=
    restrictedWalk_support w (hc (root_mem_typicalCube (by omega) hx))
  have htarget := farLegFaceCore_subset_target ht _ _ (hb (face k))
  have hout : ω ∈ crossSplit t (splitLegEquiv d k).1 (splitLegEquiv d k).2 t x := by
    have hle : restrictedGraph ω (S : Set (Vertex d)) ≤ openGraph ω := fun _ _ h => h.1
    refine ⟨b (face k), htarget, w.mapLe hle, ?_⟩
    simpa only [Walk.support_mapLe_eq_support] using hw
  simpa only [hk] using hout

end NearCritical.SplitCrossDirect
