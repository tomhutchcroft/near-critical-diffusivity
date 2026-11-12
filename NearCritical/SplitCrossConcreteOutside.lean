module

public import NearCritical.SplitCrossConcreteMoats
public import NearCritical.SplitCrossNodeSeparation
public import NearCritical.SplitCrossDirectCrossing

/-! Root, terminals, and all shifted branch tips lie in the common outside
domain. The initial tip is therefore a valid root for each tube edge. -/
@[expose] public section
noncomputable section

namespace NearCritical.SplitCrossDirect

open SplitTreeNode MeasureTheory
open scoped Classical

theorem crossingTip_mem_outside {d t : ℕ} (ht : 4096 ≤ t)
    (hd : 3 ≤ d) (x : Vertex d) (hx : x ∈ centeredBox d ((t - 1) / 32)) (axis : Fin d)
    (R ρ : ℕ)
    (hts : 512 * (4 * d - 1 + 1) * (R + 1 + ρ) ≤ t) (htl : 2048 * (R + 1 + ρ) ≤ t)
    (hgap : ((R + 1 + ρ : ℕ) : ℝ) + ((R + 1 + 1 : ℕ) : ℝ) <
      (spineRadius (4 * d - 1) t : ℝ))
    (b : SplitTreeNode (4 * d) → Vertex d) (hb : ∀ v, b v ∈ nodeSites t x axis v)
    (v : SplitTreeNode (4 * d)) (i : Fin d) (k : ℕ) (hk : k ≤ ρ) :
    crossingTip b v i (R + 1 + k) ∈ crossingOutside hd t b R 1 := by
  by_cases hv : v ∈ crossingBranches (4 * d)
  · have hsep : ∀ w ∈ crossingBranches (4 * d), v ≠ w →
        ((R + 1 + ρ : ℕ) : ℝ) + ((R + 1 + 1 : ℕ) : ℝ) < dist (b v) (b w) := by
      intro w _ hne
      exact hgap.trans_le (nodeSites_dist_of_ne (by omega) ht hx axis hne (hb v) (hb w))
    have hU (l : ℕ) (hl : l ≤ ρ) : starTip (b v) i (R + 1 + l) ∈ splitEnvelope d t :=
      crossingEdgeRegion_subset_envelope (by omega) v
        (branchBox_subset_incoming_region (by omega) axis v
          (branchBox_offset_subset hts htl x axis v hv (hb v)
            (starTip_mem_box _ _ (by omega))))
    have hray := outwardRay_mem_treeOutside (crossingBranches (4 * d)) b (branchAxes hd)
      R 1 ρ (by decide) hv i hsep (splitEnvelope d t) hU k hk
    rw [← starTip_add] at hray
    simpa [crossingTip, crossingOutside, hv] using hray
  · rw [crossingTip, ite_eq_right hv]
    refine Finset.mem_sdiff.mpr
      ⟨nodeSites_subset_envelope (by omega) hx axis v (hb v), ?_⟩
    intro hm
    obtain ⟨w, hw, hmw⟩ := Finset.mem_biUnion.mp hm
    have hne : v ≠ w := fun h => hv (by simpa only [h] using hw)
    have hd' := nodeSites_dist_of_ne (by omega : 2 ≤ d) ht hx axis hne (hb v) (hb w)
    have hm' := moatVertex_dist_center_le hmw i
    have hnonneg : 0 ≤ ((R + 1 + ρ : ℕ) : ℝ) := by positivity
    linarith

theorem concreteCrossingLayout_start_mem {d t : ℕ} (ht : 4096 ≤ t) (hd : 3 ≤ d)
    (hL : 2 ≤ 4 * d) (x : Vertex d) (hx : x ∈ centeredBox d ((t - 1) / 32)) (axis : Fin d)
    (R : ℕ) (hts : 512 * (4 * d - 1 + 1) * (R + 1) ≤ t) (htl : 2048 * (R + 1) ≤ t)
    (hgap : ((R + 1 : ℕ) : ℝ) + ((R + 1 + 1 : ℕ) : ℝ) < (spineRadius (4 * d - 1) t : ℝ))
    (b : SplitTreeNode (4 * d) → Vertex d) (hb : ∀ v, b v ∈ nodeSites t x axis v)
    (e : CrossingPort (4 * d) × CrossingPort (4 * d))
    (he : e ∈ (concreteCrossingLayout hd hL t x R).edges) :
    (concreteCrossingLayout hd hL t x R).pos
        (fun v => b v.val) (fun v => b v.val) e.1 ∈
      (concreteCrossingLayout hd hL t x R).Uout (fun v => b v.val) := by
  obtain ⟨v, _, rfl⟩ := (mem_concreteCrossingLayout_edges hd hL t x R e).mp he
  rw [concreteCrossingLayout_Uout]
  change (concreteCrossingLayout hd hL t x R).pos (fun v => b v.val) (fun v => b v.val)
    (crossingPortAt (parent hL v) (childPortSlot (childSlot v))) ∈ _
  rw [concreteCrossingLayout_pos hd hL t x R b (Finset.mem_singleton.mp (hb root))]
  exact crossingTip_mem_outside ht hd x hx axis R 0 hts htl hgap b hb _ _ 0 le_rfl

theorem concreteCrossingLayout_real_measurable {d : ℕ} (hd : 3 ≤ d)
    (hL : 2 ≤ 4 * d) (t : ℕ) (x : Vertex d) (R : ℕ)
    (β : CrossingBranch (4 * d) → Vertex d) (y : CrossingTerminal (4 * d) → Vertex d)
    (hpos : ∀ e ∈ (concreteCrossingLayout hd hL t x R).edges,
      (concreteCrossingLayout hd hL t x R).pos β y e.1 ∈
        (concreteCrossingLayout hd hL t x R).Uout β) :
    MeasurableSet ((concreteCrossingLayout hd hL t x R).Real β y hpos) := by
  exact (patEv_dependsOn _ _).measurableSet.inter (distinctLoc_dependsOn _ _).measurableSet

/-- On the concrete layout event the fixed terminals are all connected to
the root in the envelope, with the face paths in their designated corridors. -/
theorem concreteCrossingLayout_real_paths {d t : ℕ} (ht : 64 ≤ t)
    (hd : 3 ≤ d) (hL : 2 ≤ 4 * d)
    (x : Vertex d) (hx : x ∈ centeredBox d ((t - 1) / 32)) (axis : Fin d) (R : ℕ)
    (hts : 512 * (4 * d - 1 + 1) * (R + 1) ≤ t) (htl : 2048 * (R + 1) ≤ t)
    (b : SplitTreeNode (4 * d) → Vertex d) (hb : ∀ v, b v ∈ nodeSites t x axis v)
    {hpos : ∀ e ∈ (concreteCrossingLayout hd hL t x R).edges,
      (concreteCrossingLayout hd hL t x R).pos (fun v => b v.val) (fun v => b v.val) e.1 ∈
        (concreteCrossingLayout hd hL t x R).Uout (fun v => b v.val)}
    {θ : Configuration d}
    (hθ : θ ∈ (concreteCrossingLayout hd hL t x R).Real (fun v => b v.val) (fun v => b v.val) hpos) :
    θ ∈ Section10.crossAll t t x ∧ ∀ v : CrossingTerminal (4 * d),
      (restrictedGraph θ (splitEnvelope d t : Set (Vertex d))).Reachable x (b v.val) := by
  let L := concreteCrossingLayout hd hL t x R
  have hroot : b root = x := Finset.mem_singleton.mp (hb root)
  have hreach (v : SplitTreeNode (4 * d)) (j : Fin 3) (D : Set (Vertex d))
      (hD : v ∈ crossingBranches (4 * d) → (crossingBranchBox t axis v : Set (Vertex d)) ⊆ D) :
      (restrictedGraph θ D).Reachable (b v)
        (L.pos (fun v => b v.val) (fun v => b v.val) (crossingPortAt v j)) := by
    by_cases hv : v ∈ crossingBranches (4 * d)
    · let u : CrossingBranch (4 * d) := ⟨v, (mem_crossingBranches _).mp hv⟩
      change _root_.SimpleGraph.Reachable _ (b u.val)
        (L.pos (fun v => b v.val) (fun v => b v.val) (crossingPortAt u.val j))
      rw [crossingPortAt_branch u]
      change (restrictedGraph θ D).Reachable (b u.val) (rayPt (b u.val) (L.ax j) L.R)
      apply arm_reachable
      · exact fun k hk => L.real_arm_open hθ u j hk
      · intro k hk
        rw [rayPt_eq_starTip]
        exact hD hv (branchBox_offset_subset hts htl x axis v hv (hb v)
          (starTip_mem_box _ _ hk))
    · rw [concreteCrossingLayout_pos hd hL t x R b hroot]
      simp [crossingTip, hv]
  have hpath (v : SplitTreeNode (4 * d)) (hv : v ≠ root) :
      (restrictedGraph θ (crossingEdgeRegion t v : Set (Vertex d))).Reachable
        (b (parent hL v)) (b v) := by
    let e := crossingPortEdge hL v
    have he : e ∈ L.edges := (mem_concreteCrossingLayout_edges hd hL t x R _).mpr ⟨v, hv, rfl⟩
    obtain ⟨_, z, hz, _, hc⟩ := L.real_edge_conn hθ he
    rw [Set.mem_singleton_iff.mp hz] at hc
    have hT : L.tube e ∩ (L.Uout (fun v => b v.val) : Set (Vertex d)) ⊆
        (crossingEdgeRegion t v : Set (Vertex d)) := by
      change (crossingEdgeRegion t (crossingPortNode e.2) : Set (Vertex d)) ∩ _ ⊆ _
      rw [show crossingPortNode e.2 = v from crossingPortNode_edge_snd hL v]
      exact Set.inter_subset_left
    have hl := hreach (parent hL v) (childPortSlot (childSlot v))
      (crossingEdgeRegion t v : Set (Vertex d)) (fun _ _ hz =>
        branchBox_subset_outgoing_region ht hL axis v hz)
    have hr := hreach v 0 (crossingEdgeRegion t v : Set (Vertex d)) (fun _ _ hz =>
      branchBox_subset_incoming_region ht axis v hz)
    exact hl.trans ((hc.mono (restrictedGraph_mono θ hT)).trans hr.symm)
  refine ⟨crossAll_of_tree_paths ht hL θ x axis hx b hb hpath, ?_⟩
  have henv : ∀ n (v : SplitTreeNode (4 * d)), rank v = n →
      (restrictedGraph θ (splitEnvelope d t : Set (Vertex d))).Reachable x (b v) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro v hn
      by_cases hv : v = root
      · subst v
        simp [hroot]
      · have hp : rank (parent hL v) < n := hn ▸ parent_rank_lt hL v hv
        exact (ih _ hp _ rfl).trans ((hpath v hv).mono
          (restrictedGraph_mono θ (Finset.coe_subset.mpr (crossingEdgeRegion_subset_envelope ht v))))
  exact fun v => henv _ v.val rfl

end NearCritical.SplitCrossDirect
