module

public import NearCritical.Section10AvoidArm
public import NearCritical.Section10ClusterConditionedCount

/-! The lower-count bound of the `delta n^2` argument, assembled.

* `exists_avoidArm_on_face`: for an open walk from `x` in `Q` to a vertex
  outside `Q`, staying in `W`, the last-visit point of the cluster lies on any
  set `F` containing all points of `Q` with a lattice neighbour in `W \ Q`, and
  carries the avoiding arm (for `r` below its distance to the endpoint).
* `crossing_small_count_le`: hence

  `P[ x crosses to Tgt inside W  and  |C_Q(x) ∩ F| <= m ]
      <= m * alpha * P[ C_Q(x) ∩ F nonempty ]`,

  where `alpha` bounds the ordinary one-arm probability to distance `r`. This
  is the source's `P(x <-> boundary) * delta n^2 * P(0 <-> boundary of
  Lambda_{7n/8})` with `m = delta n^2`, for an abstract corridor `W`, exit
  patch `F` and target `Tgt`.
-/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open MeasureTheory
open scoped Classical

theorem exists_avoidArm_on_face {d : ℕ} {ω : Configuration d} (W Q F : Finset (Vertex d))
    {x y₀ : Vertex d} (hx : x ∈ Q) (w : (openGraph ω).Walk x y₀)
    (hW : ∀ z ∈ w.support, z ∈ W) (hy₀ : y₀ ∉ Q)
    (hWF : ∀ y ∈ Q, ∀ u ∈ W, u ∉ Q → (openGraph (fun _ : Bond d => true)).Adj y u → y ∈ F)
    (r : ℝ) (hfar : ∀ y ∈ F, r < dist y y₀) :
    ∃ y ∈ finiteBoxCluster ω Q x ∩ F, ω ∈ avoidArm W Q (finiteBoxCluster ω Q x) y r := by
  obtain ⟨y, hy, q, hsup, hlast, hav⟩ := cluster_last_visit_arm Q hx w
  have hyQ : y ∈ Q := ((mem_finiteBoxCluster ω Q x y).mp hy).1
  have hne : y ≠ y₀ := fun h => hy₀ (h ▸ hyQ)
  obtain ⟨u, hadj, q', rfl⟩ := q.exists_eq_cons_of_ne hne
  have huS : u ∈ (SimpleGraph.Walk.cons hadj q').support := by simp
  have huC : u ∉ finiteBoxCluster ω Q x := by
    intro huC
    exact hadj.ne (hlast u huS huC).symm
  have huQ : u ∉ Q := by
    intro huQ
    apply huC
    refine (mem_finiteBoxCluster ω Q x u).mpr ⟨huQ, ?_⟩
    have hradj : (restrictedGraph ω (Q : Set (Vertex d))).Adj y u := ⟨hadj, hyQ, huQ⟩
    exact ((mem_finiteBoxCluster ω Q x y).mp hy).2.trans hradj.reachable
  have hfull : (openGraph (fun _ : Bond d => true)).Adj y u := by
    obtain ⟨e, _, hends⟩ := hadj
    exact ⟨e, rfl, hends⟩
  have hyF : y ∈ F := hWF y hyQ u (hW u (hsup u huS)) huQ hfull
  refine ⟨y, Finset.mem_inter.mpr ⟨hy, hyF⟩, ?_⟩
  exact ⟨y₀, hfar y hyF, unexplored_reachable_of_avoid W Q _ _
    (fun z hz => hW z (hsup z hz)) hav⟩

/-- **Crossing with few exit points is unlikely.** -/
theorem crossing_small_count_le {d : ℕ} (p : unitInterval) (W Q F Tgt : Finset (Vertex d))
    {x : Vertex d} (hx : x ∈ Q) (hTgtQ : ∀ y₀ ∈ Tgt, y₀ ∉ Q)
    (hWF : ∀ y ∈ Q, ∀ u ∈ W, u ∉ Q → (openGraph (fun _ : Bond d => true)).Adj y u → y ∈ F)
    (r : ℝ) (hfar : ∀ y ∈ F, ∀ y₀ ∈ Tgt, r < dist y y₀) (m : ℕ) {α : ℝ}
    (hα : ∀ y : Vertex d, (percolation d p).real (extrinsicRadiusArmEvent y r) ≤ α) :
    (percolation d p).real
      ({ω | ∃ y₀ ∈ Tgt, ∃ w : (openGraph ω).Walk x y₀, ∀ z ∈ w.support, z ∈ W} ∩
        {ω | (finiteBoxCluster ω Q x ∩ F).card ≤ m}) ≤
      (m : ℝ) * α * (percolation d p).real {ω | (finiteBoxCluster ω Q x ∩ F).Nonempty} := by
  have hbound := cluster_conditioned_count_bound p Q F x hx
    (fun C => sprinklingAvailableBonds W Q C) (fun C => avoidArm_bonds_disjoint W Q C)
    (fun C y => avoidArm W Q C y r) (fun C y => measurableSet_avoidArm W Q C y r)
    (fun C y ω θ h => avoidArm_local W Q C y r ω θ h)
    (fun C y => (avoidArm_prob_le p W Q C y r).trans (hα y)) m
  refine (measureReal_mono (μ := percolation d p) ?_ (measure_ne_top _ _)).trans hbound
  rintro ω ⟨⟨y₀, hy₀, w, hW⟩, hcard⟩
  obtain ⟨y, hy, harm⟩ := exists_avoidArm_on_face W Q F hx w hW (hTgtQ y₀ hy₀) hWF r
    (fun y hyF => hfar y hyF y₀ hy₀)
  exact ⟨hcard, y, hy, harm⟩

end NearCritical.Section10
