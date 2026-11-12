module

public import NearCritical.Section10LastVisit
public import NearCritical.Section9PivotalSupport
public import NearCritical.BulkArmGeometry

/-! The arm avoiding the explored bonds of a cluster (lem.arm.2dspanning,
`delta n^2` argument).

`avoidArm W Q C y r`: `y` is joined, inside the finite region `W` and using no
edge explored by the cluster value `C` of the box `Q`, to a vertex at distance
more than `r`.

* `avoidArm_local`: the event depends only on the bonds
  `sprinklingAvailableBonds W Q C`, which are disjoint from
  `clusterRevealBonds Q C` (`avoidArm_bonds_disjoint`);
* `measurableSet_avoidArm`, `avoidArm_prob_le`: it is measurable and at most as
  likely as the ordinary one-arm event `extrinsicRadiusArmEvent y r`;
* `exists_avoidArm_of_walk`: an open walk from `x` in `Q` to `y₀`, staying in
  `W`, produces a point `y` of the cluster `C_Q(x)` with
  `avoidArm W Q C_Q(x) y r` for every `r < dist y y₀`.

These are exactly the hypotheses on the events `A C y` of
`cluster_conditioned_count_bound`.
-/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open MeasureTheory
open scoped Classical

/-- The arm from `y` avoiding the bonds explored by `C`. -/
def avoidArm {d : ℕ} (W Q C : Finset (Vertex d)) (y : Vertex d) (r : ℝ) :
    Set (Configuration d) :=
  {ω | ∃ v : Vertex d, r < dist y v ∧ (sprinklingUnexploredGraph ω W Q C).Reachable y v}

theorem avoidArm_local {d : ℕ} (W Q C : Finset (Vertex d)) (y : Vertex d) (r : ℝ)
    (ω θ : Configuration d) (h : ∀ b ∈ sprinklingAvailableBonds W Q C, ω b = θ b) :
    ω ∈ avoidArm W Q C y r ↔ θ ∈ avoidArm W Q C y r := by
  unfold avoidArm
  rw [Set.mem_setOf_eq, Set.mem_setOf_eq, sprinklingUnexploredGraph_eq_of_available_agree W Q C ω θ h]

lemma avoidArm_bonds_disjoint {d : ℕ} (W Q C : Finset (Vertex d)) :
    Disjoint (clusterRevealBonds Q C) (sprinklingAvailableBonds W Q C) := by
  unfold sprinklingAvailableBonds
  exact Finset.disjoint_sdiff

theorem measurableSet_avoidArm {d : ℕ} (W Q C : Finset (Vertex d)) (y : Vertex d) (r : ℝ) :
    MeasurableSet (avoidArm W Q C y r) := by
  have he : avoidArm W Q C y r =
      (sprinklingAvailableBonds W Q C).restrict ⁻¹'
        {ξ | extendConfiguration (sprinklingAvailableBonds W Q C) (fun _ => false) ξ ∈
          avoidArm W Q C y r} := by
    ext ω
    exact avoidArm_local W Q C y r ω _ (by
      intro b hb
      simp [extendConfiguration, hb, Finset.restrict])
  rw [he]
  exact (Finset.measurable_restrict _) (Set.toFinite _).measurableSet

theorem avoidArm_subset_arm {d : ℕ} (W Q C : Finset (Vertex d)) (y : Vertex d) (r : ℝ) :
    avoidArm W Q C y r ⊆ extrinsicRadiusArmEvent y r := by
  rintro ω ⟨v, hv, hr⟩
  exact ⟨v, hv, hr.mono (microscopicPieceGraph_le ω _ _)⟩

theorem avoidArm_prob_le {d : ℕ} (p : unitInterval) (W Q C : Finset (Vertex d)) (y : Vertex d)
    (r : ℝ) :
    (percolation d p).real (avoidArm W Q C y r) ≤
      (percolation d p).real (extrinsicRadiusArmEvent y r) :=
  measureReal_mono (avoidArm_subset_arm W Q C y r) (measure_ne_top _ _)

lemma unexplored_reachable_of_avoid {d : ℕ} {ω : Configuration d} (W Q C : Finset (Vertex d)) :
    ∀ {u v : Vertex d} (q : (openGraph ω).Walk u v), (∀ z ∈ q.support, z ∈ W) →
      (∀ b : Bond d, s(b.1, bondTip b) ∈ q.edges → b ∉ clusterRevealBonds Q C) →
      (sprinklingUnexploredGraph ω W Q C).Reachable u v := by
  intro u v q
  induction q with
  | nil => intro _ _; exact SimpleGraph.Reachable.refl _
  | @cons a b' c hab q ih =>
    intro hW hav
    have haW : a ∈ W := hW a (by simp)
    have hbW : b' ∈ W := hW b' (by simp)
    have hrest := ih (fun z hz => hW z (by simp [hz]))
      (fun b hb => hav b (by simp [hb]))
    have hex : ∃ e : Bond d, ω e = true ∧
        ((a = e.1 ∧ b' = bondTip e) ∨ (b' = e.1 ∧ a = bondTip e)) := hab
    obtain ⟨e, _, hends⟩ := hex
    have hed : s(e.1, bondTip e) = s(a, b') := by
      rcases hends with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rfl
      · exact Sym2.eq_swap
    have hnot : e ∉ clusterRevealBonds Q C := hav e (by
      rw [SimpleGraph.Walk.edges_cons, List.mem_cons]
      exact Or.inl hed)
    have hadj : (sprinklingUnexploredGraph ω W Q C).Adj a b' := by
      refine ⟨hab, haW, hbW, ?_⟩
      intro hexp
      obtain ⟨haQ, hbQ, hC⟩ := (pair_mem_exploredEdgeSet _ _ a b').mp hexp
      apply hnot
      rw [mem_clusterRevealBonds]
      rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [← h1, ← h2]
        exact ⟨haQ, hbQ, hC⟩
      · rw [← h1, ← h2]
        exact ⟨hbQ, haQ, hC.symm⟩
    exact hadj.reachable.trans hrest

/-- **From a crossing walk to an avoiding arm at a cluster point.** -/
theorem exists_avoidArm_of_walk {d : ℕ} {ω : Configuration d} (W Q : Finset (Vertex d))
    {x y₀ : Vertex d} (hx : x ∈ Q) (w : (openGraph ω).Walk x y₀)
    (hW : ∀ z ∈ w.support, z ∈ W) :
    ∃ y ∈ finiteBoxCluster ω Q x, y ∈ w.support ∧
      ∀ r : ℝ, r < dist y y₀ → ω ∈ avoidArm W Q (finiteBoxCluster ω Q x) y r := by
  obtain ⟨y, hy, q, hsup, _, hav⟩ := cluster_last_visit_arm Q hx w
  refine ⟨y, hy, hsup y (by simp), ?_⟩
  intro r hr
  exact ⟨y₀, hr, unexplored_reachable_of_avoid W Q _ q (fun z hz => hW z (hsup z hz)) hav⟩

end NearCritical.Section10
