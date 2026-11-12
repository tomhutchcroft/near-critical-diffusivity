module

public import NearCritical.Section9IntrinsicDistanceMoment
public import NearCritical.BulkSupercriticalBound

/-! The three-factor BK estimate of `lem.sprinkling.AB.geo`.

For a pivotal pair `(a, b)` the left cluster of `a` and the right cluster of
`b` are disjoint, so a geodesic from `x` to `a` in the left unexplored graph
and any path from `y` to `b` in the right one are edge-disjoint. Hence
`{x <-> z} o {z <-> a} o {y <-> b}` occurs for every vertex `z` of the
geodesic, and by BK (twice)

  `E_p[ dist_L(x,a) ; x <-> a, y <-> b, clusters separated ]
      <= sum_z tau_p(x,z) tau_p(z,a) tau_p(y,b)`

(`pivot_dist_integral_le`). This is the displayed BK inequality in the proof of
the lemma, under the unconditional law, with no hypotheses.
-/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory
open scoped Classical

theorem pivot_split_disjointOccurrence {d : ℕ} {ω : Configuration d}
    (L R Q₁ F₁ Q₃ F₃ : Finset (Vertex d)) {x a y b : Vertex d}
    (w : (sprinklingUnexploredGraph ω L Q₁ F₁).Walk x a) (hw : w.IsPath)
    (w' : (sprinklingUnexploredGraph ω R Q₃ F₃).Walk y b)
    (hdisj : ∀ v ∈ w.support, v ∉ w'.support) {z : Vertex d} (hz : z ∈ w.support) :
    DisjointOccurrence
      {θ | DisjointOccurrence (unexploredConnEvent L Q₁ F₁ x z)
        (unexploredConnEvent L Q₁ F₁ z a) θ}
      (unexploredConnEvent R Q₃ F₃ y b) ω := by
  obtain ⟨P1, ho1, he1, hf1⟩ := sprinklingUnexploredWalk_certificate L Q₁ F₁ (w.takeUntil z hz)
  obtain ⟨P2, ho2, he2, hf2⟩ := sprinklingUnexploredWalk_certificate L Q₁ F₁ (w.dropUntil z hz)
  obtain ⟨P3, ho3, he3, hf3⟩ := sprinklingUnexploredWalk_certificate R Q₃ F₃ w'
  have h12 : Disjoint (P1 : Set (Bond d)) (P2 : Set (Bond d)) := by
    apply Set.disjoint_left.mpr
    intro e h1 h2
    exact List.disjoint_left.mp (hw.isTrail.disjoint_edges_takeUntil_dropUntil hz)
      (he1 e (Finset.mem_coe.mp h1)) (he2 e (Finset.mem_coe.mp h2))
  refine ⟨((P1 ∪ P2 : Finset (Bond d)) : Set (Bond d)), (P3 : Set (Bond d)),
    (P1 ∪ P2).finite_toSet, P3.finite_toSet, ?_, ?_, ?_⟩
  · apply Set.disjoint_left.mpr
    intro e h h3
    have h3' := he3 e (Finset.mem_coe.mp h3)
    have hv' : e.1 ∈ w'.support := w'.fst_mem_support_of_mem_edges h3'
    rcases Finset.mem_union.mp (Finset.mem_coe.mp h) with h1 | h2
    · have hv := (w.takeUntil z hz).fst_mem_support_of_mem_edges (he1 e h1)
      exact hdisj e.1 (w.support_takeUntil_subset hz hv) hv'
    · have hv := (w.dropUntil z hz).fst_mem_support_of_mem_edges (he2 e h2)
      exact hdisj e.1 (w.support_dropUntil_subset hz hv) hv'
  · intro θ hθ
    refine ⟨(P1 : Set (Bond d)), (P2 : Set (Bond d)), P1.finite_toSet, P2.finite_toSet, h12,
      ?_, ?_⟩
    · intro θ' h'
      exact hf1 θ' (fun e he => (h' e (Finset.mem_coe.mpr he)).trans
        ((hθ e (Finset.mem_coe.mpr (Finset.mem_union_left _ he))).trans (ho1 e he)))
    · intro θ' h'
      exact hf2 θ' (fun e he => (h' e (Finset.mem_coe.mpr he)).trans
        ((hθ e (Finset.mem_coe.mpr (Finset.mem_union_right _ he))).trans (ho2 e he)))
  · intro θ hθ
    exact hf3 θ (fun e he => (hθ e (Finset.mem_coe.mpr he)).trans (ho3 e he))

theorem pivot_dist_succ_le {d : ℕ} (ω : Configuration d)
    (L R Q₁ F₁ Q₃ F₃ S : Finset (Vertex d)) {x a y b : Vertex d}
    (hxa : (sprinklingUnexploredGraph ω L Q₁ F₁).Reachable x a)
    (hyb : (sprinklingUnexploredGraph ω R Q₃ F₃).Reachable y b)
    (hsep : ∀ v, (sprinklingUnexploredGraph ω L Q₁ F₁).Reachable a v →
      ¬ (sprinklingUnexploredGraph ω R Q₃ F₃).Reachable b v)
    (hS : ∀ v, (sprinklingUnexploredGraph ω L Q₁ F₁).Reachable x v → v ∈ S) :
    (sprinklingUnexploredGraph ω L Q₁ F₁).dist x a + 1 ≤
      (S.filter fun z => DisjointOccurrence
        {θ | DisjointOccurrence (unexploredConnEvent L Q₁ F₁ x z)
          (unexploredConnEvent L Q₁ F₁ z a) θ}
        (unexploredConnEvent R Q₃ F₃ y b) ω).card := by
  obtain ⟨w, hw⟩ := hxa.exists_walk_length_eq_dist
  obtain ⟨w'⟩ := hyb
  have hp := w.isPath_of_length_eq_dist hw
  have hdisj : ∀ v ∈ w.support, v ∉ w'.support := by
    intro v hv hv'
    exact hsep v ⟨(w.dropUntil v hv).reverse⟩ ⟨(w'.dropUntil v hv').reverse⟩
  have hsub : w.support.toFinset ⊆ S.filter fun z => DisjointOccurrence
      {θ | DisjointOccurrence (unexploredConnEvent L Q₁ F₁ x z)
        (unexploredConnEvent L Q₁ F₁ z a) θ}
      (unexploredConnEvent R Q₃ F₃ y b) ω := by
    intro v hv
    have hv' : v ∈ w.support := List.mem_toFinset.mp hv
    exact Finset.mem_filter.mpr ⟨hS v ⟨w.takeUntil v hv'⟩,
      pivot_split_disjointOccurrence L R Q₁ F₁ Q₃ F₃ w hp w' hdisj hv'⟩
  have hcard : w.support.toFinset.card = w.length + 1 := by
    rw [List.toFinset_card_of_nodup hp.support_nodup, SimpleGraph.Walk.length_support]
  calc (sprinklingUnexploredGraph ω L Q₁ F₁).dist x a + 1 = w.support.toFinset.card := by
        rw [hcard, hw]
    _ ≤ _ := Finset.card_le_card hsub

/-- **Three-factor BK estimate of lem.sprinkling.AB.geo.** -/
theorem pivot_dist_integral_le {d : ℕ} (p : unitInterval)
    (L R Q₁ F₁ Q₃ F₃ : Finset (Vertex d)) (x a y b : Vertex d) :
    (∫ ω, (if ((sprinklingUnexploredGraph ω L Q₁ F₁).Reachable x a ∧
        (sprinklingUnexploredGraph ω R Q₃ F₃).Reachable y b ∧
        ∀ v, (sprinklingUnexploredGraph ω L Q₁ F₁).Reachable a v →
          ¬ (sprinklingUnexploredGraph ω R Q₃ F₃).Reachable b v)
      then ((sprinklingUnexploredGraph ω L Q₁ F₁).dist x a : ℝ) else 0)
      ∂(percolation d p)) ≤
      ∑ z ∈ insert x L, twoPoint d p x z * twoPoint d p z a * twoPoint d p y b := by
  have hinc : ∀ z, BK.Increasing {θ : Configuration d |
      DisjointOccurrence (unexploredConnEvent L Q₁ F₁ x z)
        (unexploredConnEvent L Q₁ F₁ z a) θ} :=
    fun z => increasing_disjointOccurrence (unexploredConnEvent_increasing L Q₁ F₁ x z)
      (unexploredConnEvent_increasing L Q₁ F₁ z a)
  have hmeas : ∀ z, MeasurableSet {ω : Configuration d | DisjointOccurrence
      {θ | DisjointOccurrence (unexploredConnEvent L Q₁ F₁ x z)
        (unexploredConnEvent L Q₁ F₁ z a) θ}
      (unexploredConnEvent R Q₃ F₃ y b) ω} :=
    fun z => measurableSet_disjointOccurrence (hinc z)
      (unexploredConnEvent_increasing R Q₃ F₃ y b)
  have hint : ∀ z ∈ insert x L, Integrable (Set.indicator {ω : Configuration d |
      DisjointOccurrence
        {θ | DisjointOccurrence (unexploredConnEvent L Q₁ F₁ x z)
          (unexploredConnEvent L Q₁ F₁ z a) θ}
        (unexploredConnEvent R Q₃ F₃ y b) ω} (fun _ => (1:ℝ))) (percolation d p) :=
    fun z _ => (integrable_const (1:ℝ)).indicator (hmeas z)
  have hpt : ∀ ω : Configuration d,
      (if ((sprinklingUnexploredGraph ω L Q₁ F₁).Reachable x a ∧
        (sprinklingUnexploredGraph ω R Q₃ F₃).Reachable y b ∧
        ∀ v, (sprinklingUnexploredGraph ω L Q₁ F₁).Reachable a v →
          ¬ (sprinklingUnexploredGraph ω R Q₃ F₃).Reachable b v)
      then ((sprinklingUnexploredGraph ω L Q₁ F₁).dist x a : ℝ) else 0) ≤
      ∑ z ∈ insert x L, Set.indicator {ω : Configuration d | DisjointOccurrence
        {θ | DisjointOccurrence (unexploredConnEvent L Q₁ F₁ x z)
          (unexploredConnEvent L Q₁ F₁ z a) θ}
        (unexploredConnEvent R Q₃ F₃ y b) ω} (fun _ => (1:ℝ)) ω := by
    intro ω
    have hsum : (∑ z ∈ insert x L, Set.indicator {ω : Configuration d | DisjointOccurrence
        {θ | DisjointOccurrence (unexploredConnEvent L Q₁ F₁ x z)
          (unexploredConnEvent L Q₁ F₁ z a) θ}
        (unexploredConnEvent R Q₃ F₃ y b) ω} (fun _ => (1:ℝ)) ω) =
        (((insert x L).filter fun z => DisjointOccurrence
          {θ | DisjointOccurrence (unexploredConnEvent L Q₁ F₁ x z)
            (unexploredConnEvent L Q₁ F₁ z a) θ}
          (unexploredConnEvent R Q₃ F₃ y b) ω).card : ℝ) := by
      rw [Finset.card_filter]
      push_cast
      refine Finset.sum_congr rfl (fun z _ => ?_)
      simp only [Set.indicator, Set.mem_setOf_eq]
    rw [hsum]
    split_ifs with hc
    · have h := pivot_dist_succ_le ω L R Q₁ F₁ Q₃ F₃ (insert x L) hc.1 hc.2.1 hc.2.2
        (fun v hr => unexplored_reachable_mem ω L Q₁ F₁ hr)
      have h' := (Nat.cast_le (α := ℝ)).mpr h
      push_cast at h'
      linarith
    · exact Nat.cast_nonneg _
  refine (integral_mono_of_nonneg (Filter.Eventually.of_forall (fun ω => ?_))
    (integrable_finset_sum _ hint) (Filter.Eventually.of_forall hpt)).trans ?_
  · show (0:ℝ) ≤ _
    split_ifs
    · exact Nat.cast_nonneg _
    · exact le_refl _
  rw [integral_finset_sum _ hint]
  refine Finset.sum_le_sum (fun z _ => ?_)
  rw [integral_indicator_const _ (hmeas z), smul_eq_mul, mul_one]
  refine (percolation_bk d p _ _ (hinc z) (unexploredConnEvent_increasing R Q₃ F₃ y b)).trans ?_
  have h2 := percolation_bk d p _ _ (unexploredConnEvent_increasing L Q₁ F₁ x z)
    (unexploredConnEvent_increasing L Q₁ F₁ z a)
  unfold twoPoint
  have hA := measureReal_mono (μ := percolation d p)
    (unexploredConnEvent_subset_connection L Q₁ F₁ x z) (measure_ne_top _ _)
  have hB := measureReal_mono (μ := percolation d p)
    (unexploredConnEvent_subset_connection L Q₁ F₁ z a) (measure_ne_top _ _)
  have hC := measureReal_mono (μ := percolation d p)
    (unexploredConnEvent_subset_connection R Q₃ F₃ y b) (measure_ne_top _ _)
  exact mul_le_mul (h2.trans (mul_le_mul hA hB measureReal_nonneg measureReal_nonneg)) hC
    measureReal_nonneg (mul_nonneg measureReal_nonneg measureReal_nonneg)

/-- A pivotal pair separates the two unexplored clusters (the condition of
`pivot_dist_integral_le`). -/
theorem sprinklingPivotalPair_sep {d : ℕ} {ω : Configuration d}
    (L R Q₁ F₁ Q₃ F₃ A B : Finset (Vertex d)) {e : Vertex d × Vertex d}
    (he : sprinklingPivotalPair ω L R Q₁ F₁ Q₃ F₃ A B e) :
    ∀ v, (sprinklingUnexploredGraph ω L Q₁ F₁).Reachable e.1 v →
      ¬ (sprinklingUnexploredGraph ω R Q₃ F₃).Reachable e.2 v := by
  obtain ⟨_, h1L, h2R, _, _, hdisj⟩ := he
  intro v hL hR
  have hvL : v ∈ L := by
    rcases Finset.mem_insert.mp (unexplored_reachable_mem ω L Q₁ F₁ hL) with h | h
    · rw [h]; exact h1L
    · exact h
  have hvR : v ∈ R := by
    rcases Finset.mem_insert.mp (unexplored_reachable_mem ω R Q₃ F₃ hR) with h | h
    · rw [h]; exact h2R
    · exact h
  exact Finset.disjoint_left.mp hdisj
    ((mem_sprinklingUnexploredCluster ω L Q₁ F₁ e.1 v).mpr ⟨hvL, hL⟩)
    ((mem_sprinklingUnexploredCluster ω R Q₃ F₃ e.2 v).mpr ⟨hvR, hR⟩)

end NearCritical
