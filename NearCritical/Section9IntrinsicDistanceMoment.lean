module

public import NearCritical.Section9AvoidanceCertificate
public import NearCritical.Section9SprinklingConnection
public import NearCritical.CountableBK

/-! The BK step of `lem.sprinkling.AB.geo`: first moment of the intrinsic
distance in the unexplored tube graph.

For `G = sprinklingUnexploredGraph omega T Q F` (the critical graph of a tube
with the explored edges of a revealed cluster removed):

* `unexplored_split_disjointOccurrence`: every vertex `z` of a path from `x` to
  `y` splits it into two edge-disjoint pieces, so `{x <-> z}` and `{z <-> y}`
  occur disjointly (source: "every vertex z of pi_1 splits it into two
  edge-disjoint open paths").
* `unexplored_dist_succ_le`: `dist(x,y) + 1` is at most the number of such `z`.
* `unexplored_dist_integral_le`: `E_p[dist_G(x,y)] <= sum_z tau_p(x,z) tau_p(z,y)`
  by the BK inequality. No hypothesis beyond a finite set containing the
  vertices reachable from `x`.
-/
@[expose] public section
noncomputable section
namespace NearCritical
open MeasureTheory
open scoped Classical

/-- Connection in the unexplored tube graph, as an event. -/
def unexploredConnEvent {d : ℕ} (T Q F : Finset (Vertex d)) (u v : Vertex d) :
    Set (Configuration d) :=
  {θ | (sprinklingUnexploredGraph θ T Q F).Reachable u v}

lemma unexploredConnEvent_increasing {d : ℕ} (T Q F : Finset (Vertex d)) (u v : Vertex d) :
    BK.Increasing (unexploredConnEvent T Q F u v) :=
  fun _ _ h hη => SimpleGraph.Reachable.mono (sprinklingUnexploredGraph_mono h T Q F) hη

lemma unexploredConnEvent_subset_connection {d : ℕ} (T Q F : Finset (Vertex d))
    (u v : Vertex d) : unexploredConnEvent T Q F u v ⊆ connectionEvent u v :=
  fun θ h => SimpleGraph.Reachable.mono (microscopicPieceGraph_le θ _ _) h

theorem unexplored_split_disjointOccurrence {d : ℕ} {ω : Configuration d}
    (T Q F : Finset (Vertex d)) {x y : Vertex d}
    (w : (sprinklingUnexploredGraph ω T Q F).Walk x y) (hw : w.IsPath) {z : Vertex d}
    (hz : z ∈ w.support) :
    DisjointOccurrence (unexploredConnEvent T Q F x z) (unexploredConnEvent T Q F z y) ω := by
  obtain ⟨P1, ho1, he1, hf1⟩ := sprinklingUnexploredWalk_certificate T Q F (w.takeUntil z hz)
  obtain ⟨P2, ho2, he2, hf2⟩ := sprinklingUnexploredWalk_certificate T Q F (w.dropUntil z hz)
  refine ⟨(P1 : Set (Bond d)), (P2 : Set (Bond d)), P1.finite_toSet, P2.finite_toSet, ?_, ?_, ?_⟩
  · apply Set.disjoint_left.mpr
    intro e h1 h2
    exact List.disjoint_left.mp (hw.isTrail.disjoint_edges_takeUntil_dropUntil hz)
      (he1 e (Finset.mem_coe.mp h1)) (he2 e (Finset.mem_coe.mp h2))
  · intro θ hθ
    exact hf1 θ (fun e he => (hθ e (Finset.mem_coe.mpr he)).trans (ho1 e he))
  · intro θ hθ
    exact hf2 θ (fun e he => (hθ e (Finset.mem_coe.mpr he)).trans (ho2 e he))

theorem unexplored_dist_succ_le {d : ℕ} (ω : Configuration d) (T Q F S : Finset (Vertex d))
    {x y : Vertex d} (hr : (sprinklingUnexploredGraph ω T Q F).Reachable x y)
    (hS : ∀ v, (sprinklingUnexploredGraph ω T Q F).Reachable x v → v ∈ S) :
    (sprinklingUnexploredGraph ω T Q F).dist x y + 1 ≤
      (S.filter fun z => DisjointOccurrence (unexploredConnEvent T Q F x z)
        (unexploredConnEvent T Q F z y) ω).card := by
  obtain ⟨w, hw⟩ := hr.exists_walk_length_eq_dist
  have hp := w.isPath_of_length_eq_dist hw
  have hsub : w.support.toFinset ⊆ S.filter fun z =>
      DisjointOccurrence (unexploredConnEvent T Q F x z) (unexploredConnEvent T Q F z y) ω := by
    intro v hv
    have hv' : v ∈ w.support := List.mem_toFinset.mp hv
    exact Finset.mem_filter.mpr ⟨hS v ⟨w.takeUntil v hv'⟩,
      unexplored_split_disjointOccurrence T Q F w hp hv'⟩
  have hcard : w.support.toFinset.card = w.length + 1 := by
    rw [List.toFinset_card_of_nodup hp.support_nodup, SimpleGraph.Walk.length_support]
  calc (sprinklingUnexploredGraph ω T Q F).dist x y + 1 = w.support.toFinset.card := by
        rw [hcard, hw]
    _ ≤ _ := Finset.card_le_card hsub

/-- **First moment of the intrinsic distance** (BK step of lem.sprinkling.AB.geo). -/
theorem unexplored_dist_integral_le {d : ℕ} (p : unitInterval) (T Q F S : Finset (Vertex d))
    (x y : Vertex d)
    (hS : ∀ (ω : Configuration d) v,
      (sprinklingUnexploredGraph ω T Q F).Reachable x v → v ∈ S) :
    (∫ ω, ((sprinklingUnexploredGraph ω T Q F).dist x y : ℝ) ∂(percolation d p)) ≤
      ∑ z ∈ S, twoPoint d p x z * twoPoint d p z y := by
  have hmeas : ∀ z, MeasurableSet {ω : Configuration d |
      DisjointOccurrence (unexploredConnEvent T Q F x z) (unexploredConnEvent T Q F z y) ω} :=
    fun z => measurableSet_disjointOccurrence (unexploredConnEvent_increasing T Q F x z)
      (unexploredConnEvent_increasing T Q F z y)
  have hint : ∀ z ∈ S, Integrable (Set.indicator {ω : Configuration d |
      DisjointOccurrence (unexploredConnEvent T Q F x z) (unexploredConnEvent T Q F z y) ω}
      (fun _ => (1:ℝ))) (percolation d p) :=
    fun z _ => (integrable_const (1:ℝ)).indicator (hmeas z)
  have hpt : ∀ ω : Configuration d, ((sprinklingUnexploredGraph ω T Q F).dist x y : ℝ) ≤
      ∑ z ∈ S, Set.indicator {ω : Configuration d |
        DisjointOccurrence (unexploredConnEvent T Q F x z) (unexploredConnEvent T Q F z y) ω}
        (fun _ => (1:ℝ)) ω := by
    intro ω
    have hsum : (∑ z ∈ S, Set.indicator {ω : Configuration d |
        DisjointOccurrence (unexploredConnEvent T Q F x z) (unexploredConnEvent T Q F z y) ω}
        (fun _ => (1:ℝ)) ω) = ((S.filter fun z => DisjointOccurrence
          (unexploredConnEvent T Q F x z) (unexploredConnEvent T Q F z y) ω).card : ℝ) := by
      rw [Finset.card_filter]
      push_cast
      refine Finset.sum_congr rfl (fun z _ => ?_)
      simp only [Set.indicator, Set.mem_setOf_eq]
    rw [hsum]
    by_cases hr : (sprinklingUnexploredGraph ω T Q F).Reachable x y
    · have h := unexplored_dist_succ_le ω T Q F S hr (hS ω)
      have h' := (Nat.cast_le (α := ℝ)).mpr h
      push_cast at h'
      linarith
    · rw [SimpleGraph.dist_eq_zero_of_not_reachable hr]
      simp
  refine (integral_mono_of_nonneg (Filter.Eventually.of_forall (fun ω => Nat.cast_nonneg _))
    (integrable_finset_sum S hint) (Filter.Eventually.of_forall hpt)).trans ?_
  rw [integral_finset_sum S hint]
  refine Finset.sum_le_sum (fun z _ => ?_)
  rw [integral_indicator_const _ (hmeas z), smul_eq_mul, mul_one]
  refine (percolation_bk d p _ _ (unexploredConnEvent_increasing T Q F x z)
    (unexploredConnEvent_increasing T Q F z y)).trans ?_
  unfold twoPoint
  exact mul_le_mul
    (measureReal_mono (unexploredConnEvent_subset_connection T Q F x z) (measure_ne_top _ _))
    (measureReal_mono (unexploredConnEvent_subset_connection T Q F z y) (measure_ne_top _ _))
    measureReal_nonneg measureReal_nonneg

lemma unexplored_reachable_mem {d : ℕ} (ω : Configuration d) (T Q F : Finset (Vertex d))
    {x v : Vertex d} (hr : (sprinklingUnexploredGraph ω T Q F).Reachable x v) :
    v ∈ insert x T := by
  obtain ⟨w⟩ := hr
  cases hw : w.reverse with
  | nil => exact Finset.mem_insert_self _ _
  | cons h _ =>
    have hv : v ∈ (T : Set (Vertex d)) := h.2.1
    exact Finset.mem_insert_of_mem hv

/-- The first-moment bound with the explicit vertex set `{x} ∪ T`. -/
theorem unexplored_dist_integral_le_tube {d : ℕ} (p : unitInterval) (T Q F : Finset (Vertex d))
    (x y : Vertex d) :
    (∫ ω, ((sprinklingUnexploredGraph ω T Q F).dist x y : ℝ) ∂(percolation d p)) ≤
      ∑ z ∈ insert x T, twoPoint d p x z * twoPoint d p z y :=
  unexplored_dist_integral_le p T Q F (insert x T) x y
    (fun ω _ hr => unexplored_reachable_mem ω T Q F hr)

end NearCritical
