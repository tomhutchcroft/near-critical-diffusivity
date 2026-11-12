module

public import NearCritical.HalfSpaceArmGeometry
public import NearCritical.CountableBK
public import NearCritical.Slab
public import Mathlib.Combinatorics.SimpleGraph.Metric

/-! First moment of the chemical distance inside a box (BK).

For the critical graph restricted to a finite set `Q`:

* `restricted_split_disjointOccurrence`: every vertex `z` of a path from `x` to
  `y` inside `Q` gives the disjoint occurrence of `{x <->_Q z}` and
  `{z <->_Q y}`;
* `restricted_dist_succ_le`: `dist_Q(x,y) + 1` is at most the number of such `z`;
* `restricted_dist_integral_le`:
  `E_p[dist_Q(x,y)] <= sum_{z in Q} P_p[x <->_Q z] P_p[z <->_Q y]`.

This is the BK step for the intrinsic diameter of spanning clusters
(condition (3) of def.spanning.z, used in Step 1 of prop.proba.pregood). No
hypotheses beyond `x in Q`.
-/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open MeasureTheory
open scoped Classical

lemma restrictedGraph_le_openGraph {d : ℕ} (ω : Configuration d) (S : Set (Vertex d)) :
    restrictedGraph ω S ≤ openGraph ω := fun _ _ h => h.1

lemma restrictedWalk_support_mem {d : ℕ} {ω : Configuration d} (Q : Finset (Vertex d))
    {x y : Vertex d} (hx : x ∈ Q) (w : (restrictedGraph ω (Q : Set (Vertex d))).Walk x y) :
    ∀ v ∈ w.support, v ∈ (Q : Set (Vertex d)) := by
  induction w with
  | nil =>
    intro v hv
    rw [SimpleGraph.Walk.support_nil, List.mem_singleton] at hv
    rw [hv]
    exact hx
  | cons h w ih =>
    intro v hv
    rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hv
    rcases hv with rfl | hv
    · exact hx
    · exact ih h.2.2 v hv

theorem restricted_split_disjointOccurrence {d : ℕ} {ω : Configuration d}
    (Q : Finset (Vertex d)) {x y : Vertex d} (hx : x ∈ Q)
    (w : (restrictedGraph ω (Q : Set (Vertex d))).Walk x y) (hw : w.IsPath) {z : Vertex d}
    (hz : z ∈ w.support) :
    DisjointOccurrence (connectionToSetEvent (Q : Set (Vertex d)) x {z})
      (connectionToSetEvent (Q : Set (Vertex d)) z {y}) ω := by
  have hzQ : z ∈ Q := restrictedWalk_support_mem Q hx w z hz
  have hle := restrictedGraph_le_openGraph ω (Q : Set (Vertex d))
  have hs1 : ∀ v ∈ ((w.takeUntil z hz).mapLe hle).support, v ∈ (Q : Set (Vertex d)) := by
    intro v hv
    rw [SimpleGraph.Walk.support_mapLe_eq_support] at hv
    exact restrictedWalk_support_mem Q hx _ v hv
  have hs2 : ∀ v ∈ ((w.dropUntil z hz).mapLe hle).support, v ∈ (Q : Set (Vertex d)) := by
    intro v hv
    rw [SimpleGraph.Walk.support_mapLe_eq_support] at hv
    exact restrictedWalk_support_mem Q hzQ _ v hv
  obtain ⟨P1, ho1, he1, hf1⟩ := openWalk_certificate ((w.takeUntil z hz).mapLe hle) _ hs1
  obtain ⟨P2, ho2, he2, hf2⟩ := openWalk_certificate ((w.dropUntil z hz).mapLe hle) _ hs2
  refine ⟨(P1 : Set (Bond d)), (P2 : Set (Bond d)), P1.finite_toSet, P2.finite_toSet, ?_, ?_, ?_⟩
  · apply Set.disjoint_left.mpr
    intro e h1 h2
    have h1' := he1 e (Finset.mem_coe.mp h1)
    have h2' := he2 e (Finset.mem_coe.mp h2)
    rw [SimpleGraph.Walk.edges_mapLe_eq_edges] at h1' h2'
    exact List.disjoint_left.mp (hw.isTrail.disjoint_edges_takeUntil_dropUntil hz) h1' h2'
  · intro θ hθ
    exact hf1 θ (fun e he => (hθ e (Finset.mem_coe.mpr he)).trans (ho1 e he))
  · intro θ hθ
    exact hf2 θ (fun e he => (hθ e (Finset.mem_coe.mpr he)).trans (ho2 e he))

theorem restricted_dist_succ_le {d : ℕ} (ω : Configuration d) (Q : Finset (Vertex d))
    {x y : Vertex d} (hx : x ∈ Q)
    (hr : (restrictedGraph ω (Q : Set (Vertex d))).Reachable x y) :
    (restrictedGraph ω (Q : Set (Vertex d))).dist x y + 1 ≤
      (Q.filter fun z => DisjointOccurrence (connectionToSetEvent (Q : Set (Vertex d)) x {z})
        (connectionToSetEvent (Q : Set (Vertex d)) z {y}) ω).card := by
  obtain ⟨w, hw⟩ := hr.exists_walk_length_eq_dist
  have hp := w.isPath_of_length_eq_dist hw
  have hsub : w.support.toFinset ⊆ Q.filter fun z =>
      DisjointOccurrence (connectionToSetEvent (Q : Set (Vertex d)) x {z})
        (connectionToSetEvent (Q : Set (Vertex d)) z {y}) ω := by
    intro v hv
    have hv' : v ∈ w.support := List.mem_toFinset.mp hv
    exact Finset.mem_filter.mpr ⟨restrictedWalk_support_mem Q hx w v hv',
      restricted_split_disjointOccurrence Q hx w hp hv'⟩
  have hcard : w.support.toFinset.card = w.length + 1 := by
    rw [List.toFinset_card_of_nodup hp.support_nodup, SimpleGraph.Walk.length_support]
  calc (restrictedGraph ω (Q : Set (Vertex d))).dist x y + 1 = w.support.toFinset.card := by
        rw [hcard, hw]
    _ ≤ _ := Finset.card_le_card hsub

/-- **First moment of the chemical distance inside a box.** -/
theorem restricted_dist_integral_le {d : ℕ} (p : unitInterval) (Q : Finset (Vertex d))
    (x y : Vertex d) (hx : x ∈ Q) :
    (∫ ω, ((restrictedGraph ω (Q : Set (Vertex d))).dist x y : ℝ) ∂(percolation d p)) ≤
      ∑ z ∈ Q, (percolation d p).real (connectionToSetEvent (Q : Set (Vertex d)) x {z}) *
        (percolation d p).real (connectionToSetEvent (Q : Set (Vertex d)) z {y}) := by
  have hmeas : ∀ z, MeasurableSet {ω : Configuration d |
      DisjointOccurrence (connectionToSetEvent (Q : Set (Vertex d)) x {z})
        (connectionToSetEvent (Q : Set (Vertex d)) z {y}) ω} :=
    fun z => measurableSet_disjointOccurrence (connectionToSetEvent_increasing _ _ _)
      (connectionToSetEvent_increasing _ _ _)
  have hint : ∀ z ∈ Q, Integrable (Set.indicator {ω : Configuration d |
      DisjointOccurrence (connectionToSetEvent (Q : Set (Vertex d)) x {z})
        (connectionToSetEvent (Q : Set (Vertex d)) z {y}) ω}
      (fun _ => (1:ℝ))) (percolation d p) :=
    fun z _ => (integrable_const (1:ℝ)).indicator (hmeas z)
  have hpt : ∀ ω : Configuration d, ((restrictedGraph ω (Q : Set (Vertex d))).dist x y : ℝ) ≤
      ∑ z ∈ Q, Set.indicator {ω : Configuration d |
        DisjointOccurrence (connectionToSetEvent (Q : Set (Vertex d)) x {z})
          (connectionToSetEvent (Q : Set (Vertex d)) z {y}) ω} (fun _ => (1:ℝ)) ω := by
    intro ω
    have hsum : (∑ z ∈ Q, Set.indicator {ω : Configuration d |
        DisjointOccurrence (connectionToSetEvent (Q : Set (Vertex d)) x {z})
          (connectionToSetEvent (Q : Set (Vertex d)) z {y}) ω} (fun _ => (1:ℝ)) ω) =
        ((Q.filter fun z => DisjointOccurrence
          (connectionToSetEvent (Q : Set (Vertex d)) x {z})
          (connectionToSetEvent (Q : Set (Vertex d)) z {y}) ω).card : ℝ) := by
      rw [Finset.card_filter]
      push_cast
      refine Finset.sum_congr rfl (fun z _ => ?_)
      simp only [Set.indicator, Set.mem_setOf_eq]
    rw [hsum]
    by_cases hr : (restrictedGraph ω (Q : Set (Vertex d))).Reachable x y
    · have h := restricted_dist_succ_le ω Q hx hr
      have h' := (Nat.cast_le (α := ℝ)).mpr h
      push_cast at h'
      linarith
    · rw [SimpleGraph.dist_eq_zero_of_not_reachable hr]
      simp
  refine (integral_mono_of_nonneg (Filter.Eventually.of_forall (fun ω => Nat.cast_nonneg _))
    (integrable_finset_sum Q hint) (Filter.Eventually.of_forall hpt)).trans ?_
  rw [integral_finset_sum Q hint]
  refine Finset.sum_le_sum (fun z _ => ?_)
  rw [integral_indicator_const _ (hmeas z), smul_eq_mul, mul_one]
  exact percolation_bk d p _ _ (connectionToSetEvent_increasing _ _ _)
    (connectionToSetEvent_increasing _ _ _)

end NearCritical.Section10
