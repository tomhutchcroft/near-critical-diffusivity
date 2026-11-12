module

public import NearCritical.Bernoulli
public import NearCritical.RandomGraphEvents

@[expose] public section
namespace NearCritical
open MeasureTheory Set

lemma measurableSet_open_adj {d : ℕ} (x y : Vertex d) :
    MeasurableSet {ω : Configuration d | (openGraph ω).Adj x y} := by
  change MeasurableSet {ω : Configuration d | ∃ e : Bond d, ω e = true ∧
    ((x = e.1 ∧ y = bondTip e) ∨ (y = e.1 ∧ x = bondTip e))}
  simp only [ofPred_exists]
  apply MeasurableSet.iUnion
  intro e
  exact (measurableSet_eq_fun (measurable_pi_apply e) measurable_const).inter
    (MeasurableSet.const _)

lemma measurableSet_connectionEvent {d : ℕ} (x y : Vertex d) :
    MeasurableSet (connectionEvent x y) :=
  measurableSet_graphReachable (fun ω ↦ openGraph ω) measurableSet_open_adj x y

lemma measurableSet_infiniteClusterEvent (d : ℕ) :
    MeasurableSet (infiniteClusterEvent d) :=
  measurableSet_graphInfiniteCluster (fun ω ↦ openGraph ω) measurableSet_open_adj 0

/-- Opening edges preserves every finite or infinite connection. -/
lemma openGraph_mono {d : ℕ} {ω η : Configuration d}
    (h : ∀ e, ω e = true → η e = true) : openGraph ω ≤ openGraph η := by
  rintro x y ⟨e, he, hxy⟩
  exact ⟨e, h e he, hxy⟩

lemma cluster_mono {d : ℕ} {ω η : Configuration d}
    (h : ∀ e, ω e = true → η e = true) (x : Vertex d) :
    cluster ω x ⊆ cluster η x := by
  intro y hy
  exact SimpleGraph.Reachable.mono (openGraph_mono h) hy

end NearCritical
