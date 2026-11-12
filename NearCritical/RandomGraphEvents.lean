module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.MeasureTheory.MeasurableSpace.CountablyGenerated
public import Mathlib.Data.Set.Finite.Basic

/-! Measurability of connectivity and infinite clusters for countable random
graphs with measurable edge events. Applies to full lattices and restricted
slabs on the same configuration space. -/
@[expose] public section
namespace NearCritical
open MeasureTheory Set

def graphNStep {V : Type*} (G : SimpleGraph V) : ℕ → V → V → Prop
  | 0, x, y => x = y
  | n + 1, x, y => ∃ z, graphNStep G n x z ∧ G.Adj z y

lemma graph_reachable_iff_exists_nStep {V : Type*} (G : SimpleGraph V) (x y : V) :
    G.Reachable x y ↔ ∃ n, graphNStep G n x y := by
  rw [SimpleGraph.reachable_iff_reflTransGen]
  constructor
  · intro h
    induction h with
    | refl => exact ⟨0, rfl⟩
    | @tail z y _ hzy ih =>
      obtain ⟨n, hn⟩ := ih
      exact ⟨n + 1, z, hn, hzy⟩
  · rintro ⟨n, hn⟩
    induction n generalizing y with
    | zero => exact hn ▸ Relation.ReflTransGen.refl
    | succ n ih =>
      obtain ⟨z, hz, hzy⟩ := hn
      exact (ih z hz).tail hzy

lemma infinite_iff_escape_finsets {α : Type*} (s : Set α) :
    s.Infinite ↔ ∀ t : Finset α, ∃ y ∈ s, y ∉ t := by
  classical
  constructor
  · exact fun hs t ↦ hs.exists_notMem_finset t
  · intro hs hf
    obtain ⟨y, hy, hnot⟩ := hs hf.toFinset
    exact hnot (hf.mem_toFinset.mpr hy)

section Random
variable {Ω V : Type*} [MeasurableSpace Ω] [Countable V]
variable (G : Ω → SimpleGraph V)
variable (hG : ∀ x y, MeasurableSet {ω | (G ω).Adj x y})
include hG

lemma measurableSet_graphNStep (n : ℕ) (x y : V) :
    MeasurableSet {ω | graphNStep (G ω) n x y} := by
  induction n generalizing y with
  | zero => exact MeasurableSet.const _
  | succ n ih =>
    change MeasurableSet {ω | ∃ z, graphNStep (G ω) n x z ∧ (G ω).Adj z y}
    simp only [ofPred_exists, ofPred_and]
    exact MeasurableSet.iUnion (fun z ↦ (ih z).inter (hG z y))

lemma measurableSet_graphReachable (x y : V) :
    MeasurableSet {ω | (G ω).Reachable x y} := by
  simp only [graph_reachable_iff_exists_nStep, ofPred_exists]
  exact MeasurableSet.iUnion (fun n ↦ measurableSet_graphNStep G hG n x y)

lemma measurableSet_graphInfiniteCluster (x : V) :
    MeasurableSet {ω | {y | (G ω).Reachable x y}.Infinite} := by
  have heq : {ω | {y | (G ω).Reachable x y}.Infinite} =
      ⋂ s : Finset V, ⋃ y : V,
        {ω | (G ω).Reachable x y} ∩ {ω : Ω | y ∉ s} := by
    ext ω
    simp [infinite_iff_escape_finsets]
  rw [heq]
  exact MeasurableSet.iInter (fun s ↦ MeasurableSet.iUnion
    (fun y ↦ (measurableSet_graphReachable G hG x y).inter (MeasurableSet.const _)))

end Random
end NearCritical
