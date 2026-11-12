module

public import NearCritical.ExternalExactExposure
public import NearCritical.BulkDomain
public import NearCritical.Slab

/-!
Actual graph identification for the imported openai/math finite exposure.
The query domain is internalBondSet U: both endpoints must lie in U.
Outside vertices are isolated in both graphs, including zero-length paths.
 Completeness and query-cost remain open.
-/
@[expose] public section
namespace NearCritical.External
open OAI.CriticalPercolation

/-- The imported labelled graph on the actual internal bonds is exactly the
project's open graph restricted to the finite vertex domain. -/
theorem finite_search_graph_eq_restricted {d : ℕ} (U : Finset (Vertex d))
    (ω : Configuration d) :
    (finiteBondSearchGraph (internalBondSet U)).openGraph {e | ω e.val = true} =
      restrictedGraph ω (U : Set (Vertex d)) := by
  ext x y
  constructor
  · intro hxy
    obtain ⟨⟨e, he, heq⟩, _⟩ := (SimpleGraph.fromEdgeSet_adj _).mp hxy
    have hends : s(e.val.1, bondTip e.val) = s(x, y) := heq
    have hi := (mem_internalBondSet U e.val).mp e.property
    rcases Sym2.eq_iff.mp hends with ⟨hbase, htip⟩ | ⟨hbase, htip⟩
    · exact ⟨⟨e.val, he, Or.inl ⟨hbase.symm, htip.symm⟩⟩,
        hbase ▸ hi.1, htip ▸ hi.2⟩
    · exact ⟨⟨e.val, he, Or.inr ⟨hbase.symm, htip.symm⟩⟩,
        htip ▸ hi.2, hbase ▸ hi.1⟩
  · rintro ⟨⟨e, he, hends⟩, hx, hy⟩
    have hi : e ∈ internalBondSet U := by
      apply (mem_internalBondSet U e).mpr
      rcases hends with ⟨hbase, htip⟩ | ⟨hbase, htip⟩
      · exact ⟨hbase ▸ hx, htip ▸ hy⟩
      · exact ⟨hbase ▸ hy, htip ▸ hx⟩
    apply (SimpleGraph.fromEdgeSet_adj _).mpr
    refine ⟨⟨⟨e, hi⟩, he, ?_⟩, ?_⟩
    · change s(e.1, bondTip e) = s(x, y)
      apply Sym2.eq_iff.mpr
      rcases hends with ⟨hbase, htip⟩ | ⟨hbase, htip⟩
      · exact Or.inl ⟨hbase.symm, htip.symm⟩
      · exact Or.inr ⟨hbase.symm, htip.symm⟩
    · exact (show (NearCritical.openGraph ω).Adj x y from ⟨e, he, hends⟩).ne

/-- Reached vertices in the imported finite exposure are connected to the root
in the actual domain-restricted project graph. -/
theorem finite_exposure_reached_actual {d : ℕ} (U : Finset (Vertex d))
    (x : Vertex d) (n : ℕ) (ω : Configuration d) :
    ∀ y ∈ ((ExactExposure.compile (finiteBondSearchGraph (internalBondSet U)) n
      (rootExposureState (internalBondSet U) x)).run (fun e => ω e.val)).reached,
      (restrictedGraph ω (U : Set (Vertex d))).Reachable x y := by
  intro y hy
  obtain ⟨s, hs, hsy⟩ := finite_exposure_sound (internalBondSet U) x n ω y hy
  have hsx : s = x := Set.mem_singleton_iff.mp hs
  subst s
  rw [finite_search_graph_eq_restricted] at hsy
  exact hsy

end NearCritical.External
