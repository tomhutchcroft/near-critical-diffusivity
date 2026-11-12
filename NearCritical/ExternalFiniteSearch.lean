module

public import NearCritical.Bernoulli
public import OAI.Probability.CriticalPercolation.Exploration.SearchTree

/-!
Concrete finite lazy DFS source from openai/math commit
4eaee87548250b2682affda7d05d947c05554bae. Original byte hashes and Apache
license are retained in third_party/openai-math. Local native checks pending.
This instantiates labelled bonds with the actual project bond indices. It
asserts no event correctness, adequate fuel, cost bound, or infinite padding.
-/
@[expose] public section
namespace NearCritical.External
open OAI.CriticalPercolation

/-- The actual positive-coordinate bond endpoints, as an upstream labelled graph. -/
def bondSearchGraph (d : ℕ) : BondGraph (Vertex d) (Bond d) where
  ends e := s(e.1, bondTip e)

/-- The finite compiled lazy search never reads an actual project bond twice,
for any fuel, initial state, stack and configuration. -/
theorem finite_bond_search_no_repeats {d : ℕ}
    (order : List (LazyDFS.Dart (Vertex d) (Bond d))) (B : Set (Vertex d))
    (fuel : ℕ) (st : LazyDFS.State (Vertex d) (Bond d))
    (stack : List (LazyDFS.Dart (Vertex d) (Bond d))) (ω : Configuration d) :
    ((LazyDFS.compile (bondSearchGraph d) order B fuel st stack).reads ω).Nodup := by
  exact SearchTree.reads_nodup _ st.read
    (LazyDFS.compile_valid (bondSearchGraph d) order B fuel st stack) ω

end NearCritical.External
