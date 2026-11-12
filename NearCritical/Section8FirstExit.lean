module
public import NearCritical.Section8PathSeparation

/-! First exit retains the inside prefix and the entire remaining walk.
This is the certificate needed for the corrected local RD decomposition. -/
@[expose] public section
noncomputable section
namespace NearCritical.Section8

/-- Split at the first edge leaving C. Unlike a last-exit split, every vertex
of the prefix is in C. The exit edge and suffix reconstruct the given walk. -/
theorem walk_first_exit {V : Type*} {G : SimpleGraph V} (C : Set V)
    {x y : V} (w : G.Walk x y) (hx : x ∈ C) (hy : y ∉ C) :
    ∃ (z u : V) (hzu : G.Adj z u) (p : G.Walk x z) (q : G.Walk u y),
      z ∈ C ∧ u ∉ C ∧ p.append (q.cons hzu) = w ∧ ∀ v ∈ p.support, v ∈ C := by
  classical
  revert hx hy
  induction w with
  | nil =>
    intro hx hy
    exact (hy hx).elim
  | @cons a b c hab w ih =>
    intro hx hy
    by_cases hb : b ∈ C
    · obtain ⟨z,u,hzu,p,q,hz,hu,hpq,hpC⟩ := ih hb hy
      refine ⟨z,u,hzu,p.cons hab,q,hz,hu,?_,?_⟩
      · simp only [SimpleGraph.Walk.cons_append,hpq]
      · intro v hv
        rcases List.mem_cons.mp hv with rfl | hv
        · exact hx
        · exact hpC v hv
    · exact ⟨a,b,hab,.nil,w,hx,hb,rfl,by simpa using hx⟩

end NearCritical.Section8
