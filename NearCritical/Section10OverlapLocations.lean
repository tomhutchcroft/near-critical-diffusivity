import NearCritical.Section10SelectedPieceEdges

noncomputable section
namespace NearCritical.Section10
open scoped Classical

/-- A physical edge in two representative components identifies their common
coarse site and their common critical component. -/
theorem common_cluster_edge_identifies_cluster {d : ℕ} {I : Type*}
    (critical : Configuration d) (cube : I → Finset (Vertex d))
    (hcube : Pairwise fun j k => Disjoint (cube j) (cube k))
    {j k : I} {C C' : Finset (Vertex d)}
    (hC : C ∈ finiteClusterFamily critical (cube j))
    (hC' : C' ∈ finiteClusterFamily critical (cube k))
    {e : Sym2 (Vertex d)}
    (he : e ∈ (restrictedGraph critical (C : Set (Vertex d))).edgeSet)
    (he' : e ∈ (restrictedGraph critical (C' : Set (Vertex d))).edgeSet) :
    j = k ∧ C = C' := by
  induction e using Sym2.ind with
  | h x y =>
    have hxy : (restrictedGraph critical (C : Set (Vertex d))).Adj x y := he
    have hxy' : (restrictedGraph critical (C' : Set (Vertex d))).Adj x y := he'
    obtain ⟨bond, _, _⟩ := hxy.1
    exact common_terminal_edge_identifies_cluster critical bond.2 cube hcube hC hC'
      hxy.2.1 hxy'.2.1 rfl

/-- Two bridge edge supports can share a bond only when they belong to the
same coarse tube, with the same base and positive coordinate direction. -/
theorem common_bridge_edge_identifies_tube {d : ℕ} {ell : ℝ} (hell : 0 < ell)
    {a b : Vertex d} {i j : Fin d} {e : Sym2 (Vertex d)}
    (he : e ∈ (coarseTubeVertices ell a i).sym2)
    (he' : e ∈ (coarseTubeVertices ell b j).sym2) :
    (a, i) = (b, j) := by
  by_contra hne
  have hdis := coarseTubeVertices_disjoint hell a b i j hne
  induction e using Sym2.ind with
  | h x y =>
    exact Set.disjoint_left.mp hdis (Set.mk_mem_sym2_iff.mp he).1
      (Set.mk_mem_sym2_iff.mp he').1

end NearCritical.Section10
