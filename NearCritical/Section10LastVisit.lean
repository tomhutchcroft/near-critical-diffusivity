module

public import NearCritical.Section8PathSeparation
public import NearCritical.Section9PhysicalBond
public import NearCritical.ClusterRevealSupport

/-! The last-visit step of the `delta n^2` argument (lem.arm.2dspanning).

* `walk_last_visit`: a walk starting in a set `T` splits at its last visit to
  `T`; the tail meets `T` only at its first vertex.
* `cluster_last_visit_arm`: let `x` be in a finite set `Q` and let an open walk
  go from `x` to a vertex outside `Q`. Then there is a vertex `y` of the
  cluster `C_Q(x)` and an open walk from `y` to the same endpoint which stays
  on the vertices of the original walk, meets `C_Q(x)` only at `y`, and uses
  no bond explored by the cluster (`clusterRevealBonds Q C_Q(x)`).

This is the source's "last visit to `C_n(x)` of an open simple path": the arm
from `y` is determined by bonds the cluster has not explored, so the
cluster-conditioned union bound applies to it.
-/
@[expose] public section
noncomputable section
namespace NearCritical.Section10
open scoped Classical

theorem walk_last_visit {V : Type*} {G : SimpleGraph V} {x y : V} (w : G.Walk x y)
    (T : Set V) (hx : x ∈ T) :
    ∃ (u : V) (p : G.Walk x u) (q : G.Walk u y),
      p.append q = w ∧ u ∈ T ∧ ∀ v ∈ q.support, v ∈ T → v = u := by
  obtain ⟨u, p', q', hpq, hu, hfirst⟩ := Section8.walk_first_hit w.reverse T
    ⟨x, by simp, hx⟩
  refine ⟨u, q'.reverse, p'.reverse, ?_, hu, ?_⟩
  · rw [← SimpleGraph.Walk.reverse_append, hpq, SimpleGraph.Walk.reverse_reverse]
  · intro v hv hvT
    rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at hv
    exact hfirst v hv hvT

theorem cluster_last_visit_arm {d : ℕ} {ω : Configuration d} (Q : Finset (Vertex d))
    {x y₀ : Vertex d} (hx : x ∈ Q) (w : (openGraph ω).Walk x y₀) :
    ∃ y ∈ finiteBoxCluster ω Q x, ∃ q : (openGraph ω).Walk y y₀,
      (∀ v ∈ q.support, v ∈ w.support) ∧
      (∀ v ∈ q.support, v ∈ finiteBoxCluster ω Q x → v = y) ∧
      ∀ b : Bond d, s(b.1, bondTip b) ∈ q.edges →
        b ∉ clusterRevealBonds Q (finiteBoxCluster ω Q x) := by
  have hxC : x ∈ finiteBoxCluster ω Q x := root_mem_finiteBoxCluster ω Q hx
  obtain ⟨y, p, q, hpq, hy, hlast⟩ :=
    walk_last_visit w {v | v ∈ finiteBoxCluster ω Q x} hxC
  refine ⟨y, hy, q, ?_, hlast, ?_⟩
  · intro v hv
    rw [← hpq, SimpleGraph.Walk.mem_support_append_iff]
    exact Or.inr hv
  · intro b hb hrev
    obtain ⟨hb1, hb2, hC⟩ := (mem_clusterRevealBonds Q _ b).mp hrev
    have hadj : (openGraph ω).Adj b.1 (bondTip b) := q.adj_of_mem_edges hb
    have hopen : ω b = true := section9_bond_open_of_adj (e := (b.1, bondTip b)) rfl hadj
    have h1s : b.1 ∈ q.support := q.fst_mem_support_of_mem_edges hb
    have h2s : bondTip b ∈ q.support := q.snd_mem_support_of_mem_edges hb
    have hradj : (restrictedGraph ω (Q : Set (Vertex d))).Adj b.1 (bondTip b) :=
      ⟨hadj, hb1, hb2⟩
    have hboth : b.1 ∈ finiteBoxCluster ω Q x ∧ bondTip b ∈ finiteBoxCluster ω Q x := by
      rcases hC with h | h
      · refine ⟨h, (mem_finiteBoxCluster ω Q x _).mpr ⟨hb2, ?_⟩⟩
        exact ((mem_finiteBoxCluster ω Q x _).mp h).2.trans hradj.reachable
      · refine ⟨(mem_finiteBoxCluster ω Q x _).mpr ⟨hb1, ?_⟩, h⟩
        exact ((mem_finiteBoxCluster ω Q x _).mp h).2.trans hradj.symm.reachable
    have e1 : b.1 = y := hlast _ h1s hboth.1
    have e2 : bondTip b = y := hlast _ h2s hboth.2
    exact bondTip_ne_base b (e2.trans e1.symm)

end NearCritical.Section10
