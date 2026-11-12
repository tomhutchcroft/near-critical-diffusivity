module

public import NearCritical.SplitCrossDirectDistinctLower

/-! Overlaps are bounded by a two-vertex diagram (item D of the direct proof of
`SplitCrossInput`, probabilistic input of the analytic estimate).

`overlap_le_diagram`: for tube edges `f, x` in a finite domain `U`,

  `overlap f x ≤ Σ_{w ∈ U} (Σ_{u ∈ U} τ_U(a_x,u) τ_U(u,b_x) τ_U(w,u)) ·`
  `                 τ_{T_f}(a_f,w) τ_{T_f}(w,b_f)`,

with `τ_S(a,b) = P[a ↔ b in S]`. The first factor is the proved restricted
tripod bound, the second is BK.
-/
@[expose] public section
noncomputable section
namespace NearCritical.SplitCrossDirect
open MeasureTheory ProbabilityTheory SimpleGraph
open scoped Classical BigOperators

variable {d : ℕ} {U : Finset (Vertex d)}

lemma connectionToSetEvent_mono_domain {S S' : Set (Vertex d)} (h : S ⊆ S') (x : Vertex d)
    (A : Set (Vertex d)) : connectionToSetEvent S x A ⊆ connectionToSetEvent S' x A := by
  rintro ω ⟨hx, y, hy, hyS, hreach⟩
  exact ⟨h hx, y, hy, h hyS, Reachable.mono (restrictedGraph_mono ω h) hreach⟩

theorem overlap_le_diagram (p : unitInterval) (f x : TEdge d U) :
    f.overlap p x ≤
      ∑ w ∈ U, (∑ u ∈ U,
          (percolation d p).real (connectionToSetEvent (U : Set (Vertex d)) x.a {u}) *
          (percolation d p).real (connectionToSetEvent (U : Set (Vertex d)) u {x.b}) *
          (percolation d p).real (connectionToSetEvent (U : Set (Vertex d)) w {u})) *
        ((percolation d p).real (connectionToSetEvent f.T f.a {w}) *
          (percolation d p).real (connectionToSetEvent f.T w {f.b})) := by
  unfold TEdge.overlap
  refine Finset.sum_le_sum (fun w _ => ?_)
  have h1 : (percolation d p).real (x.loc.withTarget w).ev ≤
      ∑ u ∈ U,
        (percolation d p).real (connectionToSetEvent (U : Set (Vertex d)) x.a {u}) *
        (percolation d p).real (connectionToSetEvent (U : Set (Vertex d)) u {x.b}) *
        (percolation d p).real (connectionToSetEvent (U : Set (Vertex d)) w {u}) := by
    have hsub : (x.loc.withTarget w).ev ⊆
        connectionToSetEvent (U : Set (Vertex d)) x.a {x.b} ∩
          connectionToSetEvent (U : Set (Vertex d)) x.a {w} :=
      fun ω hω => ⟨connectionToSetEvent_mono_domain x.hT _ _ hω.1, hω.2⟩
    exact (measureReal_mono hsub (measure_ne_top _ _)).trans
      (restricted_tripod_connection_probability_le p U x.a x.b w)
  have h2 : (percolation d p).real {ω | DisjointOccurrence (connectionToSetEvent f.T f.a {w})
        (connectionToSetEvent f.T w {f.b}) ω} ≤
      (percolation d p).real (connectionToSetEvent f.T f.a {w}) *
        (percolation d p).real (connectionToSetEvent f.T w {f.b}) :=
    percolation_bk d p _ _ (connectionToSetEvent_increasing _ _ _)
      (connectionToSetEvent_increasing _ _ _)
  exact mul_le_mul h1 h2 measureReal_nonneg
    (Finset.sum_nonneg (fun u _ => mul_nonneg (mul_nonneg measureReal_nonneg measureReal_nonneg)
      measureReal_nonneg))

end NearCritical.SplitCrossDirect
end
