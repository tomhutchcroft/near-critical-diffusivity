module
public import NearCritical.Section8FirstExit
public import NearCritical.HeartMembershipBK
public import NearCritical.Section8HeartCovariance

/-! Actual first-exit BK decomposition retaining the finite inside prefix. -/
@[expose] public section
noncomputable section
namespace NearCritical.Section8
open Set MeasureTheory
open scoped Classical

/-- First exit from C, using its actual inner interface with Q. The exit edge
belongs to the suffix, so the prefix remains confined to C. -/
theorem connectionToSet_first_exit_split {d : ℕ} {ω : Configuration d}
    (Q C : Finset (Vertex d)) (x y : Vertex d)
    (hx : x ∈ C) (hy : y ∉ C)
    (hω : ω ∈ connectionToSetEvent (Q : Set (Vertex d)) x {y}) :
    ∃ z ∈ innerEntryBoundary Q C, DisjointOccurrence
      (connectionToSetEvent (C : Set (Vertex d)) x {z})
      (connectionToSetEvent (Q : Set (Vertex d)) z {y}) ω := by
  obtain ⟨hxQ,t,ht,_htQ,⟨w⟩⟩ := hω
  have hty : t = y := ht
  subst t
  have hle : restrictedGraph ω (Q : Set (Vertex d)) ≤ openGraph ω := fun _ _ h => h.1
  let r : (openGraph ω).Walk x y :=
    (w.toPath : (restrictedGraph ω (Q : Set (Vertex d))).Walk x y).mapLe hle
  have hr : r.IsPath := w.toPath.property.mapLe _
  have hrQ : ∀ v ∈ r.support, v ∈ Q := by
    simpa only [r,SimpleGraph.Walk.support_mapLe_eq_support,Finset.mem_coe] using
      restrictedWalk_support (w.toPath : (restrictedGraph ω (Q : Set (Vertex d))).Walk x y) hxQ
  obtain ⟨z,u,hzu,p,q,hz,hu,hpq,hpC⟩ := walk_first_exit (C : Set (Vertex d)) r hx hy
  have hqQ : ∀ v ∈ (q.cons hzu).support, v ∈ Q := by
    intro v hv
    apply hrQ v
    rw [← hpq]
    exact p.support_subset_support_append_right (q.cons hzu) hv
  have huQ : u ∈ Q := hqQ u (by simp)
  have hfull : (openGraph (fun _ : Bond d => true)).Adj u z := by
    obtain ⟨e,_he,hends⟩ := hzu.symm
    exact ⟨e,rfl,hends⟩
  have hzB : z ∈ innerEntryBoundary Q C := Finset.mem_filter.mpr ⟨hz,u,huQ,hu,hfull⟩
  have hdis : p.edges.Disjoint (q.cons hzu).edges :=
    ((SimpleGraph.Walk.isTrail_append p (q.cons hzu)).mp (hpq.symm ▸ hr.isTrail)).2.2
  exact ⟨z,hzB,disjointOpenWalks_occurrence p (q.cons hzu) hdis
    (C : Set (Vertex d)) (Q : Set (Vertex d)) {z} {y} hpC hqQ rfl rfl⟩

/-- Finite first-exit probability bound with an actual restricted prefix.
No connection-probability or independence premise is assumed. -/
theorem finite_connection_first_exit_bk {d : ℕ} (p : unitInterval)
    (Q C : Finset (Vertex d)) (x y : Vertex d) (hx : x ∈ C) (hy : y ∉ C) :
    (percolation d p).real (connectionToSetEvent (Q : Set (Vertex d)) x {y}) ≤
      ∑ z ∈ innerEntryBoundary Q C,
        (percolation d p).real (connectionToSetEvent (C : Set (Vertex d)) x {z}) *
        (percolation d p).real (connectionToSetEvent (Q : Set (Vertex d)) z {y}) := by
  let E := fun z => {ω : Configuration d | DisjointOccurrence
    (connectionToSetEvent (C : Set (Vertex d)) x {z})
    (connectionToSetEvent (Q : Set (Vertex d)) z {y}) ω}
  have hs : connectionToSetEvent (Q : Set (Vertex d)) x {y} ⊆
      ⋃ z ∈ innerEntryBoundary Q C, E z := by
    intro ω hω
    obtain ⟨z,hz,hd⟩ := connectionToSet_first_exit_split Q C x y hx hy hω
    exact Set.mem_iUnion.mpr ⟨z,Set.mem_iUnion.mpr ⟨hz,hd⟩⟩
  calc
    _ ≤ (percolation d p).real (⋃ z ∈ innerEntryBoundary Q C, E z) :=
      measureReal_mono hs (measure_ne_top _ _)
    _ ≤ ∑ z ∈ innerEntryBoundary Q C, (percolation d p).real (E z) :=
      measureReal_biUnion_finset_le _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro z _hz
      exact connectionToSet_bk p (C : Set (Vertex d)) (Q : Set (Vertex d)) x z {z} {y}

end NearCritical.Section8
