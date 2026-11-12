module

public import NearCritical.HeartConnectionSecondMoment

/-! The deterministic boundary-hitting bridge for the literal source Y,
which sums boundary H while fC is defined from all of H. -/
@[expose] public section
noncomputable section
namespace NearCritical
open Set MeasureTheory
open scoped Classical

/-- A finite actual restricted walk entering H hits an actual inner boundary
vertex. The entering edge supplies the outside-neighbor witness. -/
lemma restricted_walk_hits_inner_boundary {d : ℕ} {ω : Configuration d}
    (Q H : Finset (Vertex d)) {x y : Vertex d}
    (w : (restrictedGraph ω (Q : Set (Vertex d))).Walk x y) :
    x ∉ H → y ∈ H → ∃ z ∈ boundarySites H,
      (restrictedGraph ω (Q : Set (Vertex d))).Reachable x z := by
  induction w with
  | nil =>
    intro hx hy
    exact (hx hy).elim
  | @cons a b c hab w ih =>
    intro ha hc
    by_cases hb : b ∈ H
    · have hfull : (openGraph (fun _ : Bond d => true)).Adj a b := by
        obtain ⟨e,_he,hends⟩ := hab.1
        exact ⟨e,rfl,hends⟩
      exact ⟨b,Finset.mem_filter.mpr ⟨hb,a,ha,hfull.symm⟩,
        ⟨SimpleGraph.Walk.cons hab SimpleGraph.Walk.nil⟩⟩
    · obtain ⟨z,hz,hr⟩ := ih hb hc
      exact ⟨z,hz,(show (restrictedGraph ω (Q : Set (Vertex d))).Reachable a b from
        ⟨SimpleGraph.Walk.cons hab SimpleGraph.Walk.nil⟩).trans hr⟩

/-- For an exterior root, full-heart and boundary-heart restricted events
are identical. All geometry is actual; no boundary-crossing premise remains. -/
theorem connectionToSet_heart_eq_boundary {d : ℕ} (Q H : Finset (Vertex d))
    (hHQ : H ⊆ Q) (x : Vertex d) (hxH : x ∉ H) :
    connectionToSetEvent (Q : Set (Vertex d)) x (H : Set (Vertex d)) =
      connectionToSetEvent (Q : Set (Vertex d)) x (boundarySites H : Set (Vertex d)) := by
  ext ω
  constructor
  · rintro ⟨hxQ,y,hyH,_hyQ,⟨w⟩⟩
    obtain ⟨z,hz,hr⟩ := restricted_walk_hits_inner_boundary Q H w hxH hyH
    have hzH : z ∈ H := (Finset.mem_filter.mp hz).1
    exact ⟨hxQ,z,hz,hHQ hzH,hr⟩
  · rintro ⟨hxQ,z,hz,hzQ,hr⟩
    exact ⟨hxQ,z,(Finset.mem_filter.mp hz).1,hzQ,hr⟩

theorem heartClusterUnion_boundary_mem_iff {d : ℕ} (Q H : Finset (Vertex d))
    (hHQ : H ⊆ Q) (x : Vertex d) (hxH : x ∉ H) (ω : Configuration d) :
    x ∈ heartClusterUnion ω Q (boundarySites H) ↔ x ∈ heartClusterUnion ω Q H := by
  have hbQ : boundarySites H ⊆ Q := fun _ hz => hHQ (Finset.mem_filter.mp hz).1
  rw [heartClusterUnion_mem_connection ω Q (boundarySites H) hbQ x,
    heartClusterUnion_mem_connection ω Q H hHQ x,
    connectionToSet_heart_eq_boundary Q H hHQ x hxH]

/-- Literal source Y is the boundary-target count, with the positive event
identified with the FULL heart-cluster union for exterior x. -/
theorem boundaryHeartConnectionCount_pos_iff {d : ℕ} (Q H : Finset (Vertex d))
    (hHQ : H ⊆ Q) (x : Vertex d) (hxQ : x ∈ Q) (hxH : x ∉ H) (ω : Configuration d) :
    0 < heartConnectionCount Q (boundarySites H) x ω ↔ x ∈ heartClusterUnion ω Q H := by
  have hbQ : boundarySites H ⊆ Q := fun _ hz => hHQ (Finset.mem_filter.mp hz).1
  exact (heartConnectionCount_pos_iff Q (boundarySites H) hbQ x hxQ ω).trans
    (heartClusterUnion_boundary_mem_iff Q H hHQ x hxH ω)

/-- Source eq.PxinfC_CS with boundary-count moments and the actual full-H
membership probability; the formerly missing target-set bridge is derived. -/
theorem heartClusterUnion_probability_lower_boundary_second_moment {d : ℕ}
    (p : unitInterval) (Q H : Finset (Vertex d)) (hHQ : H ⊆ Q)
    (x : Vertex d) (hxQ : x ∈ Q) (hxH : x ∉ H)
    (hm : 0 < ∫ ω, heartConnectionCount Q (boundarySites H) x ω ∂percolation d p) :
    (∫ ω, heartConnectionCount Q (boundarySites H) x ω ∂percolation d p)^2 /
        (∫ ω, (heartConnectionCount Q (boundarySites H) x ω)^2 ∂percolation d p) ≤
      (percolation d p).real {ω | x ∈ heartClusterUnion ω Q H} := by
  have hbQ : boundarySites H ⊆ Q := fun _ hz => hHQ (Finset.mem_filter.mp hz).1
  have he : {ω : Configuration d | x ∈ heartClusterUnion ω Q (boundarySites H)} =
      {ω | x ∈ heartClusterUnion ω Q H} := by
    ext ω
    exact heartClusterUnion_boundary_mem_iff Q H hHQ x hxH ω
  simpa only [he] using heartClusterUnion_probability_lower_second_moment p Q
    (boundarySites H) hbQ x hxQ hm

end NearCritical
