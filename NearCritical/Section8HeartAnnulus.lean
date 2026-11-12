module
public import NearCritical.Section8HeartCovariance
public import NearCritical.HalfSpaceArmGeometry

/-! Section 8: Ann=Q\int(H), where int(H)=H\boundary(H). The inner
boundary is RETAINED, as required for paths ending on boundary(H). -/
@[expose] public section
noncomputable section
namespace NearCritical.Section8
open Set MeasureTheory
open scoped Classical

def heartAnnulus {d : ℕ} (Q H : Finset (Vertex d)) : Finset (Vertex d) :=
  Q \ (H \ boundarySites H)

lemma heartAnnulus_subset {d : ℕ} (Q H : Finset (Vertex d)) : heartAnnulus Q H ⊆ Q :=
  Finset.sdiff_subset

lemma heartAnnulus_mem_heart_boundary {d : ℕ} (Q H : Finset (Vertex d))
    {x : Vertex d} (hx : x ∈ heartAnnulus Q H) (hxH : x ∈ H) : x ∈ boundarySites H := by
  by_contra hn
  exact (Finset.mem_sdiff.mp hx).2 (Finset.mem_sdiff.mpr ⟨hxH,hn⟩)

private lemma boundary_mem_annulus {d : ℕ} (Q H : Finset (Vertex d))
    {x : Vertex d} (hxQ : x ∈ Q) (hxB : x ∈ boundarySites H) : x ∈ heartAnnulus Q H := by
  exact Finset.mem_sdiff.mpr ⟨hxQ,fun h => (Finset.mem_sdiff.mp h).2 hxB⟩

private lemma outside_mem_annulus {d : ℕ} (Q H : Finset (Vertex d))
    {x : Vertex d} (hxQ : x ∈ Q) (hxH : x ∉ H) : x ∈ heartAnnulus Q H := by
  exact Finset.mem_sdiff.mpr ⟨hxQ,fun h => hxH (Finset.mem_sdiff.mp h).1⟩

/-- Stop at the FIRST entry into H. No annulus-support conclusion is a premise. -/
private lemma first_heart_entry {d : ℕ} {ω : Configuration d} (Q H : Finset (Vertex d))
    {x y : Vertex d} (w : (openGraph ω).Walk x y) :
    (∀ z ∈ w.support, z ∈ Q) → y ∈ H → x ∈ heartAnnulus Q H →
      ∃ v ∈ boundarySites H, v ∈ heartAnnulus Q H ∧
        (restrictedGraph ω (heartAnnulus Q H : Set (Vertex d))).Reachable x v := by
  induction w with
  | @nil a =>
    intro _haQ haH haAnn
    exact ⟨a,heartAnnulus_mem_heart_boundary Q H haAnn haH,haAnn,SimpleGraph.Reachable.refl a⟩
  | @cons a b c hab w ih =>
    intro hQ hcH haAnn
    by_cases haH : a ∈ H
    · exact ⟨a,heartAnnulus_mem_heart_boundary Q H haAnn haH,haAnn,SimpleGraph.Reachable.refl a⟩
    · have hbQ : b ∈ Q := hQ b (by simp)
      by_cases hbH : b ∈ H
      · have hfull : (openGraph (fun _ : Bond d => true)).Adj a b := by
          obtain ⟨e,_he,hends⟩ := hab
          exact ⟨e,rfl,hends⟩
        have hbB : b ∈ boundarySites H := Finset.mem_filter.mpr
          ⟨hbH,a,haH,hfull.symm⟩
        have hbAnn := boundary_mem_annulus Q H hbQ hbB
        exact ⟨b,hbB,hbAnn,(show (restrictedGraph ω (heartAnnulus Q H : Set (Vertex d))).Adj a b
          from ⟨hab,haAnn,hbAnn⟩).reachable⟩
      · have hbAnn := outside_mem_annulus Q H hbQ hbH
        obtain ⟨v,hvB,hvAnn,hbv⟩ := ih
          (fun z hz => hQ z (by simp only [SimpleGraph.Walk.support_cons,List.mem_cons]; exact Or.inr hz)) hcH hbAnn
        exact ⟨v,hvB,hvAnn,((show (restrictedGraph ω (heartAnnulus Q H : Set (Vertex d))).Adj a b
          from ⟨hab,haAnn,hbAnn⟩).reachable).trans hbv⟩

/-- Exact source identification {x in fC}={x connected to boundaryH in Ann},
stated first for the actual restricted connection event. -/
theorem heartEvent_eq_annulus {d : ℕ} (Q H : Finset (Vertex d)) (x : Vertex d)
    (hx : x ∈ heartAnnulus Q H) :
    heartEvent Q H x = connectionToSetEvent (heartAnnulus Q H : Set (Vertex d)) x
      (boundarySites H : Set (Vertex d)) := by
  ext ω
  constructor
  · rintro ⟨hxQ,y,hyH,_hyQ,⟨w⟩⟩
    have hle : restrictedGraph ω (Q : Set (Vertex d)) ≤ openGraph ω := fun _ _ h => h.1
    let r : (openGraph ω).Walk x y := w.mapLe hle
    have hrQ : ∀ z ∈ r.support, z ∈ Q := by
      intro z hz
      exact restrictedWalk_support w hxQ z
        (by simpa only [r,SimpleGraph.Walk.support_mapLe_eq_support] using hz)
    obtain ⟨v,hvB,hvAnn,hxv⟩ := first_heart_entry Q H r hrQ hyH hx
    exact ⟨hx,v,hvB,hvAnn,hxv⟩
  · rintro ⟨hxAnn,y,hyB,hyAnn,hxy⟩
    have hyH : y ∈ H := (Finset.mem_filter.mp hyB).1
    exact ⟨heartAnnulus_subset Q H hxAnn,y,hyH,heartAnnulus_subset Q H hyAnn,
      hxy.mono (restrictedGraph_mono ω (show (heartAnnulus Q H : Set (Vertex d)) ⊆
        (Q : Set (Vertex d)) from heartAnnulus_subset Q H))⟩

/-- Literal actual fC membership, with the source's H subset Q convention. -/
theorem heartUnion_mem_iff_annulus {d : ℕ} (Q H : Finset (Vertex d)) (hH : H ⊆ Q)
    (x : Vertex d) (hx : x ∈ heartAnnulus Q H) (ω : Configuration d) :
    x ∈ heartClusterUnion ω Q H ↔ ω ∈ connectionToSetEvent (heartAnnulus Q H : Set (Vertex d)) x
      (boundarySites H : Set (Vertex d)) := by
  rw [← heartEvent_iff_union_member Q H hH x ω,heartEvent_eq_annulus Q H x hx]

/-- The g(x) probability identity used in both expectation and variance diagrams. -/
theorem heart_probability_eq_annulus {d : ℕ} (p : unitInterval) (Q H : Finset (Vertex d))
    (x : Vertex d) (hx : x ∈ heartAnnulus Q H) :
    (percolation d p).real (heartEvent Q H x) =
      (percolation d p).real (connectionToSetEvent (heartAnnulus Q H : Set (Vertex d)) x
        (boundarySites H : Set (Vertex d))) := by
  rw [heartEvent_eq_annulus Q H x hx]

end NearCritical.Section8
