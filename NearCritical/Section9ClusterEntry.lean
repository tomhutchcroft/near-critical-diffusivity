module

public import NearCritical.Section9Pivotal
public import NearCritical.HeartMembershipBK

/-! Actual entry into the revealed left component from the right tube.
The exact axial exit-face identification is a separate geometric statement. -/
@[expose] public section
noncomputable section
namespace NearCritical
open scoped Classical

/-- A right-tube edge from outside the left component into it must cross the
left tube boundary. Any edge with both endpoints inside the left tube would
already connect the outside endpoint to the actual left component. -/
theorem sprinklingCluster_entry_boundary {d : ℕ} {ω : Configuration d}
    (L R Q₁ F₁ Q₃ F₃ : Finset (Vertex d)) (hRQ₁ : Disjoint R Q₁)
    (root : Vertex d) {u v : Vertex d}
    (hu : u ∉ sprinklingUnexploredCluster ω L Q₁ F₁ root)
    (hv : v ∈ sprinklingUnexploredCluster ω L Q₁ F₁ root)
    (huv : (sprinklingUnexploredGraph ω R Q₃ F₃).Adj u v) :
    v ∈ innerEntryBoundary R L := by
  obtain ⟨hvL, hrootv⟩ := (mem_sprinklingUnexploredCluster ω L Q₁ F₁ root v).mp hv
  have hnot : s(u,v) ∉ exploredEdgeSet (Q₁ : Set (Vertex d)) (F₁ : Set (Vertex d)) := by
    intro hex
    exact Finset.disjoint_left.mp hRQ₁ huv.2.1
      ((pair_mem_exploredEdgeSet _ _ _ _).mp hex).1
  have huL : u ∉ L := by
    intro huL
    have hleft : (sprinklingUnexploredGraph ω L Q₁ F₁).Adj u v :=
      ⟨huv.1, huL, hvL, hnot⟩
    apply hu
    exact (mem_sprinklingUnexploredCluster ω L Q₁ F₁ root u).mpr
      ⟨huL, hrootv.trans hleft.symm.reachable⟩
  have hfull : (openGraph (fun _ : Bond d => true)).Adj u v := by
    obtain ⟨b,_,hends⟩ := huv.1
    exact ⟨b,rfl,hends⟩
  exact Finset.mem_filter.mpr ⟨hvL,u,huv.2.1,huL,hfull⟩

/-- Any actual right-tube path from outside the revealed left component to it
visits a vertex of that component on the relative left-tube entry boundary. -/
theorem sprinklingCluster_path_hits_entry {d : ℕ} {ω : Configuration d}
    (L R Q₁ F₁ Q₃ F₃ : Finset (Vertex d)) (hRQ₁ : Disjoint R Q₁)
    (root : Vertex d) {x y : Vertex d}
    (hx : x ∉ sprinklingUnexploredCluster ω L Q₁ F₁ root)
    (hy : y ∈ sprinklingUnexploredCluster ω L Q₁ F₁ root)
    (hxy : (sprinklingUnexploredGraph ω R Q₃ F₃).Reachable x y) :
    ∃ v ∈ innerEntryBoundary R L ∩ sprinklingUnexploredCluster ω L Q₁ F₁ root,
      (sprinklingUnexploredGraph ω R Q₃ F₃).Reachable x v := by
  obtain ⟨w⟩ := hxy
  obtain ⟨u,p,q,hpq,hu,hlast⟩ := walk_last_visit w
    (fun z => z ∉ sprinklingUnexploredCluster ω L Q₁ F₁ root)
    ⟨x,w.start_mem_support,hx⟩
  cases q with
  | nil => exact (hu hy).elim
  | @cons u v y huv q =>
    have hv : v ∈ sprinklingUnexploredCluster ω L Q₁ F₁ root := by
      simpa using hlast v q.start_mem_support
    exact ⟨v, Finset.mem_inter.mpr
      ⟨sprinklingCluster_entry_boundary L R Q₁ F₁ Q₃ F₃ hRQ₁ root hu hv huv,hv⟩,
      (p.concat huv).reachable⟩

end NearCritical
