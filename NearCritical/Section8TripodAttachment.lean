module
public import NearCritical.Section8PathSeparation

/-! Common geometry of diagrams 1--3: attach an incoming first-hit walk to
one simple leg of a tripod. The attachment may coincide with the branch. -/
@[expose] public section
noncomputable section
namespace NearCritical.Section8
open scoped Classical

private lemma edges_disjoint_subsets {α : Type*} {A B C D : List α}
    (h : A.Disjoint B) (hC : C ⊆ A) (hD : D ⊆ B) : C.Disjoint D := by
  exact List.disjoint_left.mpr (fun _ hc hd => List.disjoint_left.mp h (hC hc) (hD hd))

/-- The five edge lists are pairwise disjoint. Endpoint coincidences and
nil pieces require no exceptions. Append identities preserve all domains. -/
theorem tripod_attach_on_leg {V : Type*} {G : SimpleGraph V}
    {u a b c y w : V} (pa : G.Walk u a) (pb : G.Walk u b) (pc : G.Walk u c)
    (py : G.Walk y w) (hc : pc.IsPath) (hw : w ∈ pc.support)
    (hab : pa.edges.Disjoint pb.edges) (hac : pa.edges.Disjoint pc.edges)
    (hbc : pb.edges.Disjoint pc.edges)
    (hfirst : ∀ v ∈ py.support,
      v ∈ pa.support ∨ v ∈ pb.support ∨ v ∈ pc.support → v = w) :
    ∃ (t : G.Walk u w) (s : G.Walk w c),
      t.append s = pc ∧
      List.Pairwise List.Disjoint [pa.edges,pb.edges,t.edges,s.edges,py.edges] := by
  have hya : py.edges.Disjoint pa.edges := by
    apply walk_edges_disjoint_of_one_common_vertex
    intro v hvy hva
    exact hfirst v hvy (Or.inl hva)
  have hyb : py.edges.Disjoint pb.edges := by
    apply walk_edges_disjoint_of_one_common_vertex
    intro v hvy hvb
    exact hfirst v hvy (Or.inr (Or.inl hvb))
  have hyc : py.edges.Disjoint pc.edges := by
    apply walk_edges_disjoint_of_one_common_vertex
    intro v hvy hvc
    exact hfirst v hvy (Or.inr (Or.inr hvc))
  let t := pc.takeUntil w hw
  let s := pc.dropUntil w hw
  have ht : t.edges ⊆ pc.edges := pc.edges_takeUntil_subset_edges hw
  have hs : s.edges ⊆ pc.edges := pc.edges_dropUntil_subset_edges hw
  have hat : pa.edges.Disjoint t.edges := edges_disjoint_subsets hac (fun _ h => h) ht
  have has : pa.edges.Disjoint s.edges := edges_disjoint_subsets hac (fun _ h => h) hs
  have hbt : pb.edges.Disjoint t.edges := edges_disjoint_subsets hbc (fun _ h => h) ht
  have hbs : pb.edges.Disjoint s.edges := edges_disjoint_subsets hbc (fun _ h => h) hs
  have hyt : py.edges.Disjoint t.edges := edges_disjoint_subsets hyc (fun _ h => h) ht
  have hys : py.edges.Disjoint s.edges := edges_disjoint_subsets hyc (fun _ h => h) hs
  have hts : t.edges.Disjoint s.edges := hc.isTrail.disjoint_edges_takeUntil_dropUntil hw
  refine ⟨t,s,pc.take_spec hw,?_⟩
  simp [List.pairwise_cons,hab,hat,has,hya.symm,hbt,hbs,hyb.symm,hts,hyt.symm,hys.symm]

end NearCritical.Section8
