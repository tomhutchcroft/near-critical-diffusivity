module

public import NearCritical.MaskedWaterCubeFirstHit

@[expose] public section
noncomputable section
namespace NearCritical
open Set
open scoped Classical

private theorem walk_prefix_first_entry {V : Type*} {G : SimpleGraph V}
    (P Q : V → Prop) (hentry : ∀ {u v}, G.Adj u v → ¬ P u → P v → Q v)
    {x y : V} (w : G.Walk x y) (hx : ¬ P x) (hy : P y) :
    ∃ (z : V) (p : G.Walk x z) (q : G.Walk z y),
      p.append q = w ∧ P z ∧ Q z ∧ ∀ u ∈ p.support, ¬ P u ∨ u=z := by
  induction w with
  | nil => exact (hx hy).elim
  | @cons x v y h w ih =>
    by_cases hv : P v
    · refine ⟨v, .cons h .nil, w, by simp, hv, hentry h hx hv, ?_⟩
      intro u hu
      simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
        List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl
      · exact Or.inl hx
      · exact Or.inr rfl
    · obtain ⟨z,p,q,he,hz,hQ,hs⟩ := ih hv hy
      refine ⟨z,p.cons h,q,by simp only [SimpleGraph.Walk.cons_append,he],hz,hQ,?_⟩
      intro u hu
      rcases List.mem_cons.mp hu with rfl | hu
      · exact Or.inl hx
      · exact hs u hu

private theorem waterCube_entry_bottom_is_base {d : ℕ}
    (i : Fin d) (r R : ℕ) (ω : Configuration d)
    {u v : DomainVertex (waterCube d i r R)}
    (h : ((issuedNetwork (waterCube d i r R)).positiveGraph
      (Network.binaryWeights ((issuedBondSet (waterCube d i r R)).restrict ω))
      Set.univ).Adj u v)
    (hu : u.val i ≠ -(r : ℤ)) (hv : v.val i = -(r : ℤ)) :
    v.val ∈ waterCube d i r R := by
  obtain ⟨_,_,_,e,_,he⟩ := h
  rcases he with ⟨ht,hh⟩ | ⟨ht,_⟩
  · have htail : e.val.1 = u.val := congrArg Subtype.val ht
    have htip : bondTip e.val = v.val := congrArg Subtype.val hh
    have hb := (mem_rectangularBox.mp (Finset.mem_product.mp e.property).1) i
    simp only [ite_true] at hb
    have hbase := congrFun htail i
    have hhead := congrFun htip i
    by_cases hi : i = e.val.2
    · rw [bondTip, Function.update_apply, if_pos hi] at hhead
      have heheight : e.val.1 e.val.2 = e.val.1 i := congrArg e.val.1 hi.symm
      omega
    · simp only [bondTip, Function.update_of_ne hi] at hhead
      omega
  · exact (congrArg Subtype.val ht) ▸ (Finset.mem_product.mp e.property).1

/-- A negative-face connection from inside the cube and above the bottom
contains an old-open simple prefix to a base vertex on the bottom layer.
Only the terminal vertex of the prefix lies on that layer. -/
theorem waterCube_negativeFace_simple_open_prefix {d : ℕ}
    (i : Fin d) (r R : ℕ) (ω : Configuration d)
    (x : DomainVertex (waterCube d i r R)) (hx : x.val ∈ waterCube d i r R)
    (hxlo : -(r : ℤ) < x.val i)
    (hω : ω ∈ latticeBoundaryConnectionEvent (waterCube d i r R) x
      (negativeFace (waterCube d i r R) i)) :
    ∃ y : DomainVertex (waterCube d i r R), y.val i = -(r : ℤ) ∧
      ∃ w : (openGraph ω).Walk x.val y.val, w.IsPath ∧
        (∀ z ∈ w.support, z ∈ waterCube d i r R) ∧
        (∀ z ∈ w.support, z ≠ y.val → -(r : ℤ) < z i) := by
  obtain ⟨y,hy,⟨q⟩⟩ := hω
  let w := q.toPath.val
  have hw : w.IsPath := q.toPath.property
  have hyi : y.val i = -(r : ℤ) := by
    simpa only [ite_true] using
      rectangularBox_negativeFace_coordinate (fun j => if j=i then r else R) i hy
  obtain ⟨z,p,s,hps,hzi,hz,hs⟩ := walk_prefix_first_entry
    (fun v : DomainVertex (waterCube d i r R) => v.val i = -(r : ℤ))
    (fun v => v.val ∈ waterCube d i r R)
    (fun h hu hv => waterCube_entry_bottom_is_base i r R ω h hu hv)
    w (ne_of_gt hxlo) hyi
  have hpath : (p.append s).IsPath := by rw [hps]; exact hw
  have hp : p.IsPath := ((SimpleGraph.Walk.isPath_append p s).mp hpath).1
  have hconf := rectangularBox_issued_simplePath_support
    (fun j => if j=i then r else R)
    (Network.binaryWeights ((issuedBondSet (waterCube d i r R)).restrict ω))
    Set.univ p hp hx
  let f := issuedGraphToRestricted (waterCube d i r R) ω
  have hle : restrictedGraph ω (sitesPlus (waterCube d i r R) : Set (Vertex d)) ≤ openGraph ω :=
    fun _ _ h => h.1
  let t := (p.map f).mapLe hle
  have ht : t.IsPath := (hp.map (show Function.Injective f from Subtype.val_injective)).mapLe hle
  have hsupp (u : Vertex d) (hu : u ∈ t.support) :
      ∃ v ∈ p.support, v.val = u := by
    change u ∈ ((p.map f).mapLe hle).support at hu
    rw [SimpleGraph.Walk.support_mapLe_eq_support, SimpleGraph.Walk.support_map] at hu
    exact List.mem_map.mp hu
  have hbase (v : DomainVertex (waterCube d i r R)) (hv : v ∈ p.support) :
      v.val ∈ waterCube d i r R := by
    rcases hconf v hv with hU | rfl
    · exact hU
    · exact hz
  refine ⟨z,hzi,t,ht,?_,?_⟩
  · intro u hu
    obtain ⟨v,hv,rfl⟩ := hsupp u hu
    exact hbase v hv
  · intro u hu hne
    obtain ⟨v,hv,rfl⟩ := hsupp u hu
    have hl := (mem_rectangularBox.mp (hbase v hv) i).1
    simp only [ite_true] at hl
    rcases hs v hv with hvi | rfl
    · exact lt_of_le_of_ne hl (Ne.symm hvi)
    · exact (hne rfl).elim

end NearCritical
